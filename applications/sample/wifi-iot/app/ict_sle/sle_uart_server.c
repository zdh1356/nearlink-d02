/**
 * SLE Audio Server
 * 接收 UART1 音频数据，通过 SLE 发送给 Client
 * 基于同学代码，只改动音频相关部分
 */

#include "securec.h"
#include "sle_common.h"
#include "osal_debug.h"
#include "sle_errcode.h"
#include "osal_addr.h"
#include "osal_task.h"
#include "sle_connection_manager.h"
#include "sle_device_discovery.h"
#include "sle_uart_server_adv.h"
#include "sle_uart_server.h"
#include "cmsis_os2.h"
#include "ohos_init.h"
#include "ohos_sle_common.h"
#include "ohos_sle_errcode.h"
#include "ohos_sle_ssap_server.h"
#include "ohos_sle_ssap_client.h"
#include "ohos_sle_device_discovery.h"
#include "ohos_sle_connection_manager.h"
#include "iot_uart.h"
#include "pinctrl.h"
#include "uart.h"
#include "errcode.h"
#include <stdbool.h>

#define OCTET_BIT_LEN 8
#define UUID_LEN_2 2
#define UUID_INDEX 14
#define BT_INDEX_5 5
#define BT_INDEX_4 4
#define BT_INDEX_0 0

#define SLE_MTU_SIZE_DEFAULT 1500
#define UART_BUFF_LENGTH     1500
#define SLE_ADV_HANDLE_DEFAULT 1

static char g_sleUuidAppUuid[UUID_LEN_2] = {0x12, 0x34};
static char g_slePropertyValue[OCTET_BIT_LEN] = {0x0, 0x0, 0x0, 0x0, 0x0, 0x0};
static uint16_t g_sleConnHdl = 0;
static uint8_t g_serverId = 0;
static uint16_t g_serviceHandle = 0;
static uint16_t g_propertyHandle = 0;
uint16_t g_slePairHdl;
static volatile bool g_connected = false;
static volatile uint16_t g_ssap_mtu = SLE_MTU_SIZE_DEFAULT;
uint8_t g_receiveBuf[UART_BUFF_LENGTH] = {0};

#define UUID_16BIT_LEN 2
#define UUID_128BIT_LEN 16
#define SLE_UART_SERVER_LOG "[sle uart server]"
#define SLE_SERVER_INIT_DELAY_MS 1000
#define DELAY_100MS 100
#define TASK_SIZE 4096
#define PRIO 25

static uint8_t g_sleUartBase[] = {0x37, 0xBE, 0xA8, 0x80, 0xFC, 0x70, 0x11, 0xEA,
                                  0xB7, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

/* ★★★ 音频 UART1 配置 ★★★ */
#define AUDIO_UART_NUM      1
#define AUDIO_UART_BAUD     921600
#define AUDIO_UART_TX_PIN   15
#define AUDIO_UART_RX_PIN   16
#define AUDIO_UART_BUF_SIZE 2048

static uint8_t g_audioUartRxBuff[AUDIO_UART_BUF_SIZE] = {0};
static uart_buffer_config_t g_audio_uart_buffer_config = {
    .rx_buffer = g_audioUartRxBuff,
    .rx_buffer_size = AUDIO_UART_BUF_SIZE
};

/* ★★★ UART 帧重组缓冲区 ★★★
 * ESP32 一次发 248 字节，但 UART idle 中断可能把一帧拆成多个回调
 * 所以需要在 Server 端做帧重组
 */
#define AUDIO_FRAME_HEADER  0x55AA
#define AUDIO_FRAME_TAIL    0xAA55
#define AUDIO_FRAME_MAX_LEN 512  /* 包头2+seq2+len2+payload240+包尾2 = 248，留余量 */

static uint8_t  g_frame_buf[AUDIO_FRAME_MAX_LEN];
static uint16_t g_frame_pos = 0;  /* 当前已收字节数 */

/* ★★★ 统计变量 ★★★ */
static uint32_t g_uart_rx_cb_count = 0;  /* UART 回调次数 */
static uint32_t g_uart_rx_bytes = 0;     /* UART 总接收字节 */
static uint32_t g_frame_ok_count = 0;    /* 成功重组帧数 */
static uint32_t g_frame_bad_count = 0;   /* 丢弃帧数 */
static uint32_t g_sle_tx_count = 0;      /* SLE 发送成功包数 */
static uint32_t g_sle_tx_bytes = 0;      /* SLE 发送总字节 */
static uint32_t g_sle_tx_fail = 0;       /* SLE 发送失败 */

/* ★★★ 发送队列：UART 回调把帧放入队列，主线程取出来发 ★★★ */
#define TX_QUEUE_SLOTS  8
#define TX_FRAME_MAX    256

static uint8_t  g_tx_slots[TX_QUEUE_SLOTS][TX_FRAME_MAX];
static uint16_t g_tx_lens[TX_QUEUE_SLOTS];

typedef struct {
    uint8_t  idx;
    uint16_t len;
} tx_q_item_t;

static uint8_t g_tx_widx = 0;
static osMessageQueueId_t g_tx_queue = NULL;

/* 前向声明 */
errcode_t sle_uart_server_send_report_by_handle(const uint8_t *data, uint16_t len);

/* ★★★ 处理一个完整的音频帧：直接通过 SLE 发送 ★★★ */
static void process_audio_frame(const uint8_t *frame, uint16_t frame_len)
{
    if (!g_connected || g_propertyHandle == 0) {
        return;
    }

    if (g_tx_queue == NULL) {
        return;
    }
    if (frame_len > TX_FRAME_MAX) {
        return;
    }

    uint8_t idx = g_tx_widx;
    g_tx_widx = (uint8_t)((g_tx_widx + 1) % TX_QUEUE_SLOTS);

    (void)memcpy_s(g_tx_slots[idx], TX_FRAME_MAX, frame, frame_len);
    g_tx_lens[idx] = frame_len;

    tx_q_item_t item;
    item.idx = idx;
    item.len = frame_len;

    if (osMessageQueuePut(g_tx_queue, &item, 0, 0) != osOK) {
        /* 队列满，丢最新的一包 */
        g_sle_tx_fail++;
        if (g_sle_tx_fail <= 10 || (g_sle_tx_fail % 100) == 0) {
            osal_printk("%s TX queue full[%u]\r\n", SLE_UART_SERVER_LOG, (unsigned)g_sle_tx_fail);
        }
    }
}

/* ★★★ 在 UART RX 回调中做帧重组 ★★★
 * 协议格式: [0x55AA(2)] [seq(2)] [payload_len(2)] [payload(N)] [0xAA55(2)]
 * 总帧长 = 2 + 2 + 2 + payload_len + 2 = payload_len + 8
 */
static void audio_uart_rx_callback(const void *buffer, uint16_t length, bool error)
{
    if (error || length == 0) {
        return;
    }

    g_uart_rx_cb_count++;
    g_uart_rx_bytes += length;

    const uint8_t *data = (const uint8_t *)buffer;

    for (uint16_t i = 0; i < length; i++) {
        g_frame_buf[g_frame_pos++] = data[i];

        /* 防溢出 */
        if (g_frame_pos >= AUDIO_FRAME_MAX_LEN) {
            g_frame_pos = 0;
            g_frame_bad_count++;
            continue;
        }

        /* 至少收到 6 字节才能解析 payload_len */
        if (g_frame_pos >= 6) {
            uint16_t hdr = (uint16_t)(g_frame_buf[0] | (g_frame_buf[1] << 8));

            /* 检查包头 */
            if (hdr != AUDIO_FRAME_HEADER) {
                /* 包头不对，尝试找到下一个 0xAA 重新同步 */
                uint16_t shift = 1;
                while (shift < g_frame_pos && g_frame_buf[shift] != 0xAA) {
                    shift++;
                }
                if (shift < g_frame_pos) {
                    uint16_t remain = g_frame_pos - shift;
                    (void)memmove(g_frame_buf, g_frame_buf + shift, remain);
                    g_frame_pos = remain;
                } else {
                    g_frame_pos = 0;
                }
                g_frame_bad_count++;
                continue;
            }

            /* 解析 payload_len (第4-5字节，小端) */
            uint16_t payload_len = (uint16_t)(g_frame_buf[4] | (g_frame_buf[5] << 8));
            uint16_t expected_frame_len = payload_len + 8; /* 包头2+seq2+len2+payload+包尾2 */

            if (payload_len == 0 || payload_len > 480 || expected_frame_len > AUDIO_FRAME_MAX_LEN) {
                /* payload_len 非法，丢弃第一个字节重新同步 */
                uint16_t remain = g_frame_pos - 1;
                (void)memmove(g_frame_buf, g_frame_buf + 1, remain);
                g_frame_pos = remain;
                g_frame_bad_count++;
                continue;
            }

            /* 检查是否收够一整帧 */
            if (g_frame_pos >= expected_frame_len) {
                /* 检查包尾 */
                uint16_t tail_off = expected_frame_len - 2;
                uint16_t tail = (uint16_t)(g_frame_buf[tail_off] | (g_frame_buf[tail_off + 1] << 8));

                if (tail == AUDIO_FRAME_TAIL) {
                    /* ★ 完整帧！发送 */
                    g_frame_ok_count++;
                    process_audio_frame(g_frame_buf, expected_frame_len);

                    if ((g_frame_ok_count % 200) == 0) {
                        osal_printk("%s FRAME: ok=%u bad=%u uart_cb=%u\r\n",
                                    SLE_UART_SERVER_LOG,
                                    (unsigned)g_frame_ok_count, (unsigned)g_frame_bad_count,
                                    (unsigned)g_uart_rx_cb_count);
                    }
                } else {
                    g_frame_bad_count++;
                }

                /* 移除已处理的帧，保留剩余数据 */
                uint16_t consumed = expected_frame_len;
                uint16_t remain = g_frame_pos - consumed;
                if (remain > 0) {
                    (void)memmove(g_frame_buf, g_frame_buf + consumed, remain);
                }
                g_frame_pos = remain;
            }
        }
    }
}

/* ★★★ 音频 UART1 初始化 ★★★ */
static void AudioUartInit(void)
{
    uart_attr_t attr = {
        .baud_rate = AUDIO_UART_BAUD,
        .data_bits = UART_DATA_BIT_8,
        .stop_bits = UART_STOP_BIT_1,
        .parity = UART_PARITY_NONE
    };
    uart_pin_config_t pin_config = {
        .tx_pin = AUDIO_UART_TX_PIN,
        .rx_pin = AUDIO_UART_RX_PIN,
        .cts_pin = PIN_NONE,
        .rts_pin = PIN_NONE
    };

    uapi_uart_deinit(AUDIO_UART_NUM);
    errcode_t ret = uapi_uart_init(AUDIO_UART_NUM, &pin_config, &attr, NULL, &g_audio_uart_buffer_config);
    if (ret != ERRCODE_SUCC) {
        osal_printk("%s UART%d init fail: %x\r\n", SLE_UART_SERVER_LOG, AUDIO_UART_NUM, ret);
        return;
    }
    ret = uapi_uart_register_rx_callback(AUDIO_UART_NUM, UART_RX_CONDITION_FULL_OR_IDLE,
                                         1, audio_uart_rx_callback);
    if (ret != ERRCODE_SUCC) {
        osal_printk("%s UART%d callback fail: %x\r\n", SLE_UART_SERVER_LOG, AUDIO_UART_NUM, ret);
        return;
    }
    osal_printk("%s UART%d ok @ %d, TX=%d RX=%d\r\n",
                SLE_UART_SERVER_LOG, AUDIO_UART_NUM, AUDIO_UART_BAUD,
                AUDIO_UART_TX_PIN, AUDIO_UART_RX_PIN);
}

/* ========== UUID 工具函数（完全不动） ========== */
static void Encode2byteLittle(uint8_t *ptr, uint16_t data)
{
    *(uint8_t *)((ptr) + 1) = (uint8_t)((data) >> 0x8);
    *(uint8_t *)(ptr) = (uint8_t)(data);
}

static void sle_uuid_set_base(SleUuid *out)
{
    errcode_t ret;
    ret = memcpy_s(out->uuid, SLE_UUID_LEN, g_sleUartBase, SLE_UUID_LEN);
    if (ret != EOK) {
        osal_printk("%s sle_uuid_set_base memcpy fail\n", SLE_UART_SERVER_LOG);
        out->len = 0;
        return;
    }
    out->len = UUID_LEN_2;
}

static void sle_uuid_setu2(uint16_t u2, SleUuid *out)
{
    sle_uuid_set_base(out);
    out->len = UUID_LEN_2;
    Encode2byteLittle(&out->uuid[UUID_INDEX], u2);
}

static void sle_uart_uuid_print(SleUuid *uuid)
{
    if (uuid == NULL) {
        osal_printk("%suuid_print, uuid is null\r\n", SLE_UART_SERVER_LOG);
        return;
    }
    if (uuid->len == UUID_16BIT_LEN) {
        osal_printk("%s uuid: %02x %02x.\n", SLE_UART_SERVER_LOG,
               uuid->uuid[14], uuid->uuid[15]);
    } else if (uuid->len == UUID_128BIT_LEN) {
        osal_printk("%s uuid: \n", SLE_UART_SERVER_LOG);
        osal_printk("%s 0x%02x 0x%02x 0x%02x 0x%02x\n", SLE_UART_SERVER_LOG,
               uuid->uuid[0], uuid->uuid[1], uuid->uuid[2], uuid->uuid[3]);
        osal_printk("%s 0x%02x 0x%02x 0x%02x 0x%02x\n", SLE_UART_SERVER_LOG,
               uuid->uuid[4], uuid->uuid[5], uuid->uuid[6], uuid->uuid[7]);
        osal_printk("%s 0x%02x 0x%02x 0x%02x 0x%02x\n", SLE_UART_SERVER_LOG,
               uuid->uuid[8], uuid->uuid[9], uuid->uuid[10], uuid->uuid[11]);
        osal_printk("%s 0x%02x 0x%02x 0x%02x 0x%02x\n", SLE_UART_SERVER_LOG,
               uuid->uuid[12], uuid->uuid[13], uuid->uuid[14], uuid->uuid[15]);
    }
}

/* ========== SSAP 回调（完全不动） ========== */
static void ssaps_mtu_changed_cbk(uint8_t serverId, uint16_t connId, SsapcExchangeInfo *mtu_size,
                                  errcode_t status)
{
    osal_printk("%s mtu_changed server_id:%x, conn_id:%x, mtu_size:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, connId, mtu_size->mtuSize, status);
    g_ssap_mtu = mtu_size->mtuSize;
    if (g_slePairHdl == 0) {
        g_slePairHdl = connId + 1;
    }
}

static void ssaps_start_service_cbk(uint8_t serverId, uint16_t handle, errcode_t status)
{
    osal_printk("%s start service cbk server_id:%d, handle:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, handle, status);
}

static void ssaps_add_service_cbk(uint8_t serverId, SleUuid *uuid, uint16_t handle, errcode_t status)
{
    osal_printk("%s add service cbk server_id:%x, handle:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, handle, status);
    sle_uart_uuid_print(uuid);
}

static void ssaps_add_property_cbk(uint8_t serverId, SleUuid *uuid, uint16_t serviceHandle,
                                   uint16_t handle, errcode_t status)
{
    osal_printk("%s add property cbk server_id:%x, service_handle:%x, handle:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, serviceHandle, handle, status);
    sle_uart_uuid_print(uuid);
}

static void ssaps_add_descriptor_cbk(uint8_t serverId, SleUuid *uuid, uint16_t serviceHandle,
                                     uint16_t propertyHandle, errcode_t status)
{
    osal_printk("%s add descriptor cbk server_id:%x, service_handle:%x, property_handle:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, serviceHandle, propertyHandle, status);
    sle_uart_uuid_print(uuid);
}

static void ssaps_delete_all_service_cbk(uint8_t serverId, errcode_t status)
{
    osal_printk("%s delete all service server_id:%x, status:%x\r\n",
           SLE_UART_SERVER_LOG, serverId, status);
}

static errcode_t sle_ssaps_register_cbks(ssaps_read_request_callback ssaps_read_callback,
                                         ssaps_write_request_callback ssaps_write_callback)
{

    errcode_t ret;
    SsapsCallbacks ssaps_cbk = {0};
    ssaps_cbk.addServiceCb = ssaps_add_service_cbk;
    ssaps_cbk.addPropertyCb = ssaps_add_property_cbk;
    ssaps_cbk.addDescriptorCb = ssaps_add_descriptor_cbk;
    ssaps_cbk.startServiceCb = ssaps_start_service_cbk;
    ssaps_cbk.deleteAllServiceCb = ssaps_delete_all_service_cbk;

    ssaps_cbk.mtuChangedCb = ssaps_mtu_changed_cbk;
    ssaps_cbk.readRequestCb = (SsapsReadRequestCallback)ssaps_read_callback;
    ssaps_cbk.writeRequestCb = (SsapsWriteRequestCallback)ssaps_write_callback;
    ret = SsapsRegisterCallbacks(&ssaps_cbk);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s ssaps_register_callbacks fail:%x\r\n", SLE_UART_SERVER_LOG, ret);
        return ret;
    }
    return ERRCODE_SLE_SUCCESS;
}

/* ========== 添加服务（完全不动） ========== */
static errcode_t sle_uuid_server_service_add(void)
{
    errcode_t ret;
    SleUuid service_uuid = {0};
    sle_uuid_setu2(SLE_UUID_SERVER_SERVICE, &service_uuid);
    ret = SsapsAddServiceSync(g_serverId, &service_uuid, 1, &g_serviceHandle);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s add service fail, ret:%x\r\n", SLE_UART_SERVER_LOG, ret);
        return ERRCODE_SLE_FAIL;
    }
    return ERRCODE_SLE_SUCCESS;
}

static errcode_t add_property_sync(void)
{
    errcode_t ret;
    SsapsPropertyInfo property = {0};
    property.permissions = SLE_UUID_TEST_PROPERTIES;
    property.operateIndication = SLE_UUID_TEST_OPERATION_INDICATION;
    sle_uuid_setu2(SLE_UUID_SERVER_NTF_REPORT, &property.uuid);
    property.valueLen = OCTET_BIT_LEN;
    property.value = (uint8_t *)osal_vmalloc(sizeof(g_slePropertyValue));
    if (property.value == NULL) {
        return ERRCODE_SLE_FAIL;
    }
    if (memcpy_s(property.value, sizeof(g_slePropertyValue), g_slePropertyValue,
                 sizeof(g_slePropertyValue)) != EOK) {
        osal_vfree(property.value);
        return ERRCODE_SLE_FAIL;
    }
    ret = SsapsAddPropertySync(g_serverId, g_serviceHandle, &property, &g_propertyHandle);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s add property fail, ret:%x\r\n", SLE_UART_SERVER_LOG, ret);
        osal_vfree(property.value);
        return ERRCODE_SLE_FAIL;
    }
    osal_vfree(property.value);
    return ERRCODE_SLE_SUCCESS;
}

static errcode_t sle_uuid_server_property_add(void)
{
    errcode_t ret;
    SsapsDescInfo descriptor = {0};
    uint8_t ntfValue[] = {0x01, 0x02};
    add_property_sync();
    descriptor.permissions = SLE_UUID_TEST_DESCRIPTOR;
    descriptor.type = SSAP_DESCRIPTOR_CLIENT_CONFIGURATION;
    descriptor.operateIndication = SLE_UUID_TEST_OPERATION_INDICATION;
    descriptor.value = (uint8_t *)osal_vmalloc(sizeof(ntfValue));
    if (descriptor.value == NULL) {
        return ERRCODE_SLE_FAIL;
    }
    if (memcpy_s(descriptor.value, sizeof(ntfValue), ntfValue, sizeof(ntfValue)) != EOK) {
        osal_vfree(descriptor.value);
        return ERRCODE_SLE_FAIL;
    }
    ret = SsapsAddDescriptorSync(g_serverId, g_serviceHandle, g_propertyHandle, &descriptor);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s add descriptor fail, ret:%x\r\n", SLE_UART_SERVER_LOG, ret);
        osal_vfree(descriptor.value);
        return ERRCODE_SLE_FAIL;
    }
    osal_vfree(descriptor.value);
    return ERRCODE_SLE_SUCCESS;
}

static errcode_t sle_uart_server_add(void)
{
    errcode_t ret;
    SleUuid app_uuid = {0};
    osal_printk("%s sle uart add service in\r\n", SLE_UART_SERVER_LOG);
    app_uuid.len = sizeof(g_sleUuidAppUuid);
    if (memcpy_s(app_uuid.uuid, app_uuid.len, g_sleUuidAppUuid, sizeof(g_sleUuidAppUuid)) != EOK) {
        return ERRCODE_SLE_FAIL;
    }
    SsapsRegisterServer(&app_uuid, &g_serverId);
    if (sle_uuid_server_service_add() != ERRCODE_SLE_SUCCESS) {
        SsapsUnregisterServer(g_serverId);
        return ERRCODE_SLE_FAIL;
    }
    if (sle_uuid_server_property_add() != ERRCODE_SLE_SUCCESS) {
        SsapsUnregisterServer(g_serverId);
        return ERRCODE_SLE_FAIL;
    }
    osal_printk("%s add service ok, server_id:%x, service_handle:%x, property_handle:%x\r\n",
           SLE_UART_SERVER_LOG, g_serverId, g_serviceHandle, g_propertyHandle);
    ret = SsapsStartService(g_serverId, g_serviceHandle);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s start service fail, ret:%x\r\n", SLE_UART_SERVER_LOG, ret);
        return ERRCODE_SLE_FAIL;
    }
    osal_printk("%s sle uart add service out\r\n", SLE_UART_SERVER_LOG);
    return ERRCODE_SLE_SUCCESS;
}

/* ========== SLE 发送 ========== */
errcode_t sle_uart_server_send_report_by_handle(const uint8_t *data, uint16_t len)
{
    SsapsNtfInd param = {0};
    uint16_t handle = g_propertyHandle;
    uint16_t conn = g_sleConnHdl;
    uint8_t  sid = g_serverId;

    if (!g_connected || handle == 0) {
        return ERRCODE_FAIL;
    }
    if (data == NULL || len == 0 || len > UART_BUFF_LENGTH) {
        return ERRCODE_FAIL;
    }

    param.handle = handle;
    param.type = SSAP_PROPERTY_TYPE_VALUE;
    param.value = g_receiveBuf;
    param.valueLen = len;

    if (memcpy_s(param.value, UART_BUFF_LENGTH, data, len) != EOK) {
        return ERRCODE_FAIL;
    }
    return SsapsNotifyIndicate(sid, conn, &param);
}

/* ========== 连接回调 ========== */
static void sle_connect_state_changed_cbk(uint16_t connId, const SleAddr *addr,
    SleAcbStateType conn_state, SlePairStateType pair_state, SleDiscReasonType disc_reason)
{
    osal_printk("%s conn_state changed conn_id:0x%02x, state:0x%x, pair:0x%x, reason:0x%x\r\n",
           SLE_UART_SERVER_LOG, connId, conn_state, pair_state, disc_reason);
    osal_printk("%s addr:%02x:**:**:**:%02x:%02x\r\n", SLE_UART_SERVER_LOG,
           addr->addr[BT_INDEX_0], addr->addr[BT_INDEX_4], addr->addr[BT_INDEX_5]);
    if (conn_state == OH_SLE_ACB_STATE_CONNECTED) {
        g_connected = true;
        g_sleConnHdl = connId;
        ssap_exchange_info_t parameter = {0};
        parameter.mtu_size = SLE_MTU_SIZE_DEFAULT;
        parameter.version = 1;
        ssaps_set_info(g_serverId, &parameter);
        osal_printk("%s Connected! MTU set to %u\r\n", SLE_UART_SERVER_LOG, SLE_MTU_SIZE_DEFAULT);
        /* 统计清零 */
        g_uart_rx_cb_count = 0;
        g_uart_rx_bytes = 0;
        g_frame_ok_count = 0;
        g_frame_bad_count = 0;
        g_sle_tx_count = 0;
        g_sle_tx_bytes = 0;
        g_sle_tx_fail = 0;
        g_frame_pos = 0;
    } else if (conn_state == OH_SLE_ACB_STATE_DISCONNECTED) {
        g_connected = false;
        g_sleConnHdl = 0;
        g_slePairHdl = 0;
        osal_printk("%s Disconnected. STAT: frame_ok=%u bad=%u sle_tx=%u fail=%u\r\n",
                    SLE_UART_SERVER_LOG,
                    (unsigned)g_frame_ok_count, (unsigned)g_frame_bad_count,
                    (unsigned)g_sle_tx_count, (unsigned)g_sle_tx_fail);
        SleStartAnnounce(SLE_ADV_HANDLE_DEFAULT);
    }
}

static void sle_pair_complete_cbk(uint16_t connId, const SleAddr *addr, errcode_t status)
{
    (void)addr;
    osal_printk("%s pair complete conn_id:%02x, status:%x\r\n",
           SLE_UART_SERVER_LOG, connId, status);
    g_slePairHdl = connId + 1;
}

static errcode_t sle_conn_register_cbks(void)
{
    errcode_t ret;
    SleConnectionCallbacks conn_cbks = {0};
    conn_cbks.connectStateChangedCb = sle_connect_state_changed_cbk;
    conn_cbks.pairCompleteCb = sle_pair_complete_cbk;
    ret = SleConnectionRegisterCallbacks(&conn_cbks);
    if (ret != ERRCODE_SLE_SUCCESS) {
        osal_printk("%s conn_register_cbks fail:%x\r\n", SLE_UART_SERVER_LOG, ret);
        return ret;
    }
    return ERRCODE_SLE_SUCCESS;
}

/* ========== SSAP read/write 回调 ========== */
void ssaps_read_request_callbacks(uint8_t serverId, uint16_t connId,
                                  ssaps_req_read_cb_t *read_cb_para, errcode_t status)
{
    (void)serverId; (void)connId; (void)read_cb_para; (void)status;
}

void ssaps_write_request_callbacks(uint8_t serverId, uint16_t connId,
                                   ssaps_req_write_cb_t *write_cb_para, errcode_t status)
{
    (void)serverId; (void)connId; (void)status;
    if (write_cb_para != NULL && write_cb_para->length > 0) {
        write_cb_para->value[write_cb_para->length - 1] = '\0';
        osal_printk(" client_send_data: %s\r\n", write_cb_para->value);
    }
}

/* ========== bridge API ========== */
bool sle_uart_server_is_ready(void)
{
    return (g_connected && (g_propertyHandle != 0));
}

uint16_t sle_uart_server_get_mtu(void)
{
    return g_ssap_mtu;
}

errcode_t sle_uart_server_send_bytes(const uint8_t *data, uint16_t len)
{
    if (!sle_uart_server_is_ready()) return ERRCODE_FAIL;
    if (data == NULL || len == 0) return ERRCODE_FAIL;
    return sle_uart_server_send_report_by_handle(data, len);
}

/* ========== 初始化 ========== */
errcode_t sle_uart_server_init(void)
{
    errcode_t ret;
    ret = sle_uart_announce_register_cbks();
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    ret = sle_conn_register_cbks();
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    ret = sle_ssaps_register_cbks(ssaps_read_request_callbacks, ssaps_write_request_callbacks);
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    ret = EnableSle();
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    osal_printk("%s init ok\r\n", SLE_UART_SERVER_LOG);
    return ERRCODE_SLE_SUCCESS;
}

errcode_t sle_enable_server_cbk(void)
{
    errcode_t ret;
    ret = sle_uart_server_add();
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    ret = sle_uart_server_adv_init();
    if (ret != ERRCODE_SLE_SUCCESS) return ret;
    return ERRCODE_SLE_SUCCESS;
}

uint32_t UartSleSendData(uint8_t *data, uint8_t length)
{
    osal_mdelay(DELAY_100MS);
    return sle_uart_server_send_report_by_handle(data, length);
}

/* ========== 主任务 ========== */
static void SleTask(void *arg)
{
    (void)arg;
    osal_printk("====SleTask Server Begins====\r\n");
    osal_msleep(1000);
    AudioUartInit();
    sle_uart_server_init();

    /* ★ 创建发送队列 */
    g_tx_queue = osMessageQueueNew(TX_QUEUE_SLOTS * 2, sizeof(tx_q_item_t), NULL);
    if (g_tx_queue == NULL) {
        osal_printk("%s TX queue create FAIL\r\n", SLE_UART_SERVER_LOG);
        return;
    }
    osal_printk("%s TX queue created\r\n", SLE_UART_SERVER_LOG);

    /* ★ 主循环：从队列取帧，通过 SLE 发送 */
    while (1) {
        tx_q_item_t item;
        if (osMessageQueueGet(g_tx_queue, &item, NULL, osWaitForever) == osOK) {
            uint8_t *frame = g_tx_slots[item.idx];
            uint16_t len = item.len;

            /* 尝试发送，失败则短暂等待后重试一次 */
            errcode_t ret = sle_uart_server_send_report_by_handle(frame, len);
            if (ret != ERRCODE_SUCC) {
                osal_msleep(2);
                ret = sle_uart_server_send_report_by_handle(frame, len);
            }

            if (ret == ERRCODE_SUCC) {
                g_sle_tx_count++;
                g_sle_tx_bytes += len;
                if ((g_sle_tx_count % 200) == 0) {
                    osal_printk("%s SLE TX: ok=%u fail=%u bytes=%u\r\n",
                                SLE_UART_SERVER_LOG,
                                (unsigned)g_sle_tx_count, (unsigned)g_sle_tx_fail,
                                (unsigned)g_sle_tx_bytes);
                }
            } else {
                g_sle_tx_fail++;
                if (g_sle_tx_fail <= 10 || (g_sle_tx_fail % 100) == 0) {
                    osal_printk("%s SLE TX FAIL[%u]: 0x%x\r\n",
                                SLE_UART_SERVER_LOG, (unsigned)g_sle_tx_fail, (unsigned)ret);
                }
            }
        }
    }
}

static void SleServerExample(void)
{
    osThreadAttr_t attr = {0};
    attr.name = "SleTask";
    attr.stack_size = TASK_SIZE;
    attr.priority = osPriorityNormal;
    if (osThreadNew(SleTask, NULL, &attr) == NULL) {
        osal_printk(" Failed to create SleTask!\n");
    } else {
        osal_printk(" create SleTask successfully!\n");
    }
}

SYS_RUN(SleServerExample);