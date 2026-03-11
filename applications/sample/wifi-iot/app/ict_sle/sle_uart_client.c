/**
 * SLE Audio Client
 * 接收 SLE 音频数据，转发到 UART1 给香橙派
 * 基于同学代码，去掉雷达部分，加上音频转发和统计
 */

#include "string.h"
#include "common_def.h"
#include "osal_debug.h"
#include "osal_task.h"
#include "cmsis_os2.h"
#include "securec.h"
#include "sle_device_discovery.h"
#include "sle_connection_manager.h"
#include "sle_ssap_client.h"
#include "sle_uart_client.h"
#include "sle_errcode.h"
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

/* ★ MTU 1500 */
#define SLE_MTU_SIZE_DEFAULT 1500

#define SLE_SEEK_INTERVAL_DEFAULT 100
#define SLE_SEEK_WINDOW_DEFAULT 100
#define UUID_16BIT_LEN 2
#define UUID_128BIT_LEN 16
#define SLE_UART_TASK_DELAY_MS 1000
#ifndef SLE_UART_SERVER_NAME
#define SLE_UART_SERVER_NAME "sle_uart_server"
#endif
#define SLE_UART_CLIENT_LOG "[sle uart client]"
#define UUID_LEN_2 2
#define DELAY_100MS 100
#define TASK_SIZE 0x2000
#define PRIO 25

/* ★★★ 音频 UART1 配置 (TX=15, RX=16, 921600) ★★★ */
#define AUDIO_UART_NUM      1
#define AUDIO_UART_BAUD     921600
#define AUDIO_UART_TX_PIN   15
#define AUDIO_UART_RX_PIN   16

/* ★★★ 统计变量 ★★★ */
static uint32_t g_sle_rx_count = 0;
static uint32_t g_sle_rx_bytes = 0;
static uint32_t g_uart_tx_count = 0;
static uint32_t g_uart_tx_bytes = 0;
static uint32_t g_uart_tx_fail = 0;

/* 序列号跟踪（检测丢包） */
static uint16_t g_last_seq = 0xFFFF;
static uint32_t g_seq_gap_count = 0;  /* seq 不连续次数 */
static uint32_t g_seq_gap_total = 0;  /* 总共丢了多少包 */

/* ---- SLE ---- */
static char g_sleUuidAppUuid[] = {0x39, 0xBE, 0xA8, 0x80, 0xFC, 0x70, 0x11, 0xEA,
                                  0xB7, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
static ssapc_find_service_result_t g_sle_uart_find_service_result = {0};
static sle_announce_seek_callbacks_t g_sle_uart_seek_cbk = {0};
static SleConnectionCallbacks g_sle_uart_connect_cbk = {0};
static ssapc_callbacks_t g_sle_uart_ssapc_cbk = {0};
static SleAddr g_sle_uart_remote_addr = {0};
ssapc_write_param_t g_sle_uart_send_param = {0};
uint16_t g_sle_uart_conn_id = 0;
uint8_t g_client_id = 0;

#define SLE_UART_TRANSFER_SIZE 256
static uint8_t g_app_uart_rx_buff[SLE_UART_TRANSFER_SIZE] = {0};
uint8_t receive_buf[1500] = {0};

static uart_buffer_config_t g_app_uart_buffer_config = {
    .rx_buffer = g_app_uart_rx_buff,
    .rx_buffer_size = SLE_UART_TRANSFER_SIZE
};

uint16_t get_g_sle_uart_conn_id(void)
{
    return g_sle_uart_conn_id;
}

ssapc_write_param_t *get_g_sle_uart_send_param(void)
{
    return &g_sle_uart_send_param;
}

static void uart_rx_callback(const void *buffer, uint16_t length, bool error)
{
    errcode_t ret;
    if (length > 0) {
        ret = uart_sle_client_send_data((uint8_t *)buffer, (uint8_t)length);
        if (ret != 0) {
            osal_printk("\r\n send_data_fail:%d\r\n", ret);
        }
    }
}

static void UartInitConfig(void)
{
    uart_attr_t attr = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_BIT_8,
        .stop_bits = UART_STOP_BIT_1,
        .parity = UART_PARITY_NONE};

    uart_pin_config_t pin_config = {
        .tx_pin = 0,
        .rx_pin = 0,
        .cts_pin = PIN_NONE,
        .rts_pin = PIN_NONE};
    uapi_uart_deinit(0);
    uapi_uart_init(0, &pin_config, &attr, NULL, &g_app_uart_buffer_config);
    (void)uapi_uart_register_rx_callback(0, UART_RX_CONDITION_FULL_OR_IDLE,
                                         1, uart_rx_callback);
}

/* ★★★ 音频 UART1 初始化（发送给香橙派） ★★★ */
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
    errcode_t ret = uapi_uart_init(AUDIO_UART_NUM, &pin_config, &attr, NULL, NULL);
    if (ret != ERRCODE_SUCC) {
        osal_printk("%s Audio UART%d init fail: %x\r\n", SLE_UART_CLIENT_LOG, AUDIO_UART_NUM, ret);
        return;
    }
    osal_printk("%s Audio UART%d ok @ %d, TX=%d RX=%d\r\n",
                SLE_UART_CLIENT_LOG, AUDIO_UART_NUM, AUDIO_UART_BAUD,
                AUDIO_UART_TX_PIN, AUDIO_UART_RX_PIN);
}

/* ========== 扫描相关（不动） ========== */
void SleUartStartScan(void)
{
    SleSeekParam param = {0};
    param.ownaddrtype = 0;
    param.filterduplicates = 0;
    param.seekfilterpolicy = 0;
    param.seekphys = 1;
    param.seekType[0] = 1;
    param.seekInterval[0] = SLE_SEEK_INTERVAL_DEFAULT;
    param.seekWindow[0] = SLE_SEEK_WINDOW_DEFAULT;
    SleSetSeekParam(&param);
    SleStartSeek();
}

static void sle_uart_client_sample_sle_enable_cbk(errcode_t status)
{
    if (status != 0) {
        osal_printk("%s sle_enable_cbk, status error\r\n", SLE_UART_CLIENT_LOG);
    } else {
        osal_msleep(SLE_UART_TASK_DELAY_MS);
        SleUartStartScan();
    }
}

static void sle_uart_client_sample_seek_enable_cbk(errcode_t status)
{
    if (status != 0) {
        osal_printk("%s seek_enable_cbk, status error\r\n", SLE_UART_CLIENT_LOG);
    }
}

static void sle_uart_client_sample_seek_result_info_cbk(SleSeekResultInfo *seek_result_data)
{
    if (seek_result_data == NULL) {
        osal_printk("%s seek_result_data NULL\r\n", SLE_UART_CLIENT_LOG);
        return;
    }
    osal_printk("%s scan data :%s\r\n", SLE_UART_CLIENT_LOG, seek_result_data->data);
    if (strstr((const char *)seek_result_data->data, SLE_UART_SERVER_NAME) != NULL) {
        (void)memcpy_s(&g_sle_uart_remote_addr, sizeof(g_sle_uart_remote_addr),
                       &seek_result_data->addr, sizeof(seek_result_data->addr));
        SleStopSeek();
    }
}

static void sle_uart_client_sample_seek_disable_cbk(errcode_t status)
{
    if (status != 0) {
        osal_printk("%s seek_disable_cbk, status error = %x\r\n", SLE_UART_CLIENT_LOG, status);
    } else {
        SleConnectRemoteDevice(&g_sle_uart_remote_addr);
    }
}

static void SleUartClientSampleSeekCbkRegister(void)
{
    g_sle_uart_seek_cbk.sle_enable_cb = sle_uart_client_sample_sle_enable_cbk;
    g_sle_uart_seek_cbk.seek_enable_cb = sle_uart_client_sample_seek_enable_cbk;
    g_sle_uart_seek_cbk.seek_result_cb = sle_uart_client_sample_seek_result_info_cbk;
    g_sle_uart_seek_cbk.seek_disable_cb = sle_uart_client_sample_seek_disable_cbk;
    sle_announce_seek_register_callbacks(&g_sle_uart_seek_cbk);
}

/* ========== 连接回调 ========== */
static void sle_uart_client_sample_connect_state_changed_cbk(uint16_t conn_id, const SleAddr *addr,
    SleAcbStateType conn_state, SlePairStateType pair_state, SleDiscReasonType disc_reason)
{
    unused(pair_state);
    osal_printk("%s conn state changed disc_reason:0x%x\r\n", SLE_UART_CLIENT_LOG, disc_reason);
    g_sle_uart_conn_id = conn_id;
    if (conn_state == SLE_ACB_STATE_CONNECTED) {
        osal_printk("%s SLE_ACB_STATE_CONNECTED\r\n", SLE_UART_CLIENT_LOG);
        SlePairRemoteDevice(addr);
        /* 统计清零 */
        g_sle_rx_count = 0;
        g_sle_rx_bytes = 0;
        g_uart_tx_count = 0;
        g_uart_tx_bytes = 0;
        g_uart_tx_fail = 0;
        g_last_seq = 0xFFFF;
        g_seq_gap_count = 0;
        g_seq_gap_total = 0;
    } else if (conn_state == SLE_ACB_STATE_NONE) {
        osal_printk("%s SLE_ACB_STATE_NONE\r\n", SLE_UART_CLIENT_LOG);
    } else if (conn_state == SLE_ACB_STATE_DISCONNECTED) {
        osal_printk("%s DISCONNECTED. STAT: sle_rx=%u uart_tx=%u uart_fail=%u seq_gap=%u(lost~%u)\r\n",
                    SLE_UART_CLIENT_LOG,
                    (unsigned)g_sle_rx_count, (unsigned)g_uart_tx_count,
                    (unsigned)g_uart_tx_fail,
                    (unsigned)g_seq_gap_count, (unsigned)g_seq_gap_total);
        SleRemovePairedRemoteDevice(addr);
        SleUartStartScan();
    } else {
        osal_printk("%s status error\r\n", SLE_UART_CLIENT_LOG);
    }
}

static void sle_uart_client_sample_pair_complete_cbk(uint16_t conn_id, const SleAddr *addr,
    errcode_t status)
{
    (void)addr;
    osal_printk("%s pair complete conn_id:%d status:0x%x\r\n",
           SLE_UART_CLIENT_LOG, conn_id, status);

    if (status == ERRCODE_SUCC) {
        SsapcExchangeInfo info = {0};
        info.mtuSize = SLE_MTU_SIZE_DEFAULT;
        info.version = 1;
        SsapcExchangeInfoReq(0, conn_id, &info);
        osal_printk("%s MTU exchange requested: %u\r\n",
               SLE_UART_CLIENT_LOG, SLE_MTU_SIZE_DEFAULT);
    }
}

static void SleUartClientSampleConnectCbkRegister(void)
{
    g_sle_uart_connect_cbk.connectStateChangedCb = sle_uart_client_sample_connect_state_changed_cbk;
    g_sle_uart_connect_cbk.pairCompleteCb = sle_uart_client_sample_pair_complete_cbk;
    SleConnectionRegisterCallbacks(&g_sle_uart_connect_cbk);
}

/* ========== SSAPC 回调（不动） ========== */
static void sle_uart_client_sample_exchange_info_cbk(uint8_t client_id, uint16_t conn_id,
    ssap_exchange_info_t *param, errcode_t status)
{
    osal_printk("%s exchange_info_cbk client:%d status:%d mtu:%d ver:%d\r\n",
           SLE_UART_CLIENT_LOG, client_id, status, param->mtu_size, param->version);
    ssapc_find_structure_param_t find_param = {0};
    find_param.type = 1;
    find_param.start_hdl = 1;
    find_param.end_hdl = 0xFFFF;
    int ret = ssapc_find_structure(client_id, conn_id, &find_param);
    osal_printk(" ssapc_find_structure_errcode: %d\r\n", ret);
}

static void sle_uart_client_sample_find_structure_cbk(uint8_t client_id, uint16_t conn_id,
    ssapc_find_service_result_t *service, errcode_t status)
{
    osal_printk("%s find_structure_cbk client:%d conn:%d status:%d\r\n",
           SLE_UART_CLIENT_LOG, client_id, conn_id, status);
    g_sle_uart_find_service_result.start_hdl = service->start_hdl;
    g_sle_uart_find_service_result.end_hdl = service->end_hdl;
    memcpy_s(&g_sle_uart_find_service_result.uuid, sizeof(sle_uuid_t),
             &service->uuid, sizeof(sle_uuid_t));
}

static void sle_uart_client_sample_find_property_cbk(uint8_t client_id, uint16_t conn_id,
    ssapc_find_property_result_t *property, errcode_t status)
{
    osal_printk("%s find_property_cbk client:%d conn:%d handle:%d status:%d\r\n",
           SLE_UART_CLIENT_LOG, client_id, conn_id, property->handle, status);
    g_sle_uart_send_param.handle = property->handle;
    g_sle_uart_send_param.type = SSAP_PROPERTY_TYPE_VALUE;
}

static void sle_uart_client_sample_find_structure_cmp_cbk(uint8_t client_id, uint16_t conn_id,
    ssapc_find_structure_result_t *structure_result, errcode_t status)
{
    unused(conn_id);
    osal_printk("%s find_structure_cmp_cbk client:%d status:%d type:%d\r\n",
           SLE_UART_CLIENT_LOG, client_id, status, structure_result->type);
    osal_printk("%s ===== Ready to receive audio! =====\r\n", SLE_UART_CLIENT_LOG);
}

static void sle_uart_client_sample_write_cfm_cb(uint8_t client_id, uint16_t conn_id,
    ssapc_write_result_t *write_result, errcode_t status)
{
    osal_printk("%s write_cfm conn:%d client:%d status:%d handle:%02x\r\n",
           SLE_UART_CLIENT_LOG, conn_id, client_id, status, write_result->handle);
}

/* ★★★ notification 回调：接收音频数据 → 检测丢包 → 转发 UART1 ★★★ */
void ssapc_notification_callbacks(uint8_t client_id, uint16_t conn_id,
                                 ssapc_handle_value_t *data, errcode_t status)
{
    (void)client_id;
    (void)conn_id;

    if (status != ERRCODE_SUCC || data == NULL || data->data == NULL || data->data_len == 0) {
        return;
    }

    g_sle_rx_count++;
    g_sle_rx_bytes += data->data_len;

    /* ★ 检测丢包：解析协议中的 seq 字段
     * 协议格式: [0x55AA(2)] [seq(2)] [payload_len(2)] [payload(N)] [0xAA55(2)]
     * seq 在偏移 2-3 字节处
     */
    if (data->data_len >= 6) {
        uint16_t hdr = (uint16_t)(data->data[0] | (data->data[1] << 8));
        if (hdr == 0x55AA) {
            uint16_t seq = (uint16_t)(data->data[2] | (data->data[3] << 8));
            if (g_last_seq != 0xFFFF) {
                uint16_t expected = (uint16_t)(g_last_seq + 1);
                if (seq != expected) {
                    uint16_t gap;
                    if (seq > expected) {
                        gap = seq - expected;
                    } else {
                        gap = (uint16_t)(65536 - expected + seq);
                    }
                    g_seq_gap_count++;
                    g_seq_gap_total += gap;
                    if (g_seq_gap_count <= 10 || (g_seq_gap_count % 50) == 0) {
                        osal_printk("%s SEQ GAP! expected=%u got=%u lost=%u (total_gaps=%u lost~%u)\r\n",
                                    SLE_UART_CLIENT_LOG,
                                    (unsigned)expected, (unsigned)seq, (unsigned)gap,
                                    (unsigned)g_seq_gap_count, (unsigned)g_seq_gap_total);
                    }
                }
            }
            g_last_seq = seq;
        }
    }

    /* 每 200 包打印统计 */
    if ((g_sle_rx_count % 200) == 0) {
        osal_printk("%s SLE RX: pkt=%u bytes=%u | UART TX: pkt=%u bytes=%u fail=%u | SEQ gap=%u lost~%u\r\n",
                    SLE_UART_CLIENT_LOG,
                    (unsigned)g_sle_rx_count, (unsigned)g_sle_rx_bytes,
                    (unsigned)g_uart_tx_count, (unsigned)g_uart_tx_bytes, (unsigned)g_uart_tx_fail,
                    (unsigned)g_seq_gap_count, (unsigned)g_seq_gap_total);
    }

    /* 前 3 包打印详细 */
    if (g_sle_rx_count <= 3) {
        osal_printk("%s SLE RX[%u]: %02x %02x %02x %02x %02x %02x %02x %02x (len=%u)\r\n",
                    SLE_UART_CLIENT_LOG, (unsigned)g_sle_rx_count,
                    data->data[0], data->data[1], data->data[2], data->data[3],
                    data->data[4], data->data[5], data->data[6], data->data[7],
                    (unsigned)data->data_len);
    }

    /* ★ 转发到 UART1（发给香橙派） */
    errcode_t ret = uapi_uart_write(AUDIO_UART_NUM, data->data, data->data_len, 0);
    if (ret == ERRCODE_SUCC) {
        g_uart_tx_count++;
        g_uart_tx_bytes += data->data_len;
    } else {
        g_uart_tx_fail++;
        if (g_uart_tx_fail <= 5) {
            osal_printk("%s UART TX fail: ret=%x len=%u\r\n",
                        SLE_UART_CLIENT_LOG, (unsigned)ret, (unsigned)data->data_len);
        }
    }
}

void ssapc_indication_callbacks(uint8_t client_id, uint16_t conn_id,
                                ssapc_handle_value_t *data, errcode_t status)
{
    (void)client_id; (void)conn_id; (void)data; (void)status;
}

static void sle_uart_client_sample_ssapc_cbk_register(ssapc_notification_callback notification_cb,
                                                      ssapc_indication_callback indication_cb)
{
    g_sle_uart_ssapc_cbk.exchange_info_cb      = sle_uart_client_sample_exchange_info_cbk;
    g_sle_uart_ssapc_cbk.find_structure_cb     = sle_uart_client_sample_find_structure_cbk;
    g_sle_uart_ssapc_cbk.ssapc_find_property_cbk = sle_uart_client_sample_find_property_cbk;
    g_sle_uart_ssapc_cbk.find_structure_cmp_cb = sle_uart_client_sample_find_structure_cmp_cbk;
    g_sle_uart_ssapc_cbk.write_cfm_cb          = sle_uart_client_sample_write_cfm_cb;
    g_sle_uart_ssapc_cbk.notification_cb       = notification_cb;
    g_sle_uart_ssapc_cbk.indication_cb         = indication_cb;
    ssapc_register_callbacks(&g_sle_uart_ssapc_cbk);
}

/* ========== Client 注册（不动） ========== */
static errcode_t sle_uuid_client_register(void)
{
    SleUuid app_uuid = {0};
    app_uuid.len = sizeof(g_sleUuidAppUuid);
    if (memcpy_s(app_uuid.uuid, app_uuid.len, g_sleUuidAppUuid, sizeof(g_sleUuidAppUuid)) != EOK) {
        return ERRCODE_SLE_FAIL;
    }
    return SsapcRegisterClient(&app_uuid, &g_client_id);
}

/* ========== 发送函数（不动） ========== */
errcode_t sle_uart_client_send_report_by_handle(const uint8_t *data, uint8_t len)
{
    if (data == NULL || len == 0 || len > sizeof(receive_buf)) return ERRCODE_FAIL;
    if (g_sle_uart_conn_id == 0 || g_sle_uart_send_param.handle == 0) return ERRCODE_FAIL;

    ssapc_write_param_t param = {0};
    param.handle   = g_sle_uart_send_param.handle;
    param.type     = SSAP_PROPERTY_TYPE_VALUE;
    param.data     = receive_buf;
    param.data_len = len;
    if (memcpy_s(param.data, sizeof(receive_buf), data, len) != EOK) return ERRCODE_FAIL;

    return SsapcWriteReq(g_client_id, g_sle_uart_conn_id, &param);
}

int uart_sle_client_send_data(uint8_t *data, uint8_t length)
{
    osal_mdelay(DELAY_100MS);
    return sle_uart_client_send_report_by_handle(data, length);
}

/* ========== 初始化（不动） ========== */
void SleUartClientInit(void)
{
    uint8_t local_addr[SLE_ADDR_LEN] = {0x13, 0x67, 0x5c, 0x07, 0x00, 0x51};
    SleAddr local_address;
    local_address.type = 0;
    (void)memcpy_s(local_address.addr, SLE_ADDR_LEN, local_addr, SLE_ADDR_LEN);
    sle_uuid_client_register();
    SleUartClientSampleSeekCbkRegister();
    SleUartClientSampleConnectCbkRegister();
    sle_uart_client_sample_ssapc_cbk_register(ssapc_notification_callbacks,
                                              ssapc_indication_callbacks);
    EnableSle();
    SleSetLocalAddr(&local_address);
}

/* ========== 主任务 ========== */
static void SleTask(void *arg)
{
    (void)arg;

    osal_msleep(1000);
    UartInitConfig();     /* UART0 调试口 */
    AudioUartInit();      /* ★ UART1 音频输出口 */
    SleUartClientInit();

    /* 主循环：定期打印统计 */
    while (1) {
        osal_msleep(5000);
        osal_printk("%s [5s STAT] SLE RX: pkt=%u bytes=%u | UART TX: pkt=%u fail=%u | SEQ gap=%u lost~%u\r\n",
                    SLE_UART_CLIENT_LOG,
                    (unsigned)g_sle_rx_count, (unsigned)g_sle_rx_bytes,
                    (unsigned)g_uart_tx_count, (unsigned)g_uart_tx_fail,
                    (unsigned)g_seq_gap_count, (unsigned)g_seq_gap_total);
    }
}

static void SleClientExample(void)
{
    osThreadAttr_t attr = {0};
    attr.name       = "SleTask";
    attr.stack_size = TASK_SIZE;
    attr.priority   = PRIO;

    if (osThreadNew(SleTask, NULL, &attr) == NULL) {
        osal_printk(" Failed to create SleTask!\n");
    } else {
        osal_printk(" create SleTask successfully!\n");
    }
}

SYS_RUN(SleClientExample);