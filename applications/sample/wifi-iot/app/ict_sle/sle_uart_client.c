/**
# Copyright (C) 2024 HiHope Open Source Organization .
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
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

#define SLE_MTU_SIZE_DEFAULT 1400
#define SLE_SEEK_INTERVAL_DEFAULT 100
#define SLE_SEEK_WINDOW_DEFAULT 100
#define UUID_16BIT_LEN 2
#define UUID_128BIT_LEN 16
#define SLE_UART_TASK_DELAY_MS 1000
#define SLE_UART_WAIT_SLE_CORE_READY_MS 5000
#ifndef SLE_UART_SERVER_NAME
#define SLE_UART_SERVER_NAME "sle_uart_server"
#endif
#define SLE_UART_CLIENT_LOG "[sle uart client]"
#define UUID_LEN_2 2
#define DELAY_100MS 100
#define TASK_SIZE 2048
#define PRIO 25
#define USLEEP_1000000 1000000

/* 音频帧协议常量 */
#define AUDIO_FRAME_HEADER       0x55AA
#define AUDIO_FRAME_TAIL         0xAA55
#define AUDIO_FRAME_OVERHEAD     8        /* 包头2 + 序号2 + 长度2 + 包尾2 */
#define AUDIO_CHUNK_SAMPLES      512

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

/* UART缓冲区需 >= 一帧音频大小(1032) */
#define SLE_UART_TRANSFER_SIZE 1200
static uint8_t g_app_uart_rx_buff[SLE_UART_TRANSFER_SIZE] = {0};
uint8_t receive_buf[1400] = {0}; /* match MTU */
static uart_buffer_config_t g_app_uart_buffer_config = {
    .rx_buffer = g_app_uart_rx_buff,
    .rx_buffer_size = SLE_UART_TRANSFER_SIZE};

/* ===== 丢包检测统计（利用ESP32协议中的 sequence_number 字段）===== */
static uint16_t g_expectedSeq = 0;        /* 期望收到的下一个包序号 */
static uint32_t g_totalRecvPktCount = 0;   /* 实际收到的包总数 */
static uint32_t g_lostPktCount = 0;        /* 丢包总数 */
static uint8_t  g_seqInitialized = 0;      /* 首包标记 */
/* 协商后的实际MTU大小 */
static uint16_t g_negotiatedMtu = 0;

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
    /* Client端UART1暂不需要向Server回传数据，保留空回调 */
    (void)buffer;
    (void)length;
    (void)error;
}

static void UartInitConfig(void)
{
    uart_attr_t attr = {
        .baud_rate = 921600,
        .data_bits = UART_DATA_BIT_8,
        .stop_bits = UART_STOP_BIT_1,
        .parity = UART_PARITY_NONE};

    uart_pin_config_t pin_config = {
        .tx_pin = 15,
        .rx_pin = 16,
        .cts_pin = PIN_NONE,
        .rts_pin = PIN_NONE};
    uapi_uart_deinit(1);
    uapi_uart_init(1, &pin_config, &attr, NULL, &g_app_uart_buffer_config);
    (void)uapi_uart_register_rx_callback(1, UART_RX_CONDITION_FULL_OR_IDLE,
                                         1, uart_rx_callback);
}

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
        osal_printk("%s sle_uart_client_sample_sle_enable_cbk,status error\r\n", SLE_UART_CLIENT_LOG);
    } else {
        osal_msleep(SLE_UART_TASK_DELAY_MS);
        SleUartStartScan();
    }
}

static void sle_uart_client_sample_seek_enable_cbk(errcode_t status)
{
    if (status != 0) {
        osal_printk("%s sle_uart_client_sample_seek_enable_cbk, status error\r\n", SLE_UART_CLIENT_LOG);
    }
}

static void sle_uart_client_sample_seek_result_info_cbk(SleSeekResultInfo *seek_result_data)
{
    osal_printk("%s sle uart scan data :%s\r\n", SLE_UART_CLIENT_LOG, seek_result_data->data);
    if (seek_result_data == NULL) {
        osal_printk("status error\r\n");
    } else if (strstr((const char *)seek_result_data->data, SLE_UART_SERVER_NAME) != NULL) {
        memcpy_s(&g_sle_uart_remote_addr, sizeof(sle_addr_t), &seek_result_data->addr, sizeof(sle_addr_t));
        SleStopSeek();
    }
}

static void sle_uart_client_sample_seek_disable_cbk(errcode_t status)
{
    if (status != 0) {
        osal_printk("%s sle_uart_client_sample_seek_disable_cbk,status error = %x\r\n", SLE_UART_CLIENT_LOG, status);
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

static void sle_uart_client_sample_connect_state_changed_cbk(uint16_t conn_id, const SleAddr *addr,
                                                             SleAcbStateType conn_state, SlePairStateType pair_state,
                                                             SleDiscReasonType disc_reason)
{
    unused(addr);
    unused(pair_state);
    osal_printk("%s conn state changed disc_reason:0x%x\r\n", SLE_UART_CLIENT_LOG, disc_reason);
    g_sle_uart_conn_id = conn_id;
    if (conn_state == SLE_ACB_STATE_CONNECTED) {
        osal_printk("%s SLE_ACB_STATE_CONNECTED\r\n", SLE_UART_CLIENT_LOG);
        SsapcExchangeInfo info = {0};
        info.mtuSize = SLE_MTU_SIZE_DEFAULT;
        info.version = 1;
        osal_printk("%s [MTU] requesting MTU = %d\r\n", SLE_UART_CLIENT_LOG, SLE_MTU_SIZE_DEFAULT);
        SsapcExchangeInfoReq(0, conn_id, &info);
        SlePairRemoteDevice(addr);
        /* 连接时重置丢包统计 */
        g_expectedSeq = 0;
        g_totalRecvPktCount = 0;
        g_lostPktCount = 0;
        g_seqInitialized = 0;
    } else if (conn_state == SLE_ACB_STATE_NONE) {
        osal_printk("%s SLE_ACB_STATE_NONE\r\n", SLE_UART_CLIENT_LOG);
    } else if (conn_state == SLE_ACB_STATE_DISCONNECTED) {
        osal_printk("%s SLE_ACB_STATE_DISCONNECTED\r\n", SLE_UART_CLIENT_LOG);
        /* 断连时打印丢包统计汇总 */
        uint32_t totalExpected = g_totalRecvPktCount + g_lostPktCount;
        osal_printk("%s [PKT LOSS] === DISCONNECT SUMMARY ===\r\n", SLE_UART_CLIENT_LOG);
        osal_printk("%s [PKT LOSS]   total_recv   = %u\r\n", SLE_UART_CLIENT_LOG, g_totalRecvPktCount);
        osal_printk("%s [PKT LOSS]   total_lost   = %u\r\n", SLE_UART_CLIENT_LOG, g_lostPktCount);
        if (totalExpected > 0) {
            osal_printk("%s [PKT LOSS]   loss_rate    = %u.%02u%%\r\n",
                        SLE_UART_CLIENT_LOG,
                        (g_lostPktCount * 100) / totalExpected,
                        ((g_lostPktCount * 10000) / totalExpected) % 100);
        }
        g_negotiatedMtu = 0;
        SleRemovePairedRemoteDevice(addr);
        SleUartStartScan();
    } else {
        osal_printk("%s status error\r\n", SLE_UART_CLIENT_LOG);
    }
}

static void SleUartClientSampleConnectCbkRegister(void)
{
    g_sle_uart_connect_cbk.connectStateChangedCb = sle_uart_client_sample_connect_state_changed_cbk;
    SleConnectionRegisterCallbacks(&g_sle_uart_connect_cbk);
}

static void sle_uart_client_sample_exchange_info_cbk(uint8_t client_id, uint16_t conn_id, ssap_exchange_info_t *param,
                                                     errcode_t status)
{
    osal_printk("%s exchange_info_cbk client id:%d status:%d\r\n", SLE_UART_CLIENT_LOG,
           client_id, status);
    g_negotiatedMtu = param->mtu_size;
    osal_printk("%s [MTU] negotiated MTU = %d, version = %d\r\n", SLE_UART_CLIENT_LOG,
           g_negotiatedMtu, param->version);

    ssapc_find_structure_param_t find_param = {0};
    find_param.type = 1;
    find_param.start_hdl = 1;
    find_param.end_hdl = 0xFFFF;
    int ret = ssapc_find_structure(client_id, conn_id, &find_param);
    osal_printk(" ssapc_find_structure_errcode: %d\r\n", ret);
}

static void sle_uart_client_sample_find_structure_cbk(uint8_t client_id, uint16_t conn_id,
                                                      ssapc_find_service_result_t *service,
                                                      errcode_t status)
{
    osal_printk("%s find structure cbk client:%d conn_id:%d status:%d\r\n", SLE_UART_CLIENT_LOG,
           client_id, conn_id, status);
    osal_printk("%s find structure start_hdl:[0x%02x], end_hdl:[0x%02x], uuid len:%d\r\n", SLE_UART_CLIENT_LOG,
           service->start_hdl, service->end_hdl,
           service->uuid.len);
    g_sle_uart_find_service_result.start_hdl = service->start_hdl;
    g_sle_uart_find_service_result.end_hdl = service->end_hdl;
    memcpy_s(&g_sle_uart_find_service_result.uuid, sizeof(sle_uuid_t), &service->uuid, sizeof(sle_uuid_t));
}

static void sle_uart_client_sample_find_property_cbk(uint8_t client_id, uint16_t conn_id,
                                                     ssapc_find_property_result_t *property, errcode_t status)
{
    osal_printk("%s find_property_cbk, client id:%d, conn id:%d, operate ind:%d,"
           "desc count:%d status:%d handle:%d\r\n",
           SLE_UART_CLIENT_LOG,
           client_id, conn_id,
           property->operate_indication,
           property->descriptors_count, status, property->handle);
    g_sle_uart_send_param.handle = property->handle;
    g_sle_uart_send_param.type = SSAP_PROPERTY_TYPE_VALUE;
}

static void sle_uart_client_sample_find_structure_cmp_cbk(uint8_t client_id, uint16_t conn_id,
                                                          ssapc_find_structure_result_t *structure_result,
                                                          errcode_t status)
{
    unused(conn_id);
    osal_printk("%s find_structure_cmp_cbk, client id:%d status:%d type:%d uuid len:%d\r\n",
           SLE_UART_CLIENT_LOG, client_id, status, structure_result->type, structure_result->uuid.len);
}

static void sle_uart_client_sample_write_cfm_cb(uint8_t client_id, uint16_t conn_id,
                                                ssapc_write_result_t *write_result, errcode_t status)
{
    osal_printk("%s write_cfm_cb, conn_id:%d client_id:%d status:%d handle:%02x type:%02x\r\n",
           SLE_UART_CLIENT_LOG,
           conn_id, client_id, status, write_result->handle, write_result->type);
}

static void sle_uart_client_sample_ssapc_cbk_register(ssapc_notification_callback notification_cb,
                                                      ssapc_indication_callback indication_cb)
{
    g_sle_uart_ssapc_cbk.exchange_info_cb = sle_uart_client_sample_exchange_info_cbk;
    g_sle_uart_ssapc_cbk.find_structure_cb = sle_uart_client_sample_find_structure_cbk;
    g_sle_uart_ssapc_cbk.ssapc_find_property_cbk = sle_uart_client_sample_find_property_cbk;
    g_sle_uart_ssapc_cbk.find_structure_cmp_cb = sle_uart_client_sample_find_structure_cmp_cbk;
    g_sle_uart_ssapc_cbk.write_cfm_cb = sle_uart_client_sample_write_cfm_cb;
    g_sle_uart_ssapc_cbk.notification_cb = notification_cb;
    g_sle_uart_ssapc_cbk.indication_cb = indication_cb;
    ssapc_register_callbacks(&g_sle_uart_ssapc_cbk);
}

static errcode_t sle_uuid_client_register(void)
{
    errcode_t ret;
    SleUuid app_uuid = {0};

    osal_printk("[uuid client] ssapc_register_client\r\n");
    app_uuid.len = sizeof(g_sleUuidAppUuid);
    if (memcpy_s(app_uuid.uuid, app_uuid.len, g_sleUuidAppUuid, sizeof(g_sleUuidAppUuid)) != EOK) {
        return ERRCODE_SLE_FAIL;
    }
    ret = SsapcRegisterClient(&app_uuid, &g_client_id);
    return ret;
}

/* ---------- 核心回调：收到 server 通过SLE转发的音频帧 ---------- */
void ssapc_notification_callbacks(uint8_t client_id,
                                  uint16_t conn_id, ssapc_handle_value_t *data,
                                  errcode_t status)
{
    (void)client_id;
    (void)conn_id;
    (void)status;

    uint16_t dataLen = data->data_len;

    /*
     * 帧完整性校验：
     *   最小长度 = 8 (header 2 + seq 2 + len 2 + tail 2)
     *   检查包头 0x55AA 和包尾 0xAA55（小端存储）
     */
    if (dataLen < AUDIO_FRAME_OVERHEAD) {
        osal_printk("%s [SLE RX] frame too short: %d bytes, discard\r\n",
                    SLE_UART_CLIENT_LOG, dataLen);
        return;
    }

    /* 检查包头（小端：data[0]=0xAA, data[1]=0x55 → 合成 0x55AA） */
    uint16_t header = (uint16_t)data->data[0] | ((uint16_t)data->data[1] << 8);
    /* 检查包尾（小端：data[len-2]=0x55, data[len-1]=0xAA → 合成 0xAA55） */
    uint16_t tail = (uint16_t)data->data[dataLen - 2] | ((uint16_t)data->data[dataLen - 1] << 8);

    if (header != AUDIO_FRAME_HEADER || tail != AUDIO_FRAME_TAIL) {
        osal_printk("%s [SLE RX] bad frame: header=0x%04X tail=0x%04X, discard\r\n",
                    SLE_UART_CLIENT_LOG, header, tail);
        return;
    }

    /* 解析 ESP32 协议中的 sequence_number（偏移2~3，小端） */
    uint16_t recvSeq = (uint16_t)data->data[2] | ((uint16_t)data->data[3] << 8);
    /* 解析 payload_length（偏移4~5，小端） */
    uint16_t payloadLen = (uint16_t)data->data[4] | ((uint16_t)data->data[5] << 8);

    g_totalRecvPktCount++;

    /* ---------- 丢包检测 ---------- */
    if (!g_seqInitialized) {
        /* 首包：以收到的序号为基准 */
        g_expectedSeq = recvSeq;
        g_seqInitialized = 1;
        osal_printk("%s [PKT LOSS] first pkt seq=%u, start tracking\r\n",
                    SLE_UART_CLIENT_LOG, recvSeq);
    }

    if (recvSeq != g_expectedSeq) {
        /*
         * 序号是 uint16_t，ESP32 的 sequence_number 也是 uint16_t，
         * 需要处理回绕：0xFFFF → 0x0000
         */
        uint16_t gap;
        if (recvSeq > g_expectedSeq) {
            gap = recvSeq - g_expectedSeq;
        } else {
            /* 回绕情况：比如 expected=65534, recv=1 → 实际跳了3包 */
            gap = (uint16_t)(0x10000UL + recvSeq - g_expectedSeq);
        }

        if (gap <= 1000) {
            /* 正常丢包（gap合理范围内） */
            g_lostPktCount += gap;
            osal_printk("%s [PKT LOSS] expected_seq=%u, got_seq=%u, lost=%u, total_lost=%u\r\n",
                        SLE_UART_CLIENT_LOG, g_expectedSeq, recvSeq, gap, g_lostPktCount);
        } else {
            /* gap太大，可能是乱序或重复包，仅打印警告 */
            osal_printk("%s [PKT LOSS] abnormal: expected_seq=%u, got_seq=%u, gap=%u (ignored)\r\n",
                        SLE_UART_CLIENT_LOG, g_expectedSeq, recvSeq, gap);
        }
    }

    /* 下一个期望序号（处理uint16回绕） */
    g_expectedSeq = recvSeq + 1;

    /* 每100包打印一次统计摘要 */
    if (g_totalRecvPktCount % 100 == 0) {
        uint32_t totalExpected = g_totalRecvPktCount + g_lostPktCount;
        osal_printk("%s [PKT LOSS] --- periodic stats --- recv=%u, lost=%u, total_expected=%u",
                    SLE_UART_CLIENT_LOG, g_totalRecvPktCount, g_lostPktCount, totalExpected);
        if (totalExpected > 0) {
            osal_printk(", loss_rate=%u.%02u%%",
                        (g_lostPktCount * 100) / totalExpected,
                        ((g_lostPktCount * 10000) / totalExpected) % 100);
        }
        osal_printk("\r\n");
    }

    osal_printk("%s [SLE RX] seq=%u, sle_len=%u, payload_len=%u, recv=%u, lost=%u\r\n",
                SLE_UART_CLIENT_LOG, recvSeq, dataLen, payloadLen,
                g_totalRecvPktCount, g_lostPktCount);

    /* ---------- 提取音频数据，转发到UART1 ----------
     * 只发音频payload部分（去掉包头包尾序号），
     * 让下游设备直接拿到PCM裸数据。
     * 如果下游也需要完整协议帧，改为发送 data->data, dataLen 即可。
     */
    uint8_t *audioPayload = &data->data[6]; /* 偏移6开始是音频数据 */

    if (payloadLen > 0 && payloadLen <= (dataLen - AUDIO_FRAME_OVERHEAD)) {
        int32_t uartRet = uapi_uart_write(1, audioPayload, payloadLen, 0);
        osal_printk("%s [UART1 TX] forwarded %u bytes PCM to uart1, ret=%d\r\n",
                    SLE_UART_CLIENT_LOG, payloadLen, uartRet);
    } else {
        osal_printk("%s [UART1 TX] invalid payload_len=%u for frame_len=%u, skip\r\n",
                    SLE_UART_CLIENT_LOG, payloadLen, dataLen);
    }
}

void ssapc_indication_callbacks(
    uint8_t client_id, uint16_t conn_id,
    ssapc_handle_value_t *data,
    errcode_t status)
{
    (void)client_id;
    (void)conn_id;
    (void)data;
    (void)status;
}

void SleUartClientInit()
{
    uint8_t local_addr[SLE_ADDR_LEN] = {0x13, 0x67, 0x5c, 0x07, 0x00, 0x51};
    SleAddr local_address;
    local_address.type = 0;
    (void)memcpy_s(local_address.addr, SLE_ADDR_LEN, local_addr, SLE_ADDR_LEN);
    sle_uuid_client_register();
    SleUartClientSampleSeekCbkRegister();
    SleUartClientSampleConnectCbkRegister();
    sle_uart_client_sample_ssapc_cbk_register(ssapc_notification_callbacks, ssapc_indication_callbacks);
    EnableSle();
    SleSetLocalAddr(&local_address);
}

static void SleTask(char *arg)
{
    (void)arg;
    usleep(USLEEP_1000000);
    UartInitConfig();
    SleUartClientInit();
    return NULL;
}

static void SleClientExample(void)
{
    osThreadAttr_t attr;
    attr.name = "SleTask";
    attr.attr_bits = 0U;
    attr.cb_mem = NULL;
    attr.cb_size = 0U;
    attr.stack_mem = NULL;
    attr.stack_size = TASK_SIZE;
    attr.priority = PRIO;

    if (osThreadNew(SleTask, NULL, &attr) == NULL) {
        osal_printk(" Falied to create SleTask!\n");
    } else {
        osal_printk(" create SleTask successfully !\n");
    }
}

SYS_RUN(SleClientExample);