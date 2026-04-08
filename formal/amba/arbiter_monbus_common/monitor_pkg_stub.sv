// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Minimal monitor package stubs for yosys formal verification.
// Provides only the constants, types, and functions actually used
// by arbiter_monbus_common. String functions are stubbed out.

`timescale 1ns / 1ps

package monitor_common_pkg;

    typedef enum logic [2:0] {
        PROTOCOL_AXI    = 3'b000,
        PROTOCOL_AXIS   = 3'b001,
        PROTOCOL_APB    = 3'b010,
        PROTOCOL_ARB    = 3'b011,
        PROTOCOL_CORE   = 3'b100
    } protocol_type_t;

    localparam logic [3:0] PktTypeError      = 4'h0;
    localparam logic [3:0] PktTypeCompletion = 4'h1;
    localparam logic [3:0] PktTypeThreshold  = 4'h2;
    localparam logic [3:0] PktTypeTimeout    = 4'h3;
    localparam logic [3:0] PktTypePerf       = 4'h4;
    localparam logic [3:0] PktTypeCredit     = 4'h5;
    localparam logic [3:0] PktTypeChannel    = 4'h6;
    localparam logic [3:0] PktTypeStream     = 4'h7;
    localparam logic [3:0] PktTypeAddrMatch  = 4'h8;
    localparam logic [3:0] PktTypeAPB        = 4'h9;
    localparam logic [3:0] PktTypeDebug      = 4'hF;

    typedef logic [63:0] monitor_packet_t;

    // Minimal transfer/state types needed for compilation
    typedef enum logic [1:0] { AXIS_TRANSFER_DATA=0, AXIS_TRANSFER_LAST=1,
                                AXIS_TRANSFER_NULL=2, AXIS_TRANSFER_IDLE=3 } axis_transfer_type_t;
    typedef enum logic [1:0] { AXIS_HANDSHAKE_IDLE=0, AXIS_HANDSHAKE_VALID=1,
                                AXIS_HANDSHAKE_READY=2, AXIS_HANDSHAKE_ACTIVE=3 } axis_handshake_state_t;
    typedef enum logic [1:0] { APB_PHASE_IDLE=0, APB_PHASE_SETUP=1,
                                APB_PHASE_ACCESS=2, APB_PHASE_ENABLE=3 } apb_phase_t;
    typedef enum logic [2:0] { APB_PROT_NORMAL=0 } apb_prot_type_t;
    typedef enum logic [1:0] { ARB_TYPE_ROUND_ROBIN=0, ARB_TYPE_WEIGHTED_RR=1,
                                ARB_TYPE_PRIORITY=2, ARB_TYPE_CUSTOM=3 } arb_type_t;
    typedef enum logic [2:0] { ARB_STATE_IDLE=0, ARB_STATE_ARBITRATE=1, ARB_STATE_GRANT=2,
                                ARB_STATE_BLOCKED=3, ARB_STATE_WEIGHT_UPD=4, ARB_STATE_ERROR=5 } arb_state_t;
    typedef enum logic [2:0] { TRANS_IDLE=0 } transaction_state_t;

    function automatic logic [63:0] create_monitor_packet(
        input logic [3:0]     packet_type,
        input logic [2:0]     protocol,
        input logic [3:0]     event_code,
        input logic [5:0]     channel_id,
        input logic [3:0]     unit_id,
        input logic [7:0]     agent_id,
        input logic [34:0]    event_data
    );
        create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
    endfunction

    function automatic logic [3:0] get_packet_type(input logic [63:0] pkt);
        get_packet_type = pkt[63:60];
    endfunction

    function automatic logic [2:0] get_protocol_type_bits(input logic [63:0] pkt);
        get_protocol_type_bits = pkt[59:57];
    endfunction

    function automatic logic [3:0] get_event_code(input logic [63:0] pkt);
        get_event_code = pkt[56:53];
    endfunction

    function automatic logic [5:0] get_channel_id(input logic [63:0] pkt);
        get_channel_id = pkt[52:47];
    endfunction

    function automatic logic [3:0] get_unit_id(input logic [63:0] pkt);
        get_unit_id = pkt[46:43];
    endfunction

    function automatic logic [7:0] get_agent_id(input logic [63:0] pkt);
        get_agent_id = pkt[42:35];
    endfunction

    function automatic logic [34:0] get_event_data(input logic [63:0] pkt);
        get_event_data = pkt[34:0];
    endfunction

endpackage : monitor_common_pkg

package monitor_amba4_pkg;
    // Stub - arbiter_monbus_common does not use AMBA4 types directly
endpackage : monitor_amba4_pkg

package monitor_arbiter_pkg;

    typedef enum logic [3:0] {
        ARB_ERR_STARVATION=0, ARB_ERR_ACK_TIMEOUT=1, ARB_ERR_PROTOCOL_VIOLATION=2,
        ARB_ERR_CREDIT_VIOLATION=3, ARB_ERR_FAIRNESS_VIOLATION=4, ARB_ERR_WEIGHT_UNDERFLOW=5,
        ARB_ERR_CONCURRENT_GRANTS=6, ARB_ERR_INVALID_GRANT_ID=7, ARB_ERR_ORPHAN_ACK=8,
        ARB_ERR_GRANT_OVERLAP=9, ARB_ERR_MASK_ERROR=10, ARB_ERR_STATE_MACHINE=11,
        ARB_ERR_CONFIGURATION=12, ARB_ERR_RESERVED_D=13, ARB_ERR_RESERVED_E=14,
        ARB_ERR_USER_DEFINED=15
    } arb_error_code_t;

    typedef enum logic [3:0] {
        ARB_TIMEOUT_GRANT_ACK=0, ARB_TIMEOUT_REQUEST_HOLD=1, ARB_TIMEOUT_WEIGHT_UPDATE=2,
        ARB_TIMEOUT_BLOCK_RELEASE=3, ARB_TIMEOUT_CREDIT_UPDATE=4, ARB_TIMEOUT_STATE_CHANGE=5,
        ARB_TIMEOUT_RESERVED_6=6, ARB_TIMEOUT_RESERVED_7=7, ARB_TIMEOUT_RESERVED_8=8,
        ARB_TIMEOUT_RESERVED_9=9, ARB_TIMEOUT_RESERVED_A=10, ARB_TIMEOUT_RESERVED_B=11,
        ARB_TIMEOUT_RESERVED_C=12, ARB_TIMEOUT_RESERVED_D=13, ARB_TIMEOUT_RESERVED_E=14,
        ARB_TIMEOUT_USER_DEFINED=15
    } arb_timeout_code_t;

    typedef enum logic [3:0] {
        ARB_COMPL_GRANT_ISSUED=0, ARB_COMPL_ACK_RECEIVED=1, ARB_COMPL_TRANSACTION=2,
        ARB_COMPL_WEIGHT_UPDATE=3, ARB_COMPL_CREDIT_CYCLE=4, ARB_COMPL_FAIRNESS_PERIOD=5,
        ARB_COMPL_BLOCK_PERIOD=6, ARB_COMPL_RESERVED_7=7, ARB_COMPL_RESERVED_8=8,
        ARB_COMPL_RESERVED_9=9, ARB_COMPL_RESERVED_A=10, ARB_COMPL_RESERVED_B=11,
        ARB_COMPL_RESERVED_C=12, ARB_COMPL_RESERVED_D=13, ARB_COMPL_RESERVED_E=14,
        ARB_COMPL_USER_DEFINED=15
    } arb_completion_code_t;

    typedef enum logic [3:0] {
        ARB_THRESH_REQUEST_LATENCY=0, ARB_THRESH_ACK_LATENCY=1, ARB_THRESH_FAIRNESS_DEV=2,
        ARB_THRESH_ACTIVE_REQUESTS=3, ARB_THRESH_GRANT_RATE=4, ARB_THRESH_EFFICIENCY=5,
        ARB_THRESH_CREDIT_LOW=6, ARB_THRESH_RESERVED_7=7, ARB_THRESH_RESERVED_8=8,
        ARB_THRESH_RESERVED_9=9, ARB_THRESH_RESERVED_A=10, ARB_THRESH_RESERVED_B=11,
        ARB_THRESH_RESERVED_C=12, ARB_THRESH_RESERVED_D=13, ARB_THRESH_RESERVED_E=14,
        ARB_THRESH_USER_DEFINED=15
    } arb_threshold_code_t;

    typedef enum logic [3:0] {
        ARB_PERF_GRANT_ISSUED=0, ARB_PERF_ACK_LATENCY=1, ARB_PERF_THROUGHPUT=2,
        ARB_PERF_UTILIZATION=3, ARB_PERF_WEIGHT_DISTRIBUTION=4, ARB_PERF_BLOCK_RATIO=5,
        ARB_PERF_RESERVED_6=6, ARB_PERF_RESERVED_7=7, ARB_PERF_RESERVED_8=8,
        ARB_PERF_RESERVED_9=9, ARB_PERF_RESERVED_A=10, ARB_PERF_RESERVED_B=11,
        ARB_PERF_RESERVED_C=12, ARB_PERF_RESERVED_D=13, ARB_PERF_RESERVED_E=14,
        ARB_PERF_USER_DEFINED=15
    } arb_performance_code_t;

    typedef enum logic [3:0] {
        ARB_DBG_STATE_CHANGE=0, ARB_DBG_WEIGHT_UPDATE=1, ARB_DBG_CREDIT_UPDATE=2,
        ARB_DBG_QUEUE_STATUS=3, ARB_DBG_MASK_STATUS=4, ARB_DBG_RESERVED_5=5,
        ARB_DBG_RESERVED_6=6, ARB_DBG_RESERVED_7=7, ARB_DBG_RESERVED_8=8,
        ARB_DBG_RESERVED_9=9, ARB_DBG_RESERVED_A=10, ARB_DBG_RESERVED_B=11,
        ARB_DBG_RESERVED_C=12, ARB_DBG_RESERVED_D=13, ARB_DBG_RESERVED_E=14,
        ARB_DBG_USER_DEFINED=15
    } arb_debug_code_t;

    // Stub types for CORE (not used by arbiter_monbus_common directly)
    typedef enum logic [3:0] { CORE_ERR_STUB=0 } core_error_code_t;
    typedef enum logic [3:0] { CORE_TIMEOUT_STUB=0 } core_timeout_code_t;
    typedef enum logic [3:0] { CORE_COMPL_STUB=0 } core_completion_code_t;
    typedef enum logic [3:0] { CORE_THRESH_STUB=0 } core_threshold_code_t;
    typedef enum logic [3:0] { CORE_PERF_STUB=0 } core_performance_code_t;
    typedef enum logic [3:0] { CORE_DBG_STUB=0 } core_debug_code_t;
    typedef logic [3:0] arb_core_event_code_t;

endpackage : monitor_arbiter_pkg

package monitor_pkg;
    // Empty - all needed symbols come from the individual protocol packages
endpackage : monitor_pkg
