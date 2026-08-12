// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apbx_xbar_monitored
// Purpose: Apb Xbar Monitored module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apbx_xbar_monitored
    import monitor_common_pkg::*;   // monitor_packet_t, monbus_timestamp_t
#(
    parameter int NUM_MASTERS = 3,
    parameter int NUM_SLAVES = 4,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH/8,

    // Monitor parameters
    parameter int MAX_TRANSACTIONS = 8,  // APB is simple, 8 is sufficient
    parameter int UNIT_ID = 0,           // Crossbar unit ID

    // Agent IDs are assigned BASE + port index. Only the two bases are
    // parameters: the generate loops always computed BASE + index, so the
    // former per-port parameters (AGENT_ID_M1/M2, AGENT_ID_S1/S2/S3) could be
    // overridden with no effect at all. A parameter that cannot change
    // behaviour is worse than none, because it reads as configurable.
    parameter logic [7:0] AGENT_ID_M_BASE = 8'h10,  // masters: 0x10, 0x11, 0x12
    parameter logic [7:0] AGENT_ID_S_BASE = 8'h40   // slaves:  0x40..0x43
) (
    input  logic pclk,
    input  logic presetn,

    // =============================================================================
    // Master Interfaces (3 masters)
    // =============================================================================

    // Master 0
    input  logic                  m0_apb_psel,
    input  logic                  m0_apb_penable,
    input  logic                  m0_apb_pwrite,
    input  logic [2:0]            m0_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m0_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m0_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m0_apb_pstrb,
    output logic                  m0_apb_pready,
    output logic [DATA_WIDTH-1:0] m0_apb_prdata,
    output logic                  m0_apb_pslverr,

    // Master 1
    input  logic                  m1_apb_psel,
    input  logic                  m1_apb_penable,
    input  logic                  m1_apb_pwrite,
    input  logic [2:0]            m1_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m1_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m1_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m1_apb_pstrb,
    output logic                  m1_apb_pready,
    output logic [DATA_WIDTH-1:0] m1_apb_prdata,
    output logic                  m1_apb_pslverr,

    // Master 2
    input  logic                  m2_apb_psel,
    input  logic                  m2_apb_penable,
    input  logic                  m2_apb_pwrite,
    input  logic [2:0]            m2_apb_pprot,
    input  logic [ADDR_WIDTH-1:0] m2_apb_paddr,
    input  logic [DATA_WIDTH-1:0] m2_apb_pwdata,
    input  logic [STRB_WIDTH-1:0] m2_apb_pstrb,
    output logic                  m2_apb_pready,
    output logic [DATA_WIDTH-1:0] m2_apb_prdata,
    output logic                  m2_apb_pslverr,

    // =============================================================================
    // Slave Interfaces (4 slaves)
    // =============================================================================

    // Slave 0 (Memory-mapped peripheral 0x0000-0x0FFF)
    output logic                  s0_apb_psel,
    output logic                  s0_apb_penable,
    output logic                  s0_apb_pwrite,
    output logic [2:0]            s0_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s0_apb_paddr,
    output logic [DATA_WIDTH-1:0] s0_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s0_apb_pstrb,
    input  logic                  s0_apb_pready,
    input  logic [DATA_WIDTH-1:0] s0_apb_prdata,
    input  logic                  s0_apb_pslverr,

    // Slave 1 (Memory-mapped peripheral 0x1000-0x1FFF)
    output logic                  s1_apb_psel,
    output logic                  s1_apb_penable,
    output logic                  s1_apb_pwrite,
    output logic [2:0]            s1_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s1_apb_paddr,
    output logic [DATA_WIDTH-1:0] s1_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s1_apb_pstrb,
    input  logic                  s1_apb_pready,
    input  logic [DATA_WIDTH-1:0] s1_apb_prdata,
    input  logic                  s1_apb_pslverr,

    // Slave 2 (Memory-mapped peripheral 0x2000-0x2FFF)
    output logic                  s2_apb_psel,
    output logic                  s2_apb_penable,
    output logic                  s2_apb_pwrite,
    output logic [2:0]            s2_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s2_apb_paddr,
    output logic [DATA_WIDTH-1:0] s2_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s2_apb_pstrb,
    input  logic                  s2_apb_pready,
    input  logic [DATA_WIDTH-1:0] s2_apb_prdata,
    input  logic                  s2_apb_pslverr,

    // Slave 3 (Memory-mapped peripheral 0x3000-0x3FFF)
    output logic                  s3_apb_psel,
    output logic                  s3_apb_penable,
    output logic                  s3_apb_pwrite,
    output logic [2:0]            s3_apb_pprot,
    output logic [ADDR_WIDTH-1:0] s3_apb_paddr,
    output logic [DATA_WIDTH-1:0] s3_apb_pwdata,
    output logic [STRB_WIDTH-1:0] s3_apb_pstrb,
    input  logic                  s3_apb_pready,
    input  logic [DATA_WIDTH-1:0] s3_apb_prdata,
    input  logic                  s3_apb_pslverr,

    // =============================================================================
    // Aggregated Monitor Bus Output
    // =============================================================================
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output monitor_common_pkg::monitor_packet_t monbus_packet,

    // =============================================================================
    // Configuration Inputs
    // =============================================================================
    // cfg_compl_enable used to sit here. It was declared and never wired to
    // anything, and apb4_monitor has no completion-packet control -- the
    // closest thing is cfg_perf_enable, which this module already exposes.
    input logic cfg_error_enable,    // Enable error packet reporting
    input logic cfg_timeout_enable,  // Enable timeout detection
    input logic cfg_perf_enable      // Enable performance metrics
);

    // =============================================================================
    // Internal APB Crossbar Signals (without monitors)
    // =============================================================================

    // Master-side internal (pre-monitor)
    logic [NUM_MASTERS-1:0]                  xbar_m_psel;
    logic [NUM_MASTERS-1:0]                  xbar_m_penable;
    logic [NUM_MASTERS-1:0]                  xbar_m_pwrite;
    logic [NUM_MASTERS-1:0][2:0]             xbar_m_pprot;
    logic [NUM_MASTERS-1:0][ADDR_WIDTH-1:0]  xbar_m_paddr;
    logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0]  xbar_m_pwdata;
    logic [NUM_MASTERS-1:0][STRB_WIDTH-1:0]  xbar_m_pstrb;
    logic [NUM_MASTERS-1:0]                  xbar_m_pready;
    logic [NUM_MASTERS-1:0][DATA_WIDTH-1:0]  xbar_m_prdata;
    logic [NUM_MASTERS-1:0]                  xbar_m_pslverr;

    // Slave-side internal (pre-monitor)
    logic [NUM_SLAVES-1:0]                  xbar_s_psel;
    logic [NUM_SLAVES-1:0]                  xbar_s_penable;
    logic [NUM_SLAVES-1:0]                  xbar_s_pwrite;
    logic [NUM_SLAVES-1:0][2:0]             xbar_s_pprot;
    logic [NUM_SLAVES-1:0][ADDR_WIDTH-1:0]  xbar_s_paddr;
    logic [NUM_SLAVES-1:0][DATA_WIDTH-1:0]  xbar_s_pwdata;
    logic [NUM_SLAVES-1:0][STRB_WIDTH-1:0]  xbar_s_pstrb;
    logic [NUM_SLAVES-1:0]                  xbar_s_pready;
    logic [NUM_SLAVES-1:0][DATA_WIDTH-1:0]  xbar_s_prdata;
    logic [NUM_SLAVES-1:0]                  xbar_s_pslverr;

    // Connect external master interfaces to internal crossbar inputs
    assign xbar_m_psel    = {m2_apb_psel, m1_apb_psel, m0_apb_psel};
    assign xbar_m_penable = {m2_apb_penable, m1_apb_penable, m0_apb_penable};
    assign xbar_m_pwrite  = {m2_apb_pwrite, m1_apb_pwrite, m0_apb_pwrite};
    assign xbar_m_pprot   = {m2_apb_pprot, m1_apb_pprot, m0_apb_pprot};
    assign xbar_m_paddr   = {m2_apb_paddr, m1_apb_paddr, m0_apb_paddr};
    assign xbar_m_pwdata  = {m2_apb_pwdata, m1_apb_pwdata, m0_apb_pwdata};
    assign xbar_m_pstrb   = {m2_apb_pstrb, m1_apb_pstrb, m0_apb_pstrb};

    assign {m2_apb_pready, m1_apb_pready, m0_apb_pready}   = xbar_m_pready;
    assign {m2_apb_prdata, m1_apb_prdata, m0_apb_prdata}   = xbar_m_prdata;
    assign {m2_apb_pslverr, m1_apb_pslverr, m0_apb_pslverr} = xbar_m_pslverr;

    // Connect internal crossbar outputs to external slave interfaces
    assign {s3_apb_psel, s2_apb_psel, s1_apb_psel, s0_apb_psel}       = xbar_s_psel;
    assign {s3_apb_penable, s2_apb_penable, s1_apb_penable, s0_apb_penable} = xbar_s_penable;
    assign {s3_apb_pwrite, s2_apb_pwrite, s1_apb_pwrite, s0_apb_pwrite}     = xbar_s_pwrite;
    assign {s3_apb_pprot, s2_apb_pprot, s1_apb_pprot, s0_apb_pprot}   = xbar_s_pprot;
    assign {s3_apb_paddr, s2_apb_paddr, s1_apb_paddr, s0_apb_paddr}   = xbar_s_paddr;
    assign {s3_apb_pwdata, s2_apb_pwdata, s1_apb_pwdata, s0_apb_pwdata} = xbar_s_pwdata;
    assign {s3_apb_pstrb, s2_apb_pstrb, s1_apb_pstrb, s0_apb_pstrb}   = xbar_s_pstrb;

    assign xbar_s_pready  = {s3_apb_pready, s2_apb_pready, s1_apb_pready, s0_apb_pready};
    assign xbar_s_prdata  = {s3_apb_prdata, s2_apb_prdata, s1_apb_prdata, s0_apb_prdata};
    assign xbar_s_pslverr = {s3_apb_pslverr, s2_apb_pslverr, s1_apb_pslverr, s0_apb_pslverr};

    // =============================================================================
    // APB Crossbar Instance (Thin Variant - Tested and Working)
    // =============================================================================

    apbx_xbar_thin #(
        .M(NUM_MASTERS),
        .S(NUM_SLAVES),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_apbx_xbar (
        .pclk        (pclk),
        .presetn     (presetn),

        // Address map configuration
        .SLAVE_ENABLE    ({NUM_SLAVES{1'b1}}),                       // All slaves enabled
        .SLAVE_ADDR_BASE ({32'h3000, 32'h2000, 32'h1000, 32'h0000}), // 4KB regions
        .SLAVE_ADDR_LIMIT({32'h3FFF, 32'h2FFF, 32'h1FFF, 32'h0FFF}),
        .THRESHOLDS      ({NUM_SLAVES{4'h4}}),                       // Threshold = 4 cycles

        // Master interfaces
        .m_apb_psel    (xbar_m_psel),
        .m_apb_penable (xbar_m_penable),
        .m_apb_pwrite  (xbar_m_pwrite),
        .m_apb_pprot   (xbar_m_pprot),
        .m_apb_paddr   (xbar_m_paddr),
        .m_apb_pwdata  (xbar_m_pwdata),
        .m_apb_pstrb   (xbar_m_pstrb),
        .m_apb_pready  (xbar_m_pready),
        .m_apb_prdata  (xbar_m_prdata),
        .m_apb_pslverr (xbar_m_pslverr),

        // Slave interfaces
        .s_apb_psel    (xbar_s_psel),
        .s_apb_penable (xbar_s_penable),
        .s_apb_pwrite  (xbar_s_pwrite),
        .s_apb_pprot   (xbar_s_pprot),
        .s_apb_paddr   (xbar_s_paddr),
        .s_apb_pwdata  (xbar_s_pwdata),
        .s_apb_pstrb   (xbar_s_pstrb),
        .s_apb_pready  (xbar_s_pready),
        .s_apb_prdata  (xbar_s_prdata),
        .s_apb_pslverr (xbar_s_pslverr)
    );

    // =============================================================================
    // Monitor Bus Signals (7 monitors total)
    // =============================================================================
    localparam int NUM_MONITORS = NUM_MASTERS + NUM_SLAVES;  // 3 + 4 = 7

    logic [NUM_MONITORS-1:0]              mon_valid;
    logic [NUM_MONITORS-1:0]              mon_ready;
    monitor_common_pkg::monitor_packet_t  mon_packet [NUM_MONITORS];

    // Free-running time broadcast for the monitors' side-band timestamp. A real
    // system drives this from the monbus_group time source.
    monitor_common_pkg::monbus_timestamp_t mon_time;
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) mon_time <= '0;
        else          mon_time <= mon_time + 1'b1;
    end

    // APB -> cmd/rsp tap. apb4_monitor watches the translated side of a bridge,
    // never the wire; APB completes in the ACCESS phase with one outstanding
    // transaction, so command and response are accepted together on
    // psel && penable && pready. Pure observation -- nothing registered.
    logic [NUM_MASTERS-1:0] m_xfer;
    logic [NUM_SLAVES-1:0]  s_xfer;
    localparam logic ALWAYS_READY = 1'b1;

    // =============================================================================
    // Master Monitors (3 monitors: M0, M1, M2)
    // =============================================================================

    genvar m;
    generate
        for (m = 0; m < NUM_MASTERS; m++) begin : gen_master_monitors
            apb4_monitor #(
                .ADDR_WIDTH       (ADDR_WIDTH),
                .DATA_WIDTH       (DATA_WIDTH),
                .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
                .UNIT_ID          (UNIT_ID[7:0]),
                .AGENT_ID         (16'(AGENT_ID_M_BASE + m))
            ) u_master_mon (
                .aclk                     (pclk),
                .aresetn                  (presetn),

                .cmd_valid                (m_xfer[m]),
                .cmd_ready                (ALWAYS_READY),
                .cmd_pwrite               (xbar_m_pwrite[m]),
                .cmd_paddr                (xbar_m_paddr[m]),
                .cmd_pwdata               (xbar_m_pwdata[m]),
                .cmd_pstrb                (xbar_m_pstrb[m]),
                .cmd_pprot                (xbar_m_pprot[m]),

                .rsp_valid                (m_xfer[m]),
                .rsp_ready                (ALWAYS_READY),
                .rsp_prdata               (xbar_m_prdata[m]),
                .rsp_pslverr              (xbar_m_pslverr[m]),

                .cfg_error_enable         (cfg_error_enable),
                .cfg_timeout_enable       (cfg_timeout_enable),
                .cfg_protocol_enable      (1'b0),
                .cfg_slverr_enable        (cfg_error_enable),
                .cfg_perf_enable          (cfg_perf_enable),
                .cfg_latency_enable       (1'b0),
                .cfg_throughput_enable    (1'b0),
                .cfg_debug_enable         (1'b0),
                .cfg_trans_debug_enable   (1'b0),
                .cfg_debug_level          (4'd0),
                .cfg_cmd_timeout_cnt      (16'd0),
                .cfg_rsp_timeout_cnt      (16'd0),
                .cfg_latency_threshold    (32'd0),
                .cfg_throughput_threshold (16'd0),

                .cfg_addr_check_enable    (1'b0),
                .cfg_addr_range_enable    ('0),
                .cfg_addr_range_low       ('0),
                .cfg_addr_range_high      ('0),

                .i_mon_time               (mon_time),

                .monbus_valid             (mon_valid[m]),
                .monbus_ready             (mon_ready[m]),
                .monbus_packet            (mon_packet[m]),
                .monbus_timestamp         (),

                .active_count             (),
                .error_count              (),
                .transaction_count        ()
            );
        end
    endgenerate

    // =============================================================================
    // Slave Monitors (4 monitors: S0, S1, S2, S3)
    // =============================================================================

    genvar s;
    generate
        for (s = 0; s < NUM_SLAVES; s++) begin : gen_slave_monitors
            apb4_monitor #(
                .ADDR_WIDTH       (ADDR_WIDTH),
                .DATA_WIDTH       (DATA_WIDTH),
                .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
                .UNIT_ID          (UNIT_ID[7:0]),
                .AGENT_ID         (16'(AGENT_ID_S_BASE + s))
            ) u_slave_mon (
                .aclk                     (pclk),
                .aresetn                  (presetn),

                .cmd_valid                (s_xfer[s]),
                .cmd_ready                (ALWAYS_READY),
                .cmd_pwrite               (xbar_s_pwrite[s]),
                .cmd_paddr                (xbar_s_paddr[s]),
                .cmd_pwdata               (xbar_s_pwdata[s]),
                .cmd_pstrb                (xbar_s_pstrb[s]),
                .cmd_pprot                (xbar_s_pprot[s]),

                .rsp_valid                (s_xfer[s]),
                .rsp_ready                (ALWAYS_READY),
                .rsp_prdata               (xbar_s_prdata[s]),
                .rsp_pslverr              (xbar_s_pslverr[s]),

                .cfg_error_enable         (cfg_error_enable),
                .cfg_timeout_enable       (cfg_timeout_enable),
                .cfg_protocol_enable      (1'b0),
                .cfg_slverr_enable        (cfg_error_enable),
                .cfg_perf_enable          (cfg_perf_enable),
                .cfg_latency_enable       (1'b0),
                .cfg_throughput_enable    (1'b0),
                .cfg_debug_enable         (1'b0),
                .cfg_trans_debug_enable   (1'b0),
                .cfg_debug_level          (4'd0),
                .cfg_cmd_timeout_cnt      (16'd0),
                .cfg_rsp_timeout_cnt      (16'd0),
                .cfg_latency_threshold    (32'd0),
                .cfg_throughput_threshold (16'd0),

                .cfg_addr_check_enable    (1'b0),
                .cfg_addr_range_enable    ('0),
                .cfg_addr_range_low       ('0),
                .cfg_addr_range_high      ('0),

                .i_mon_time               (mon_time),

                .monbus_valid             (mon_valid[NUM_MASTERS + s]),
                .monbus_ready             (mon_ready[NUM_MASTERS + s]),
                .monbus_packet            (mon_packet[NUM_MASTERS + s]),
                .monbus_timestamp         (),

                .active_count             (),
                .error_count              (),
                .transaction_count        ()
            );
        end
    endgenerate

    // =============================================================================
    // Monitor Bus Arbiter (Round-Robin)
    // =============================================================================
    // Aggregates 7 monitor packet streams into single output

    // Tap strobes, one per monitored port
    generate
        for (genvar mi = 0; mi < NUM_MASTERS; mi++) begin : gen_m_xfer
            assign m_xfer[mi] = xbar_m_psel[mi] && xbar_m_penable[mi] && xbar_m_pready[mi];
        end
        for (genvar si = 0; si < NUM_SLAVES; si++) begin : gen_s_xfer
            assign s_xfer[si] = xbar_s_psel[si] && xbar_s_penable[si] && xbar_s_pready[si];
        end
    endgenerate

    // =============================================================================
    // Monitor bus aggregation
    // =============================================================================
    // Round-robin, not priority: a master that errors continuously must not lock
    // the other ports out of the bus, or you lose the evidence explaining it.

    logic [NUM_MONITORS-1:0]         mon_grant;
    logic [$clog2(NUM_MONITORS)-1:0] mon_grant_id;

    arbiter_round_robin #(
        .CLIENTS      (NUM_MONITORS),
        .WAIT_GNT_ACK (0)
    ) u_mon_arbiter (
        .clk         (pclk),
        .rst_n       (presetn),
        .block_arb   (~monbus_ready),
        .request     (mon_valid),
        .grant_ack   ('0),
        .grant_valid (monbus_valid),
        .grant       (mon_grant),
        .grant_id    (mon_grant_id),
        .last_grant  ()
    );

    always_comb begin
        mon_ready = '0;
        mon_ready[mon_grant_id] = monbus_valid && monbus_ready;
    end

    assign monbus_packet = mon_packet[mon_grant_id];

endmodule : apbx_xbar_monitored
