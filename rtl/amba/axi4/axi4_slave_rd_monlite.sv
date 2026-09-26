// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_rd_monlite
// Purpose: AXI4 Slave Read with the lite monitor (axi_monitor_lite) -- axi4_slave_rd plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/axi4/axi4_slave_rd_monlite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axi4_slave_rd_mon (amba/monitor-lite TASK-001). Same
// core, same taps, same 128-bit packets on the same monbus with the same
// UNIT/AGENT ids, so the arbiter, group and host tooling cannot tell the two
// apart. Different interface: only what the lite can honour is on the port
// list -- no perf window, no debug, no address-range checker, no ID/address
// filters, no per-event masks -- and two status outputs the full monitor
// does not have (dropped_count, refused_count). The lite never stalls the
// port: an event it cannot deliver is dropped and counted, and a command
// that finds no free table entry is counted and left untracked (its beats
// then report as ORPHAN errors). There is no block_ready and no gating of
// the command handshake; the core's ready goes straight to the port.
//
// Every core parameter and port is declared here verbatim from axi4_slave_rd
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axi4_slave_rd_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h02,
    parameter logic [15:0] AGENT_ID               = 16'h0014,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi4_slave_rd) ----

    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short params and calculations
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
) (

    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]                s_axi_arid,
    input  logic [AW-1:0]                s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [3:0]                   s_axi_arregion,
    input  logic [UW-1:0]                s_axi_aruser,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,

    // Master AXI Interface (Output Side to memory or backend)
    // Read address channel (AR)
    output logic [IW-1:0]                fub_axi_arid,
    output logic [AW-1:0]                fub_axi_araddr,
    output logic [7:0]                   fub_axi_arlen,
    output logic [2:0]                   fub_axi_arsize,
    output logic [1:0]                   fub_axi_arburst,
    output logic                         fub_axi_arlock,
    output logic [3:0]                   fub_axi_arcache,
    output logic [2:0]                   fub_axi_arprot,
    output logic [3:0]                   fub_axi_arqos,
    output logic [3:0]                   fub_axi_arregion,
    output logic [UW-1:0]                fub_axi_aruser,
    output logic                         fub_axi_arvalid,
    input  logic                         fub_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,

    // Status outputs for clock gating
    output logic                         busy,

    // ---- Monitor control (the lite's own set: nothing here it cannot honour) ----
    input  logic                                  cam_clear,           // sync clear of the monitor's table (named as on the _mon wrapper: pin-compatible)
    input  logic                                  cfg_monitor_enable,  // 0 = monitor inert, table held clear
    input  logic                                  cfg_error_enable,
    input  logic                                  cfg_timeout_enable,
    input  logic                                  cfg_compl_enable,
    input  logic                                  cfg_threshold_enable,
    input  logic [15:0]                           cfg_timeout_cycles,  // MICROSECONDS of no progress; 0 = never
    input  logic [3:0]                            cfg_freq_sel,        // counter_freq_invariant LUT index
    input  logic [15:0]                           cfg_axi_pkt_mask,    // drop mask by packet type
    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Monitor bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,
    // ---- Status ----
    output logic [7:0]                            active_transactions, // entries in the table
    output logic [15:0]                           error_count,         // error + timeout packets emitted
    output logic [31:0]                           transaction_count,   // completion packets emitted
    output logic [15:0]                           dropped_count,       // events lost to monbus backpressure since the last report
    output logic [15:0]                           refused_count        // commands that found no free table entry
);

    // ------------------------------------------------------------------------
    // The core, passed through untouched (no monitor gating on any handshake)
    // ------------------------------------------------------------------------
    axi4_slave_rd #(
        .SKID_DEPTH_AR               (SKID_DEPTH_AR),
        .SKID_DEPTH_R                (SKID_DEPTH_R),
        .AXI_ID_WIDTH                (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH              (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH              (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH              (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH             (AXI_WSTRB_WIDTH),
        .AW                          (AW),
        .DW                          (DW),
        .IW                          (IW),
        .SW                          (SW),
        .UW                          (UW),
        .ARSize                      (ARSize),
        .RSize                       (RSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .s_axi_arid                  (s_axi_arid),
        .s_axi_araddr                (s_axi_araddr),
        .s_axi_arlen                 (s_axi_arlen),
        .s_axi_arsize                (s_axi_arsize),
        .s_axi_arburst               (s_axi_arburst),
        .s_axi_arlock                (s_axi_arlock),
        .s_axi_arcache               (s_axi_arcache),
        .s_axi_arprot                (s_axi_arprot),
        .s_axi_arqos                 (s_axi_arqos),
        .s_axi_arregion              (s_axi_arregion),
        .s_axi_aruser                (s_axi_aruser),
        .s_axi_arvalid               (s_axi_arvalid),
        .s_axi_arready               (s_axi_arready),
        .s_axi_rid                   (s_axi_rid),
        .s_axi_rdata                 (s_axi_rdata),
        .s_axi_rresp                 (s_axi_rresp),
        .s_axi_rlast                 (s_axi_rlast),
        .s_axi_ruser                 (s_axi_ruser),
        .s_axi_rvalid                (s_axi_rvalid),
        .s_axi_rready                (s_axi_rready),
        .fub_axi_arid                (fub_axi_arid),
        .fub_axi_araddr              (fub_axi_araddr),
        .fub_axi_arlen               (fub_axi_arlen),
        .fub_axi_arsize              (fub_axi_arsize),
        .fub_axi_arburst             (fub_axi_arburst),
        .fub_axi_arlock              (fub_axi_arlock),
        .fub_axi_arcache             (fub_axi_arcache),
        .fub_axi_arprot              (fub_axi_arprot),
        .fub_axi_arqos               (fub_axi_arqos),
        .fub_axi_arregion            (fub_axi_arregion),
        .fub_axi_aruser              (fub_axi_aruser),
        .fub_axi_arvalid             (fub_axi_arvalid),
        .fub_axi_arready             (fub_axi_arready),
        .fub_axi_rid                 (fub_axi_rid),
        .fub_axi_rdata               (fub_axi_rdata),
        .fub_axi_rresp               (fub_axi_rresp),
        .fub_axi_rlast               (fub_axi_rlast),
        .fub_axi_ruser               (fub_axi_ruser),
        .fub_axi_rvalid              (fub_axi_rvalid),
        .fub_axi_rready              (fub_axi_rready),
        .busy                        (busy)
    );

    // ------------------------------------------------------------------------
    // Monitor taps. cfg_monitor_enable gates every tap and holds the table
    // clear; cfg_timeout_cycles is MICROSECONDS at full width, 0 = never.
    // ------------------------------------------------------------------------
    logic        w_mon_cmd_valid;
    logic        w_mon_data_valid;
    logic        w_mon_resp_valid;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;
    assign w_mon_cmd_valid  = s_axi_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = s_axi_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = (s_axi_rvalid && s_axi_rlast) & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axi_monitor_lite #(
        .UNIT_ID (UNIT_ID),
        .AGENT_ID (AGENT_ID),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .OUT_DEPTH (OUT_DEPTH),
        .ADDR_WIDTH (AW),
        .ID_WIDTH (IW),
        .IS_READ (1'b1),
        .IS_AXI (1'b1),
        .CFI_MIN_FREQ_MHZ (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk (aclk),
        .aresetn (aresetn),
        .clear (cam_clear | ~cfg_monitor_enable),
        .i_mon_time (i_mon_time),
        .cmd_addr (s_axi_araddr),
        .cmd_id (s_axi_arid),
        .cmd_len (s_axi_arlen),
        .cmd_valid (w_mon_cmd_valid),
        .cmd_ready (s_axi_arready),
        .data_id (s_axi_rid),
        .data_last (s_axi_rlast),
        .data_resp (s_axi_rresp),
        .data_valid (w_mon_data_valid),
        .data_ready (s_axi_rready),
        .resp_id (s_axi_rid),
        .resp_code (s_axi_rresp),
        .resp_valid (w_mon_resp_valid),
        .resp_ready (s_axi_rready),
        .cfg_freq_sel (cfg_freq_sel),
        .cfg_timeout_cnt (w_timeout_cnt),
        .cfg_error_enable (cfg_error_enable),
        .cfg_compl_enable (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_threshold_enable (cfg_threshold_enable),
        .cfg_active_trans_threshold (16'(ACTIVE_TRANS_THRESHOLD)),
        .cfg_axi_pkt_mask (cfg_axi_pkt_mask),
        .monbus_valid (monbus_valid),
        .monbus_ready (monbus_ready),
        .monbus_packet (monbus_packet),
        .monbus_timestamp (monbus_timestamp),
        .active_count (active_transactions),
        /* verilator lint_off PINCONNECTEMPTY */
        .busy (),
        .dropped_count (dropped_count),
        .refused_count (refused_count),
        /* verilator lint_on PINCONNECTEMPTY */
        .perf_completed_count (w_perf_completed_count),
        .perf_error_count           (w_perf_error_count)
        );
    end else begin : gen_no_monitor
        assign monbus_valid           = 1'b0;
        assign monbus_packet          = '0;
        assign monbus_timestamp       = '0;
        assign active_transactions    = 8'h0;
        assign dropped_count          = 16'h0;
        assign refused_count          = 16'h0;
        assign w_perf_completed_count = 16'h0;
        assign w_perf_error_count     = 16'h0;
    end

    // error_count covers error+timeout packets, transaction_count completion
    // packets -- what the lite actually EMITTED, as on the _mon wrapper.
    assign error_count       = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

endmodule : axi4_slave_rd_monlite
