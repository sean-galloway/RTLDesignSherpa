// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_axil_group
// Purpose: Monbus Axil Group module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/*
================================================================================
Monitor Bus AXI-Lite Group  (shared AMBA building block)
================================================================================
Single monbus input -- consumers that need N-way arbitration (RAPIDS source +
sink, the bridge's per-port wrappers) instantiate a separate monbus_arbiter
upstream and feed this group with the merged stream. That keeps arbitration
and capture as orthogonal concerns and means this module never has to
duplicate the arbiter for each consumer's input count.

This module receives a single monbus stream,
applies configurable filtering based on protocol and packet types, and
routes filtered packets to either:
- Error/Interrupt FIFO (slave read interface) - generates interrupt when not empty
- Master Write FIFO - writes to configurable address range

Features:
- Single monitor bus input (no arbitration needed)
- Per-protocol configurable packet filtering (drop, error/interrupt, master write)
- Separate FIFOs for error/interrupt vs master write paths
- Configurable address range for master write operations
- Protocol support: AXI, AXIS, CORE (3 protocols)
- Built-in AXI-Lite skid buffering for timing closure

Packet width is locked at 128 bits via monitor_common_pkg::MONBUS_PKT_WIDTH.
Side-band timestamp width is locked at 64 bits via monitor_common_pkg::MONBUS_TS_WIDTH.

Timestamping:
- Free-running 64-bit counter inside the group is driven OUT on mon_time_out
  to every wrapper's i_mon_time input. The group is the single timestamp
  authority for the whole monitor subsystem.
- Wrappers sample on emission and return that timestamp on the
  monbus_timestamp side-band, which arrives here paired with the packet.
- Both FIFOs (err and write) store the same 192-bit record:
  {packet[127:0], source_ts[63:0]}. The m_axil master write FSM and the
  s_axil slave read drain both emit/consume that record as exactly three
  64-bit beats, with the timestamp beat leading and carrying a 4-bit
  encoding tag in its top 4 bits:
    beat 0 = {tag[3:0], source_ts[59:0]}
             tag = 4'h0  raw 3-beat record (no compression, this writer)
             tag = 4'h1  reserved -- future Tier-1 compression format A
             tag = 4'h2  reserved -- future Tier-1 compression format B
             tag = 4'h3  reserved -- future Tier-1 compression format C
             tag = 4'h4-4'hF  reserved for future use
             The current writer hardwires tag = 4'h0; an optional
             compressor block in front of this writer can populate the
             other codes without changing the wire format.
    beat 1 = packet[127:64]
    beat 2 = packet[63:0]
  Putting the tag-bearing beat first lets a decoder read one 64-bit
  word, look at the top 4 bits, and immediately know the record length
  and format without lookahead. The 60-bit truncated timestamp wraps at
  2^60 cycles (~117 days at 100 MHz, plenty for any capture window).
- The variable-size append-mode used in earlier revisions (16/24/32-byte
  records selected by cfg_ts_append_enable / cfg_ts_append_mode) is GONE.
  The endpoints (parser, host dump scripts) treat the timestamp as an
  opaque ordering key -- they do not care where it originates -- which
  leaves room for a future hybrid scheme (global us counter + local
  per-wrapper resolution) without touching the transport. See the
  monitor system whitepaper stub for the design space.

Configuration Registers (per protocol):
- pkt_mask[15:0]     - Drop packets when bit[pkt_type] = 1
- err_select[15:0]   - Route to error FIFO when bit[pkt_type] = 1
- Individual event masks for each packet type (16 bits each)

================================================================================
*/

`include "reset_defs.svh"

module monbus_axil_group
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR     = 64,   // Error/interrupt FIFO depth
    parameter int FIFO_DEPTH_WRITE   = 32,   // Master write FIFO depth
    parameter int ADDR_WIDTH         = 32,   // AXI address width
    parameter int S_AXIL_DATA_WIDTH  = 64,   // Slave AXI-Lite data width (CPU read)
                                             // Locked at 64: drains a {packet,
                                             // source_ts} record in 3 beats.
    parameter int M_AXIL_DATA_WIDTH  = 64,   // Master AXI-Lite data width (capture writes)
    parameter int NUM_PROTOCOLS      = 3,    // AXI, AXIS, CORE
    // Bulk-trace compressor select (off by default for back-compat).
    //   0: raw 3-beat-per-record writer (existing behaviour, tag=4'h0)
    //   1: monbus_compressor sits in front of the writer; the writer
    //      becomes a per-slot 1-beat AXIL emitter and each beat carries
    //      its own 4-bit format tag in bits [63:60]. Stat counters are
    //      exposed via mon_compressor_stat_*.
    parameter int USE_COMPRESSION    = 0
) (
    // Clock and Reset
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    // Monitor Bus Input (single input - STREAM is memory-to-memory only)
    input  logic                          monbus_valid,
    output logic                          monbus_ready,
    input  monitor_packet_t               monbus_packet,
    input  monbus_timestamp_t             monbus_timestamp,

    // Free-running monitor-time output (drive to every wrapper's i_mon_time)
    output monbus_timestamp_t             mon_time_out,

    // Error/Interrupt FIFO (Slave Read Interface) — 32-bit CPU reads
    input  logic                          s_axil_arvalid,
    output logic                          s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]         s_axil_araddr,
    input  logic [2:0]                    s_axil_arprot,

    output logic                          s_axil_rvalid,
    input  logic                          s_axil_rready,
    output logic [S_AXIL_DATA_WIDTH-1:0]  s_axil_rdata,
    output logic [1:0]                    s_axil_rresp,

    // Master Write Interface — 64-bit captures
    output logic                          m_axil_awvalid,
    input  logic                          m_axil_awready,
    output logic [ADDR_WIDTH-1:0]         m_axil_awaddr,
    output logic [2:0]                    m_axil_awprot,

    output logic                          m_axil_wvalid,
    input  logic                          m_axil_wready,
    output logic [M_AXIL_DATA_WIDTH-1:0]  m_axil_wdata,
    output logic [M_AXIL_DATA_WIDTH/8-1:0] m_axil_wstrb,

    input  logic                          m_axil_bvalid,
    output logic                          m_axil_bready,
    input  logic [1:0]                    m_axil_bresp,

    // Interrupt Output (renamed from 'interrupt' to avoid C++ keyword)
    output logic                          irq_out,

    // Configuration Interface (simplified - could be expanded to full AXI-Lite)
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,       // Base address for master writes
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,      // Limit address for master writes

    // Protocol Configuration - AXI (protocol 0)
    input  logic [15:0]                   cfg_axi_pkt_mask,     // Drop mask for packet types
    input  logic [15:0]                   cfg_axi_err_select,   // Error FIFO select for packet types
    input  logic [15:0]                   cfg_axi_error_mask,   // Individual error event mask
    input  logic [15:0]                   cfg_axi_timeout_mask, // Individual timeout event mask
    input  logic [15:0]                   cfg_axi_compl_mask,   // Individual completion event mask
    input  logic [15:0]                   cfg_axi_thresh_mask,  // Individual threshold event mask
    input  logic [15:0]                   cfg_axi_perf_mask,    // Individual performance event mask
    input  logic [15:0]                   cfg_axi_addr_mask,    // Individual address match event mask
    input  logic [15:0]                   cfg_axi_debug_mask,   // Individual debug event mask

    // Protocol Configuration - AXIS (protocol 1)
    input  logic [15:0]                   cfg_axis_pkt_mask,
    input  logic [15:0]                   cfg_axis_err_select,
    input  logic [15:0]                   cfg_axis_error_mask,
    input  logic [15:0]                   cfg_axis_timeout_mask,
    input  logic [15:0]                   cfg_axis_compl_mask,
    input  logic [15:0]                   cfg_axis_credit_mask,
    input  logic [15:0]                   cfg_axis_channel_mask,
    input  logic [15:0]                   cfg_axis_stream_mask,

    // Protocol Configuration - CORE (protocol 4 — PROTOCOL_CORE)
    input  logic [15:0]                   cfg_core_pkt_mask,
    input  logic [15:0]                   cfg_core_err_select,
    input  logic [15:0]                   cfg_core_error_mask,
    input  logic [15:0]                   cfg_core_timeout_mask,
    input  logic [15:0]                   cfg_core_compl_mask,
    input  logic [15:0]                   cfg_core_thresh_mask,
    input  logic [15:0]                   cfg_core_perf_mask,
    input  logic [15:0]                   cfg_core_debug_mask,

    // Debug/Status
    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [7:0]                    err_fifo_count,
    output logic [7:0]                    write_fifo_count,

    // Compressor statistics (valid only when USE_COMPRESSION == 1;
    // tied to 0 in the raw-writer build so the wrapper layer sees
    // consistent ports regardless of build option).
    output logic [31:0]                   mon_compressor_stat_tier1_a,
    output logic [31:0]                   mon_compressor_stat_tier1_b,
    output logic [31:0]                   mon_compressor_stat_tier1_c,
    output logic [31:0]                   mon_compressor_stat_tier0,
    output logic [31:0]                   mon_compressor_stat_cam_miss,
    output logic [31:0]                   mon_compressor_stat_delta_ts_ovf,
    output logic [31:0]                   mon_compressor_stat_event_data_ovf,
    output logic [31:0]                   mon_compressor_stat_ed_delta_ovf
);

    // =======================================================================
    // Local Parameters
    // =======================================================================

    localparam int ERR_FIFO_ADDR_WIDTH   = $clog2(FIFO_DEPTH_ERR);
    localparam int WRITE_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_WRITE);

    // Both FIFOs store the same 192-bit record: {source_ts, packet}.
    // s_axil drains in three 64-bit beats (slice 0: {tag[3:0],
    // source_ts[59:0]}; slice 1: packet[127:64]; slice 2: packet[63:0]);
    // the m_axil writer emits the same three beats in the same order to
    // memory. Putting the timestamp slice first reserves the top 4 bits
    // for a future on-the-wire compression tag without changing FIFO
    // contents (FIFO still holds raw 192-bit records; tag is asserted
    // by the writer/drainer as a constant 4'h0 today).
    localparam int FIFO_REC_WIDTH       = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;
    localparam int ERR_FIFO_REC_WIDTH   = FIFO_REC_WIDTH;
    localparam int WRITE_REC_WIDTH      = FIFO_REC_WIDTH;

    // =======================================================================
    // Internal Signals
    // =======================================================================

    // Input monitor bus (no arbitration - single input)
    logic                            input_monbus_valid;
    logic                            input_monbus_ready;
    monitor_packet_t                 input_monbus_packet;
    monbus_timestamp_t               input_monbus_source_ts;

    // Packet analysis
    logic [3:0]                      pkt_type;
    logic [3:0]                      pkt_protocol;
    logic [7:0]                      pkt_event_code;
    logic [3:0]                      ec_idx;       // event-code index into 16-bit masks
    logic                            ec_in_mask_range;
    logic [63:0]                     pkt_event_data;

    // Filter decisions
    logic                            pkt_drop;
    logic                            pkt_to_err_fifo;
    logic                            pkt_to_write_fifo;
    logic                            pkt_event_masked;

    // Free-running timestamp counter (this module is the counter authority)
    monbus_timestamp_t               r_ts_counter;

    // Error FIFO signals -- carries {source_ts, packet} per entry so the
    // CPU IRQ handler reading via s_axil gets the source timestamp
    // alongside the packet body without going to the SRAM dump path.
    logic                            err_fifo_wr_valid;
    logic                            err_fifo_wr_ready;
    logic [ERR_FIFO_REC_WIDTH-1:0]   err_fifo_wr_data;
    logic                            err_fifo_rd_valid;
    logic                            err_fifo_rd_ready;
    logic [ERR_FIFO_REC_WIDTH-1:0]   err_fifo_rd_data;
    logic                            err_fifo_empty;
    logic [ERR_FIFO_ADDR_WIDTH:0]    err_fifo_count_full;

    // Write FIFO signals (carries combined record)
    logic                            write_fifo_wr_valid;
    logic                            write_fifo_wr_ready;
    logic [WRITE_REC_WIDTH-1:0]      write_fifo_wr_data;
    logic                            write_fifo_rd_valid;
    logic                            write_fifo_rd_ready;
    logic [WRITE_REC_WIDTH-1:0]      write_fifo_rd_data;
    logic                            write_fifo_empty;
    logic [WRITE_FIFO_ADDR_WIDTH:0]  write_fifo_count_full;

    // Unpacked record at FIFO output
    monitor_packet_t                 wr_rec_packet;
    monbus_timestamp_t               wr_rec_source_ts;

    // Backend interfaces for AXI-Lite slave read (32-bit CPU side)
    logic [ADDR_WIDTH-1:0]           fub_rd_araddr;
    logic [2:0]                      fub_rd_arprot;
    logic                            fub_rd_arvalid;
    logic                            fub_rd_arready;
    logic [S_AXIL_DATA_WIDTH-1:0]    fub_rd_rdata;
    logic [1:0]                      fub_rd_rresp;
    logic                            fub_rd_rvalid;
    logic                            fub_rd_rready;

    // Backend interfaces for AXI-Lite master write (64-bit capture side)
    logic [ADDR_WIDTH-1:0]            fub_wr_awaddr;
    logic [2:0]                       fub_wr_awprot;
    logic                             fub_wr_awvalid;
    logic                             fub_wr_awready;
    logic [M_AXIL_DATA_WIDTH-1:0]     fub_wr_wdata;
    logic [M_AXIL_DATA_WIDTH/8-1:0]   fub_wr_wstrb;
    logic                             fub_wr_wvalid;
    logic                             fub_wr_wready;
    logic [1:0]                       fub_wr_bresp;
    logic                             fub_wr_bvalid;
    logic                             fub_wr_bready;

    // Address generation for master writes
    logic [ADDR_WIDTH-1:0]            current_write_addr;

    // =======================================================================
    // Free-running Timestamp Counter
    // =======================================================================

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_ts_counter <= '0;
        end else begin
            r_ts_counter <= r_ts_counter + 1'b1;
        end
    )

    assign mon_time_out = r_ts_counter;

    // =======================================================================
    // Monitor Bus Input (No Arbitration Needed - Single Input)
    // =======================================================================

    // Direct connection - no arbitration needed for single input
    assign input_monbus_valid     = monbus_valid;
    assign monbus_ready           = input_monbus_ready;
    assign input_monbus_packet    = monbus_packet;
    assign input_monbus_source_ts = monbus_timestamp;

    // =======================================================================
    // Packet Analysis and Filtering
    // =======================================================================

    // Extract packet fields (new 128-bit layout)
    assign pkt_type       = get_packet_type(input_monbus_packet);
    assign pkt_protocol   = input_monbus_packet[108:105]; // 4-bit protocol field
    assign pkt_event_code = get_event_code(input_monbus_packet);
    assign pkt_event_data = get_event_data(input_monbus_packet);

    // Event-code is now 8 bits but the per-event mask registers stayed 16 bits
    // for backward-compat with the existing register map. Index with the low
    // nibble; codes >= 16 are treated as "not in mask" (no event masking).
    assign ec_idx           = pkt_event_code[3:0];
    assign ec_in_mask_range = (pkt_event_code[7:4] == 4'h0);

    // Filter logic. Protocols are NOT contiguous (AXI=0, AXIS=1, APB=2, ARB=3,
    // CORE=4) so we don't gate on `< NUM_PROTOCOLS` — the case statement's
    // default branch drops anything we don't have config registers for.
    // NUM_PROTOCOLS is kept as a parameter for backward-compat but is now
    // informational only.
    /* verilator lint_off UNUSEDPARAM */
    // (NUM_PROTOCOLS retained for API stability)
    /* verilator lint_on UNUSEDPARAM */
    always_comb begin
        pkt_drop          = 1'b0;
        pkt_to_err_fifo   = 1'b0;
        pkt_to_write_fifo = 1'b0;
        pkt_event_masked  = 1'b0;

        if (input_monbus_valid) begin
            // Protocol-specific filtering. Use the package enum values
            // (PROTOCOL_AXI=0, PROTOCOL_AXIS=1, PROTOCOL_CORE=4).
            case (pkt_protocol)
                PROTOCOL_AXI: begin // AXI
                    pkt_drop        = cfg_axi_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;

                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_axi_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_axi_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask  [ec_idx];
                            PktTypeThreshold:  pkt_event_masked = cfg_axi_thresh_mask [ec_idx];
                            PktTypePerf:       pkt_event_masked = cfg_axi_perf_mask   [ec_idx];
                            PktTypeAddrMatch:  pkt_event_masked = cfg_axi_addr_mask   [ec_idx];
                            PktTypeDebug:      pkt_event_masked = cfg_axi_debug_mask  [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end

                PROTOCOL_AXIS: begin // AXIS (AXI4-Stream)
                    pkt_drop        = cfg_axis_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_axis_err_select[pkt_type] && !pkt_drop;

                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_axis_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_axis_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_axis_compl_mask  [ec_idx];
                            PktTypeCredit:     pkt_event_masked = cfg_axis_credit_mask [ec_idx];
                            PktTypeChannel:    pkt_event_masked = cfg_axis_channel_mask[ec_idx];
                            PktTypeStream:     pkt_event_masked = cfg_axis_stream_mask [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end

                PROTOCOL_CORE: begin // CORE
                    pkt_drop        = cfg_core_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_core_err_select[pkt_type] && !pkt_drop;

                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_core_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_core_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_core_compl_mask  [ec_idx];
                            PktTypeThreshold:  pkt_event_masked = cfg_core_thresh_mask [ec_idx];
                            PktTypePerf:       pkt_event_masked = cfg_core_perf_mask   [ec_idx];
                            PktTypeDebug:      pkt_event_masked = cfg_core_debug_mask  [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end

                default: begin
                    pkt_drop = 1'b1; // Drop unsupported protocols (APB, ARB, etc.)
                end
            endcase

            // Final decision - apply event masking
            if (pkt_event_masked) begin
                pkt_drop        = 1'b1;
                pkt_to_err_fifo = 1'b0;
            end

            // Packets go to write FIFO if not dropped and not going to error FIFO
            pkt_to_write_fifo = !pkt_drop && !pkt_to_err_fifo;
        end
    end

    // Input ready based on FIFO availability
    assign input_monbus_ready = pkt_drop ||
                                (pkt_to_err_fifo   && err_fifo_wr_ready) ||
                                (pkt_to_write_fifo && write_fifo_wr_ready);

    // =======================================================================
    // Error/Interrupt FIFO (packet-only, no timestamps)
    // =======================================================================

    assign err_fifo_wr_valid = input_monbus_valid && pkt_to_err_fifo && !pkt_drop;
    // Pack: {source_ts[63:0], packet[127:0]}. source_ts arrives paired
    // with the packet on the monbus_timestamp side-band; captured on the
    // same input handshake that fills the FIFO entry.
    assign err_fifo_wr_data  = {input_monbus_source_ts, input_monbus_packet};

    gaxi_fifo_sync #(
        .REGISTERED     (0),
        .DATA_WIDTH     (ERR_FIFO_REC_WIDTH),
        .DEPTH          (FIFO_DEPTH_ERR)
    ) u_err_fifo (
        .axi_aclk       (axi_aclk),
        .axi_aresetn    (axi_aresetn),
        .wr_valid       (err_fifo_wr_valid),
        .wr_ready       (err_fifo_wr_ready),
        .wr_data        (err_fifo_wr_data),
        .rd_valid       (err_fifo_rd_valid),
        .rd_ready       (err_fifo_rd_ready),
        .rd_data        (err_fifo_rd_data),
        .count          (err_fifo_count_full)
    );

    assign err_fifo_empty = !err_fifo_rd_valid;
    assign err_fifo_full  = !err_fifo_wr_ready;
    assign irq_out        = !err_fifo_empty; // Interrupt when FIFO not empty
    // Zero-extend FIFO count to 8 bits
    assign err_fifo_count = {{(8-ERR_FIFO_ADDR_WIDTH-1){1'b0}}, err_fifo_count_full};

    // =======================================================================
    // Master Write FIFO (record: packet + source_ts -- same as err FIFO)
    // =======================================================================

    assign write_fifo_wr_valid = input_monbus_valid && pkt_to_write_fifo && !pkt_drop;
    // Pack: {source_ts[63:0], packet[127:0]} -- mirrors err_fifo_wr_data so
    // both FIFOs feed the m_axil writer / s_axil drainer with an identical
    // 3-beat layout: slice 0 = {tag[3:0], source_ts[59:0]}, slice 1 =
    // packet[127:64], slice 2 = packet[63:0]. The tag is asserted by the
    // writer/drainer (4'h0 today, reserved for future compression).
    assign write_fifo_wr_data  = {input_monbus_source_ts, input_monbus_packet};

    gaxi_fifo_sync #(
        .REGISTERED     (0),
        .DATA_WIDTH     (WRITE_REC_WIDTH),
        .DEPTH          (FIFO_DEPTH_WRITE)
    ) u_write_fifo (
        .axi_aclk       (axi_aclk),
        .axi_aresetn    (axi_aresetn),
        .wr_valid       (write_fifo_wr_valid),
        .wr_ready       (write_fifo_wr_ready),
        .wr_data        (write_fifo_wr_data),
        .rd_valid       (write_fifo_rd_valid),
        .rd_ready       (write_fifo_rd_ready),
        .rd_data        (write_fifo_rd_data),
        .count          (write_fifo_count_full)
    );

    // Unpack record at FIFO output (matches the err FIFO layout)
    assign wr_rec_packet    = write_fifo_rd_data[MONBUS_PKT_WIDTH-1:0];
    assign wr_rec_source_ts = write_fifo_rd_data[WRITE_REC_WIDTH-1:MONBUS_PKT_WIDTH];

    assign write_fifo_empty = !write_fifo_rd_valid;
    assign write_fifo_full  = !write_fifo_wr_ready;
    assign write_fifo_count = {{(8-WRITE_FIFO_ADDR_WIDTH-1){1'b0}}, write_fifo_count_full};

    // =======================================================================
    // AXI-Lite Slave Read Interface (Error/Interrupt FIFO Access, 32-bit)
    // =======================================================================

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (S_AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR   (2),
        .SKID_DEPTH_R    (4)
    ) u_slave_rd (
        .aclk            (axi_aclk),
        .aresetn         (axi_aresetn),

        // Slave AXI-Lite Interface (External)
        .s_axil_araddr   (s_axil_araddr),
        .s_axil_arprot   (s_axil_arprot),
        .s_axil_arvalid  (s_axil_arvalid),
        .s_axil_arready  (s_axil_arready),
        .s_axil_rdata    (s_axil_rdata),
        .s_axil_rresp    (s_axil_rresp),
        .s_axil_rvalid   (s_axil_rvalid),
        .s_axil_rready   (s_axil_rready),

        // Backend Interface (to FIFO)
        .fub_araddr      (fub_rd_araddr),
        .fub_arprot      (fub_rd_arprot),
        .fub_arvalid     (fub_rd_arvalid),
        .fub_arready     (fub_rd_arready),
        .fub_rdata       (fub_rd_rdata),
        .fub_rresp       (fub_rd_rresp),
        .fub_rvalid      (fub_rd_rvalid),
        .fub_rready      (fub_rd_rready),

        .busy            () // Unused
    );

    // ---------------------------------------------------------------
    // 192-bit err_fifo record drained over 3 × 64-bit CPU beats.
    //
    // An internal slice counter (r_slice_idx) tracks which 64-bit chunk
    // of the current head-of-FIFO entry the next read should return.
    // The slice order mirrors the m_axil bulk-writer:
    //   slice 0: {tag[3:0], source_ts[59:0]}   tag = 4'h0 (raw, no compression)
    //   slice 1: packet[127:64]
    //   slice 2: packet[63:0]
    // The slice counter advances on each successful read; the FIFO entry
    // is popped only when the third slice fires. The CPU therefore
    // drains one packet by issuing three reads in a row -- the read
    // address is ignored for slice selection so reads can target the
    // same offset or different offsets, the slicer doesn't care.
    //
    // The top 4 bits of slice 0 reserve space for a future on-the-wire
    // compression encoding (see file header). Today the s_axil drain
    // always emits tag = 4'h0 because the FIFO holds raw 192-bit
    // records; a future compressor that lives upstream of both FIFOs
    // would change this.
    //
    // arready stalls while the FIFO is empty (no entry to slice).
    // Once a drain is in progress (r_slice_idx != 0) the head entry
    // stays put until the wrap, so the CPU can pause between beats
    // without losing the in-flight packet.
    // ---------------------------------------------------------------
    // Slice ordering: source_ts (with tag) first, then packet high, then
    // packet low. Matches the m_axil bulk-writer beat order so a host
    // walking the SRAM ring and a CPU IRQ handler get identical records.
    typedef enum logic [1:0] {
        SLICE_SRC_TS = 2'd0,
        SLICE_PKT_HI = 2'd1,
        SLICE_PKT_LO = 2'd2,
        SLICE_RSVD   = 2'd3
    } read_slice_t;

    read_slice_t r_slice_idx;

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_slice_idx <= SLICE_SRC_TS;
        end else if (fub_rd_rvalid && fub_rd_rready) begin
            r_slice_idx <= (r_slice_idx == SLICE_PKT_LO)
                           ? SLICE_SRC_TS
                           : read_slice_t'(r_slice_idx + 2'd1);
        end
    )

    assign fub_rd_arready    = !err_fifo_empty;
    assign fub_rd_rvalid     = fub_rd_arvalid && fub_rd_arready;
    // Pop only when the third slice (packet low) is read -- the FIFO
    // advances every 3 reads, not every read.
    assign err_fifo_rd_ready = fub_rd_rvalid && fub_rd_rready
                            && (r_slice_idx == SLICE_PKT_LO);

    // Tag hardwired to 4'h0 for the raw (uncompressed) record format.
    // Matches the m_axil bulk-writer WRITE_TAG_RAW constant.
    localparam logic [3:0] READ_TAG_RAW = 4'h0;
    always_comb begin
        fub_rd_rdata = {S_AXIL_DATA_WIDTH{1'b0}};
        if (!err_fifo_empty) begin
            unique case (r_slice_idx)
                SLICE_SRC_TS: fub_rd_rdata = {READ_TAG_RAW,
                                              err_fifo_rd_data[MONBUS_PKT_WIDTH+59:MONBUS_PKT_WIDTH]};
                SLICE_PKT_HI: fub_rd_rdata = err_fifo_rd_data[MONBUS_PKT_WIDTH-1:64];
                SLICE_PKT_LO: fub_rd_rdata = err_fifo_rd_data[63:0];
                default:      fub_rd_rdata = '0;
            endcase
        end
    end
    assign fub_rd_rresp = 2'b00; // OKAY response

    // =======================================================================
    // AXI-Lite Master Write Interface (64-bit captures)
    // =======================================================================

    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (M_AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW   (2),
        .SKID_DEPTH_W    (2),
        .SKID_DEPTH_B    (2)
    ) u_master_wr (
        .aclk            (axi_aclk),
        .aresetn         (axi_aresetn),

        // Backend Interface (from FIFO)
        .fub_awaddr      (fub_wr_awaddr),
        .fub_awprot      (fub_wr_awprot),
        .fub_awvalid     (fub_wr_awvalid),
        .fub_awready     (fub_wr_awready),
        .fub_wdata       (fub_wr_wdata),
        .fub_wstrb       (fub_wr_wstrb),
        .fub_wvalid      (fub_wr_wvalid),
        .fub_wready      (fub_wr_wready),
        .fub_bresp       (fub_wr_bresp),
        .fub_bvalid      (fub_wr_bvalid),
        .fub_bready      (fub_wr_bready),

        // Master AXI-Lite Interface (External)
        .m_axil_awaddr   (m_axil_awaddr),
        .m_axil_awprot   (m_axil_awprot),
        .m_axil_awvalid  (m_axil_awvalid),
        .m_axil_awready  (m_axil_awready),
        .m_axil_wdata    (m_axil_wdata),
        .m_axil_wstrb    (m_axil_wstrb),
        .m_axil_wvalid   (m_axil_wvalid),
        .m_axil_wready   (m_axil_wready),
        .m_axil_bresp    (m_axil_bresp),
        .m_axil_bvalid   (m_axil_bvalid),
        .m_axil_bready   (m_axil_bready),

        .busy            () // Unused
    );

    // =======================================================================
    // Write Path -- selected at elaboration via USE_COMPRESSION
    //
    //   USE_COMPRESSION == 0 (default): raw 3-beat-per-record writer.
    //     Beat order per record (+8 bytes per beat, 24 B/record):
    //       beat 0 = {tag=4'h0, source_ts[59:0]}
    //       beat 1 = packet[127:64]
    //       beat 2 = packet[63:0]
    //     Identical to the s_axil drain slice order.
    //
    //   USE_COMPRESSION == 1: bulk-trace compressor (monbus_compressor)
    //     consumes raw records and emits 64-bit slots; the writer below
    //     becomes a per-slot 1-beat AXIL emitter (+8 bytes per slot).
    //     Each slot carries its own 4-bit format tag in bits [63:60]
    //     (4'h0 = RAW expansion beat, 4'h1/4'h2/4'h3 = Tier-1 formats),
    //     so a host walking the SRAM ring can decode one slot at a time
    //     without lookahead. The compressor's CAM lives upstream of this
    //     writer, so the wire framing here stays trivial.
    //
    // Address-window wrap (both modes):
    //   The cfg_base_addr / cfg_limit_addr window is treated as a
    //   record-aligned ring. We compute a "next-record-fits" check at
    //   the *start* of each transaction (record in raw mode, slot in
    //   compressed mode) and rewind to base before issuing the first AW
    //   if it would not fit. Mid-record/mid-burst wrap is forbidden --
    //   that would corrupt the layout in memory.
    // =======================================================================

    generate
    if (USE_COMPRESSION == 0) begin : gen_writer_raw

        // -----------------------------------------------------------------
        // Raw 3-beat-per-record writer (legacy behaviour).
        // -----------------------------------------------------------------
        typedef enum logic [2:0] {
            WRITE_IDLE   = 3'd0,
            WRITE_LOAD   = 3'd1,  // 1 cycle: latch record from FIFO, maybe wrap addr
            WRITE_AW     = 3'd2,
            WRITE_W      = 3'd3,
            WRITE_B      = 3'd4
        } write_state_t;

        // 1-beat addr stride in bytes (8 for a 64-bit master).
        localparam int  BEAT_STRIDE_INT = M_AXIL_DATA_WIDTH / 8;
        // Total bytes per record: 3 * 8 = 24.
        localparam int  REC_SIZE_INT    = 3 * BEAT_STRIDE_INT;
        // Tag hardwired 4'h0 for the raw (uncompressed) record format.
        localparam logic [3:0] WRITE_TAG_RAW = 4'h0;

        write_state_t                    write_state;
        monitor_packet_t                 current_packet;
        monbus_timestamp_t               current_source_ts;
        logic [1:0]                      beat_idx;  // 0..2

        // Combinational helpers for the WRITE_LOAD next-record-fits check.
        logic [ADDR_WIDTH-1:0]   load_start_addr;
        logic [ADDR_WIDTH-1:0]   load_last_byte_addr;
        logic                    load_needs_rewind;
        logic [ADDR_WIDTH-1:0]   load_effective_start;
        logic                    last_beat_of_record;

        always_comb begin
            load_start_addr      = current_write_addr;
            load_last_byte_addr  = load_start_addr + ADDR_WIDTH'(REC_SIZE_INT)
                                 - {{(ADDR_WIDTH-1){1'b0}}, 1'b1};
            load_needs_rewind    = (load_last_byte_addr > cfg_limit_addr) ||
                                   (load_start_addr     < cfg_base_addr);
            load_effective_start = load_needs_rewind ? cfg_base_addr : load_start_addr;
            last_beat_of_record  = (beat_idx == 2'd2);
        end

        `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
            if (`RST_ASSERTED(axi_aresetn)) begin
                write_state        <= WRITE_IDLE;
                current_packet     <= '0;
                current_source_ts  <= '0;
                beat_idx           <= 2'd0;
                current_write_addr <= '0;
            end else begin
                case (write_state)
                    WRITE_IDLE: begin
                        if (write_fifo_rd_valid) begin
                            current_packet    <= wr_rec_packet;
                            current_source_ts <= wr_rec_source_ts;
                            beat_idx          <= 2'd0;
                            write_state       <= WRITE_LOAD;
                        end
                    end

                    WRITE_LOAD: begin
                        current_write_addr <= load_effective_start;
                        write_state        <= WRITE_AW;
                    end

                    WRITE_AW: begin
                        if (fub_wr_awvalid && fub_wr_awready) begin
                            write_state <= WRITE_W;
                        end
                    end

                    WRITE_W: begin
                        if (fub_wr_wvalid && fub_wr_wready) begin
                            write_state <= WRITE_B;
                        end
                    end

                    WRITE_B: begin
                        if (fub_wr_bvalid && fub_wr_bready) begin
                            current_write_addr <= current_write_addr + ADDR_WIDTH'(BEAT_STRIDE_INT);
                            if (last_beat_of_record) begin
                                beat_idx    <= 2'd0;
                                write_state <= WRITE_IDLE;
                            end else begin
                                beat_idx    <= beat_idx + 2'd1;
                                write_state <= WRITE_AW;
                            end
                        end
                    end

                    default: begin
                        write_state <= WRITE_IDLE;
                    end
                endcase
            end
        )

        // Backend interface control
        assign fub_wr_awvalid = (write_state == WRITE_AW);
        assign fub_wr_awaddr  = current_write_addr;
        assign fub_wr_awprot  = 3'b000;

        assign fub_wr_wvalid  = (write_state == WRITE_W);
        always_comb begin
            unique case (beat_idx)
                2'd0:    fub_wr_wdata = {WRITE_TAG_RAW, current_source_ts[59:0]};
                2'd1:    fub_wr_wdata = current_packet[MONBUS_PKT_WIDTH-1:64];
                2'd2:    fub_wr_wdata = current_packet[63:0];
                default: fub_wr_wdata = '0;
            endcase
        end
        assign fub_wr_wstrb   = {(M_AXIL_DATA_WIDTH/8){1'b1}};
        assign fub_wr_bready  = (write_state == WRITE_B);

        // FIFO read control - pop one record per WRITE_IDLE->WRITE_LOAD transition
        assign write_fifo_rd_ready = (write_state == WRITE_IDLE) && write_fifo_rd_valid;

        // Compressor stats are not used in raw mode.
        assign mon_compressor_stat_tier1_a        = 32'd0;
        assign mon_compressor_stat_tier1_b        = 32'd0;
        assign mon_compressor_stat_tier1_c        = 32'd0;
        assign mon_compressor_stat_tier0          = 32'd0;
        assign mon_compressor_stat_cam_miss       = 32'd0;
        assign mon_compressor_stat_delta_ts_ovf   = 32'd0;
        assign mon_compressor_stat_event_data_ovf = 32'd0;
        assign mon_compressor_stat_ed_delta_ovf   = 32'd0;

    end else begin : gen_writer_compressed

        // -----------------------------------------------------------------
        // monbus_compressor + per-slot 1-beat AXIL emitter.
        //
        // The compressor consumes (packet, source_ts) records via its
        // in_valid/in_ready handshake and produces 64-bit slots via
        // out_valid/out_ready. A Tier-1 record collapses to a single
        // slot; a RAW (uncompressed) record expands into three slots.
        // The writer below issues one AW+W+B per slot, with the same
        // base/limit wrap rule applied per-slot (8 bytes per slot).
        // -----------------------------------------------------------------
        typedef enum logic [1:0] {
            SLOT_IDLE = 2'd0,
            SLOT_AW   = 2'd1,
            SLOT_W    = 2'd2,
            SLOT_B    = 2'd3
        } slot_state_t;

        // 1-beat addr stride in bytes (8 for a 64-bit master).
        localparam int  SLOT_STRIDE_INT = M_AXIL_DATA_WIDTH / 8;

        // Compressor handshake
        logic                    comp_in_valid;
        logic                    comp_in_ready;
        logic                    comp_out_valid;
        logic                    comp_out_ready;
        logic [63:0]             comp_out_slot;

        assign comp_in_valid       = write_fifo_rd_valid;
        assign write_fifo_rd_ready = comp_in_ready;

        monbus_compressor u_compressor (
            .clk                  (axi_aclk),
            .rst_n                (axi_aresetn),

            .in_valid             (comp_in_valid),
            .in_ready             (comp_in_ready),
            .in_packet            (wr_rec_packet),
            .in_source_ts         (wr_rec_source_ts),

            .out_valid            (comp_out_valid),
            .out_ready            (comp_out_ready),
            .out_slot             (comp_out_slot),

            .stat_tier1_a         (mon_compressor_stat_tier1_a),
            .stat_tier1_b         (mon_compressor_stat_tier1_b),
            .stat_tier1_c         (mon_compressor_stat_tier1_c),
            .stat_tier0           (mon_compressor_stat_tier0),
            .stat_cam_miss        (mon_compressor_stat_cam_miss),
            .stat_delta_ts_ovf    (mon_compressor_stat_delta_ts_ovf),
            .stat_event_data_ovf  (mon_compressor_stat_event_data_ovf),
            .stat_ed_delta_ovf    (mon_compressor_stat_ed_delta_ovf)
        );

        // Per-slot writer FSM
        slot_state_t             slot_state;
        logic [63:0]             current_slot;

        // Per-slot wrap check (8 bytes need to fit).
        logic [ADDR_WIDTH-1:0]   slot_last_byte_addr;
        logic                    slot_needs_rewind;
        logic [ADDR_WIDTH-1:0]   slot_effective_start;

        always_comb begin
            slot_last_byte_addr  = current_write_addr + ADDR_WIDTH'(SLOT_STRIDE_INT)
                                 - {{(ADDR_WIDTH-1){1'b0}}, 1'b1};
            slot_needs_rewind    = (slot_last_byte_addr > cfg_limit_addr) ||
                                   (current_write_addr  < cfg_base_addr);
            slot_effective_start = slot_needs_rewind ? cfg_base_addr : current_write_addr;
        end

        `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
            if (`RST_ASSERTED(axi_aresetn)) begin
                slot_state         <= SLOT_IDLE;
                current_slot       <= 64'd0;
                current_write_addr <= '0;
            end else begin
                case (slot_state)
                    SLOT_IDLE: begin
                        if (comp_out_valid) begin
                            current_slot       <= comp_out_slot;
                            current_write_addr <= slot_effective_start;
                            slot_state         <= SLOT_AW;
                        end
                    end

                    SLOT_AW: begin
                        if (fub_wr_awvalid && fub_wr_awready) begin
                            slot_state <= SLOT_W;
                        end
                    end

                    SLOT_W: begin
                        if (fub_wr_wvalid && fub_wr_wready) begin
                            slot_state <= SLOT_B;
                        end
                    end

                    SLOT_B: begin
                        if (fub_wr_bvalid && fub_wr_bready) begin
                            current_write_addr <= current_write_addr + ADDR_WIDTH'(SLOT_STRIDE_INT);
                            slot_state         <= SLOT_IDLE;
                        end
                    end

                    default: slot_state <= SLOT_IDLE;
                endcase
            end
        )

        // Compressor output handshake: accept a slot only when the
        // writer is idle (we register it that cycle and transition
        // to AW). This means the compressor's internal buffering
        // sets the back-pressure shape, not the AXIL bus.
        assign comp_out_ready = (slot_state == SLOT_IDLE);

        assign fub_wr_awvalid = (slot_state == SLOT_AW);
        assign fub_wr_awaddr  = current_write_addr;
        assign fub_wr_awprot  = 3'b000;

        assign fub_wr_wvalid  = (slot_state == SLOT_W);
        assign fub_wr_wdata   = current_slot;
        assign fub_wr_wstrb   = {(M_AXIL_DATA_WIDTH/8){1'b1}};

        assign fub_wr_bready  = (slot_state == SLOT_B);

    end
    endgenerate

endmodule : monbus_axil_group
