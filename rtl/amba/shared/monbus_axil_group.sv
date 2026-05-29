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

Timestamping (see MON-PKT-64-to-128-plan.md sec 4.4.1):
- Free-running 64-bit counter inside the group is driven OUT on mon_time_out
  to every wrapper's i_mon_time input.
- Wrappers sample on emission and return the source timestamp on the
  monbus_timestamp side-band, which arrives here paired with the packet.
- On the input handshake, the group also captures an arrival timestamp from
  its own counter.
- The write FIFO carries {packet[127:0], source_ts[63:0], arrival_ts[63:0]}.
- The AXIL master write FSM emits 2-4 64-bit beats per record depending on
  cfg_ts_append_enable / cfg_ts_append_mode.

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
    parameter int NUM_PROTOCOLS      = 3     // AXI, AXIS, CORE
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

    // Timestamp-append configuration
    input  logic                          cfg_ts_append_enable,
    input  logic [1:0]                    cfg_ts_append_mode,

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
    output logic [7:0]                    write_fifo_count
);

    // =======================================================================
    // Local Parameters
    // =======================================================================

    localparam int ERR_FIFO_ADDR_WIDTH   = $clog2(FIFO_DEPTH_ERR);
    localparam int WRITE_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_WRITE);

    // Combined write-FIFO record: {packet[127:0], source_ts[63:0], arrival_ts[63:0]}
    localparam int WRITE_REC_WIDTH = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH + MONBUS_TS_WIDTH;

    // Error-FIFO record: {source_ts[63:0], packet[127:0]} = 192 bits.
    // The CPU drains via the 64-bit s_axil read port in exactly three
    // beats (slice 0: packet[63:0]; slice 1: packet[127:64]; slice 2:
    // source_ts[63:0]). Layout chosen so packet bits are contiguous in
    // the low half, matching the natural byte-order expectation.
    localparam int ERR_FIFO_REC_WIDTH = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;

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
    monbus_timestamp_t               wr_rec_arrival_ts;

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
    // Master Write FIFO (combined record: packet + source_ts + arrival_ts)
    // =======================================================================

    assign write_fifo_wr_valid = input_monbus_valid && pkt_to_write_fifo && !pkt_drop;
    // Pack: {packet[127:0], source_ts[63:0], arrival_ts[63:0]}
    // arrival_ts is sampled on the input handshake — by construction
    // write_fifo_wr_valid implies the handshake cycle, so r_ts_counter at this
    // moment is the arrival time.
    assign write_fifo_wr_data  = {input_monbus_packet, input_monbus_source_ts, r_ts_counter};

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

    // Unpack record at FIFO output
    assign wr_rec_arrival_ts = write_fifo_rd_data[MONBUS_TS_WIDTH-1:0];
    assign wr_rec_source_ts  = write_fifo_rd_data[2*MONBUS_TS_WIDTH-1:MONBUS_TS_WIDTH];
    assign wr_rec_packet     = write_fifo_rd_data[WRITE_REC_WIDTH-1:2*MONBUS_TS_WIDTH];

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
    // of the current head-of-FIFO entry the next read should return:
    //   slice 0: packet[63:0]
    //   slice 1: packet[127:64]
    //   slice 2: source_ts[63:0]
    // The slice counter advances on each successful read; the FIFO entry
    // is popped only when the third slice fires. The CPU therefore
    // drains one packet by issuing three reads in a row -- the read
    // address is ignored for slice selection so reads can target the
    // same offset or different offsets, the slicer doesn't care.
    //
    // arready stalls while the FIFO is empty (no entry to slice).
    // Once a drain is in progress (r_slice_idx != 0) the head entry
    // stays put until the wrap, so the CPU can pause between beats
    // without losing the in-flight packet.
    // ---------------------------------------------------------------
    typedef enum logic [1:0] {
        SLICE_PKT_LO = 2'd0,
        SLICE_PKT_HI = 2'd1,
        SLICE_SRC_TS = 2'd2,
        SLICE_RSVD   = 2'd3
    } read_slice_t;

    read_slice_t r_slice_idx;

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_slice_idx <= SLICE_PKT_LO;
        end else if (fub_rd_rvalid && fub_rd_rready) begin
            r_slice_idx <= (r_slice_idx == SLICE_SRC_TS)
                           ? SLICE_PKT_LO
                           : read_slice_t'(r_slice_idx + 2'd1);
        end
    )

    assign fub_rd_arready    = !err_fifo_empty;
    assign fub_rd_rvalid     = fub_rd_arvalid && fub_rd_arready;
    // Pop only when the third slice (source_ts) is read -- the FIFO
    // advances every 3 reads, not every read.
    assign err_fifo_rd_ready = fub_rd_rvalid && fub_rd_rready
                            && (r_slice_idx == SLICE_SRC_TS);

    always_comb begin
        fub_rd_rdata = {S_AXIL_DATA_WIDTH{1'b0}};
        if (!err_fifo_empty) begin
            unique case (r_slice_idx)
                SLICE_PKT_LO: fub_rd_rdata = err_fifo_rd_data[63:0];
                SLICE_PKT_HI: fub_rd_rdata = err_fifo_rd_data[MONBUS_PKT_WIDTH-1:64];
                SLICE_SRC_TS: fub_rd_rdata = err_fifo_rd_data[ERR_FIFO_REC_WIDTH-1:MONBUS_PKT_WIDTH];
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
    // Write FSM — 64-bit master, variable record size
    //
    // Beat order per record (always +8 bytes per beat):
    //
    //   append_enable=0:            beat0=pkt[63:0]    beat1=pkt[127:64]                              (16 B)
    //   append_enable=1, mode=01:   beat0=pkt[63:0]    beat1=pkt[127:64]   beat2=source_ts            (24 B)
    //   append_enable=1, mode=10:   beat0=pkt[63:0]    beat1=pkt[127:64]   beat2=arrival_ts           (24 B)
    //   append_enable=1, mode=11:   beat0=pkt[63:0]    beat1=pkt[127:64]   beat2=source_ts   beat3=arrival_ts  (32 B)
    //
    // Address-window wrap:
    //   The cfg_base_addr / cfg_limit_addr window is intended to be a
    //   record-aligned ring. We use a "next-record-fits" check at the
    //   start of each record only: if the current_write_addr + record_size
    //   would exceed cfg_limit_addr, rewind to cfg_base_addr first. Once a
    //   record is in flight we DO NOT wrap mid-record, even if a beat
    //   address crosses the limit — partial records corrupt the data layout
    //   in memory. The strict interpretation (rewind only between records)
    //   matches the spec note in section 4.4.1.
    // =======================================================================

    typedef enum logic [2:0] {
        WRITE_IDLE   = 3'd0,
        WRITE_LOAD   = 3'd1,  // 1 cycle: latch record from FIFO, compute size, maybe wrap addr
        WRITE_AW     = 3'd2,
        WRITE_W      = 3'd3,
        WRITE_B      = 3'd4
    } write_state_t;

    write_state_t                    write_state;
    monitor_packet_t                 current_packet;
    monbus_timestamp_t               current_source_ts;
    monbus_timestamp_t               current_arrival_ts;

    logic                            cur_append_enable;
    logic [1:0]                      cur_append_mode;

    // Beat counters — 3 bits because total_beats can be 4 (mode 11)
    logic [2:0]                      total_beats;     // 2, 3, or 4
    logic [2:0]                      beat_idx;        // 0..total_beats-1

    // 1-beat addr stride in bytes (8 for a 64-bit master).
    localparam int             BEAT_STRIDE_INT = M_AXIL_DATA_WIDTH / 8;

    // Compute beats for a given (en, mode) combo
    function automatic logic [2:0] record_beats(input logic en, input logic [1:0] mode);
        if (!en)                  return 3'd2;
        if (mode == 2'b11)        return 3'd4; // both
        if (mode == 2'b01 || mode == 2'b10) return 3'd3;
        return 3'd2;  // mode 00 with en=1 is treated as packet-only
    endfunction

    // Compute current beat's data based on beat index + mode.
    // Beat slot mapping:
    //   slot 0 -> packet[63:0]
    //   slot 1 -> packet[127:64]
    //   slot 2 -> source_ts   (if mode==01 or 11)
    //          OR arrival_ts  (if mode==10)
    //   slot 3 -> arrival_ts  (mode==11 only)
    function automatic logic [M_AXIL_DATA_WIDTH-1:0] beat_data(
        input logic [2:0]              idx,
        input logic                    en,
        input logic [1:0]              mode,
        input monitor_packet_t         pkt,
        input monbus_timestamp_t       src_ts,
        input monbus_timestamp_t       arr_ts
    );
        case (idx)
            3'd0: return pkt[63:0];
            3'd1: return pkt[127:64];
            3'd2: begin
                if (!en)                 return '0;
                if (mode == 2'b10)       return arr_ts;
                return src_ts; // 01 or 11
            end
            3'd3: return arr_ts; // only valid when mode==11
            default: return '0;
        endcase
    endfunction

    // Combinational helpers for the WRITE_LOAD next-record-fits check.
    logic [ADDR_WIDTH-1:0]   rec_size_bytes;
    logic [ADDR_WIDTH-1:0]   load_start_addr;
    logic [ADDR_WIDTH-1:0]   load_last_byte_addr;
    logic                    load_needs_rewind;
    logic [ADDR_WIDTH-1:0]   load_effective_start;
    logic                    last_beat_of_record;

    always_comb begin
        // Total bytes in the record currently being launched.
        // total_beats is at most 4, BEAT_STRIDE_INT is 8 -> max 32, fits any
        // reasonable ADDR_WIDTH. Zero-extend the multiplicands.
        rec_size_bytes       = {{(ADDR_WIDTH-3){1'b0}}, total_beats} *
                               ADDR_WIDTH'(BEAT_STRIDE_INT);
        load_start_addr      = current_write_addr;
        load_last_byte_addr  = load_start_addr + rec_size_bytes - {{(ADDR_WIDTH-1){1'b0}}, 1'b1};
        load_needs_rewind    = (load_last_byte_addr > cfg_limit_addr) ||
                               (load_start_addr     < cfg_base_addr);
        load_effective_start = load_needs_rewind ? cfg_base_addr : load_start_addr;

        last_beat_of_record  = (beat_idx + 3'd1) == total_beats;
    end

    // FSM
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            write_state        <= WRITE_IDLE;
            current_packet     <= '0;
            current_source_ts  <= '0;
            current_arrival_ts <= '0;
            cur_append_enable  <= 1'b0;
            cur_append_mode    <= 2'b00;
            total_beats        <= 3'd2;
            beat_idx           <= 3'd0;
            current_write_addr <= '0;
        end else begin
            case (write_state)
                WRITE_IDLE: begin
                    if (write_fifo_rd_valid) begin
                        // Latch record + capture cfg snapshot for this record
                        current_packet     <= wr_rec_packet;
                        current_source_ts  <= wr_rec_source_ts;
                        current_arrival_ts <= wr_rec_arrival_ts;
                        cur_append_enable  <= cfg_ts_append_enable;
                        cur_append_mode    <= cfg_ts_append_mode;
                        total_beats        <= record_beats(cfg_ts_append_enable, cfg_ts_append_mode);
                        beat_idx           <= 3'd0;
                        write_state        <= WRITE_LOAD;
                    end
                end

                WRITE_LOAD: begin
                    // Decide whether the next full record fits in the window;
                    // if not, rewind to base BEFORE issuing the first AW.
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
                        // Beat retired
                        current_write_addr <= current_write_addr + ADDR_WIDTH'(BEAT_STRIDE_INT);
                        if (last_beat_of_record) begin
                            beat_idx    <= 3'd0;
                            write_state <= WRITE_IDLE;
                        end else begin
                            beat_idx    <= beat_idx + 3'd1;
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
    assign fub_wr_wdata   = beat_data(beat_idx,
                                       cur_append_enable,
                                       cur_append_mode,
                                       current_packet,
                                       current_source_ts,
                                       current_arrival_ts);
    assign fub_wr_wstrb   = {(M_AXIL_DATA_WIDTH/8){1'b1}}; // All bytes valid

    assign fub_wr_bready  = (write_state == WRITE_B);

    // FIFO read control - pop one record per WRITE_IDLE->WRITE_LOAD transition
    assign write_fifo_rd_ready = (write_state == WRITE_IDLE) && write_fifo_rd_valid;

endmodule : monbus_axil_group
