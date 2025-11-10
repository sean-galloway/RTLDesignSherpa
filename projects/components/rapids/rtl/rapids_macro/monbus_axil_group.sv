// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_axil_group
// Purpose: Monbus Axil Group module
//
// Documentation: projects/components/rapids_macro/PRD.md
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/*
================================================================================
Monitor Bus AXI-Lite Group
================================================================================

This module aggregates monitor bus streams from source and sink paths,
applies configurable filtering based on protocol and packet types, and
routes filtered packets to either:
- Error/Interrupt FIFO (slave read interface) - generates interrupt when not empty
- Master Write FIFO - writes to configurable address range

Features:
- Round-robin arbitration between source and sink monitor streams
- Per-protocol configurable packet filtering (drop, error/interrupt, master write)
- Separate FIFOs for error/interrupt vs master write paths
- Configurable address range for master write operations
- Protocol support: AXI, Network, CORE (3 protocols)
- Built-in AXI-Lite skid buffering for timing closure

Configuration Registers (per protocol):
- pkt_mask[15:0]     - Drop packets when bit[pkt_type] = 1
- err_select[15:0]   - Route to error FIFO when bit[pkt_type] = 1
- Individual event masks for each packet type (16 bits each)

================================================================================
*/

`include "reset_defs.svh"

module monbus_axil_group #(
    parameter int FIFO_DEPTH_ERR    = 64,   // Error/interrupt FIFO depth
    parameter int FIFO_DEPTH_WRITE  = 32,   // Master write FIFO depth
    parameter int ADDR_WIDTH        = 32,   // AXI address width
    parameter int DATA_WIDTH        = 32,   // AXI data width (for master write)
    parameter int NUM_PROTOCOLS     = 3     // AXI, Network, CORE
) (
    // Clock and Reset
    input  logic                    axi_aclk,
    input  logic                    axi_aresetn,

    // Source Monitor Bus Input
    input  logic                    source_monbus_valid,
    output logic                    source_monbus_ready,
    input  logic [63:0]             source_monbus_packet,

    // Sink Monitor Bus Input
    input  logic                    sink_monbus_valid,
    output logic                    sink_monbus_ready,
    input  logic [63:0]             sink_monbus_packet,

    // Error/Interrupt FIFO (Slave Read Interface)
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,

    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,
    output logic [DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]              s_axil_rresp,

    // Master Write Interface
    output logic                    m_axil_awvalid,
    input  logic                    m_axil_awready,
    output logic [ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]              m_axil_awprot,

    output logic                    m_axil_wvalid,
    input  logic                    m_axil_wready,
    output logic [DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [DATA_WIDTH/8-1:0] m_axil_wstrb,

    input  logic                    m_axil_bvalid,
    output logic                    m_axil_bready,
    input  logic [1:0]              m_axil_bresp,

    // Interrupt Output (renamed from 'interrupt' to avoid C++ keyword)
    output logic                    irq_out,

    // Configuration Interface (simplified - could be expanded to full AXI-Lite)
    input  logic [ADDR_WIDTH-1:0]   cfg_base_addr,       // Base address for master writes
    input  logic [ADDR_WIDTH-1:0]   cfg_limit_addr,      // Limit address for master writes

    // Protocol Configuration - AXI (protocol 0)
    input  logic [15:0]             cfg_axi_pkt_mask,     // Drop mask for packet types
    input  logic [15:0]             cfg_axi_err_select,   // Error FIFO select for packet types
    input  logic [15:0]             cfg_axi_error_mask,   // Individual error event mask
    input  logic [15:0]             cfg_axi_timeout_mask, // Individual timeout event mask
    input  logic [15:0]             cfg_axi_compl_mask,   // Individual completion event mask
    input  logic [15:0]             cfg_axi_thresh_mask,  // Individual threshold event mask
    input  logic [15:0]             cfg_axi_perf_mask,    // Individual performance event mask
    input  logic [15:0]             cfg_axi_addr_mask,    // Individual address match event mask
    input  logic [15:0]             cfg_axi_debug_mask,   // Individual debug event mask

    // Protocol Configuration - AXIS (protocol 1)
    input  logic [15:0]             cfg_axis_pkt_mask,
    input  logic [15:0]             cfg_axis_err_select,
    input  logic [15:0]             cfg_axis_error_mask,
    input  logic [15:0]             cfg_axis_timeout_mask,
    input  logic [15:0]             cfg_axis_compl_mask,
    input  logic [15:0]             cfg_axis_credit_mask,
    input  logic [15:0]             cfg_axis_channel_mask,
    input  logic [15:0]             cfg_axis_stream_mask,

    // Protocol Configuration - CORE (protocol 2)
    input  logic [15:0]             cfg_core_pkt_mask,
    input  logic [15:0]             cfg_core_err_select,
    input  logic [15:0]             cfg_core_error_mask,
    input  logic [15:0]             cfg_core_timeout_mask,
    input  logic [15:0]             cfg_core_compl_mask,
    input  logic [15:0]             cfg_core_thresh_mask,
    input  logic [15:0]             cfg_core_perf_mask,
    input  logic [15:0]             cfg_core_debug_mask,

    // Debug/Status
    output logic                    err_fifo_full,
    output logic                    write_fifo_full,
    output logic [7:0]              err_fifo_count,
    output logic [7:0]              write_fifo_count
);

    import monitor_pkg::*;

    // =======================================================================
    // Local Parameters
    // =======================================================================

    localparam int ERR_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_ERR);
    localparam int WRITE_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_WRITE);

    // =======================================================================
    // Internal Signals
    // =======================================================================

    // Arbitrated monitor bus
    logic                    arb_monbus_valid;
    logic                    arb_monbus_ready;
    logic [63:0]             arb_monbus_packet;

    // Packet analysis
    logic [3:0]              pkt_type;
    logic [2:0]              pkt_protocol;
    logic [3:0]              pkt_event_code;
    logic [35:0]             pkt_event_data;

    // Filter decisions
    logic                    pkt_drop;
    logic                    pkt_to_err_fifo;
    logic                    pkt_to_write_fifo;
    logic                    pkt_event_masked;

    // Error FIFO signals
    logic                    err_fifo_wr_valid;
    logic                    err_fifo_wr_ready;
    logic [63:0]             err_fifo_wr_data;
    logic                    err_fifo_rd_valid;
    logic                    err_fifo_rd_ready;
    logic [63:0]             err_fifo_rd_data;
    logic                    err_fifo_empty;
    logic [ERR_FIFO_ADDR_WIDTH:0] err_fifo_count_full;

    // Write FIFO signals
    logic                    write_fifo_wr_valid;
    logic                    write_fifo_wr_ready;
    logic [63:0]             write_fifo_wr_data;
    logic                    write_fifo_rd_valid;
    logic                    write_fifo_rd_ready;
    logic [63:0]             write_fifo_rd_data;
    logic                    write_fifo_empty;
    logic [WRITE_FIFO_ADDR_WIDTH:0] write_fifo_count_full;

    // Backend interfaces for AXI-Lite modules
    logic [ADDR_WIDTH-1:0]   fub_rd_araddr;
    logic [2:0]              fub_rd_arprot;
    logic                    fub_rd_arvalid;
    logic                    fub_rd_arready;
    logic [DATA_WIDTH-1:0]   fub_rd_rdata;
    logic [1:0]              fub_rd_rresp;
    logic                    fub_rd_rvalid;
    logic                    fub_rd_rready;

    logic [ADDR_WIDTH-1:0]   fub_wr_awaddr;
    logic [2:0]              fub_wr_awprot;
    logic                    fub_wr_awvalid;
    logic                    fub_wr_awready;
    logic [DATA_WIDTH-1:0]   fub_wr_wdata;
    logic [DATA_WIDTH/8-1:0] fub_wr_wstrb;
    logic                    fub_wr_wvalid;
    logic                    fub_wr_wready;
    logic [1:0]              fub_wr_bresp;
    logic                    fub_wr_bvalid;
    logic                    fub_wr_bready;

    // Address generation for master writes
    logic [ADDR_WIDTH-1:0]   current_write_addr;
    logic [ADDR_WIDTH-1:0]   next_write_addr;
    logic                    addr_counter_enable;

    // =======================================================================
    // Monitor Bus Arbitration
    // =======================================================================

    monbus_arbiter #(
        .CLIENTS            (2),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_arbiter (
        .axi_aclk           (axi_aclk),
        .axi_aresetn        (axi_aresetn),
        .block_arb          (1'b0),

        // Inputs
        .monbus_valid_in    ({sink_monbus_valid, source_monbus_valid}),
        .monbus_ready_in    ({sink_monbus_ready, source_monbus_ready}),
        .monbus_packet_in   ({sink_monbus_packet, source_monbus_packet}),

        // Output
        .monbus_valid       (arb_monbus_valid),
        .monbus_ready       (arb_monbus_ready),
        .monbus_packet      (arb_monbus_packet),

        // Debug (unused)
        .grant_valid        (),
        .grant              (),
        .grant_id           (),
        .last_grant         ()
    );

    // =======================================================================
    // Packet Analysis and Filtering
    // =======================================================================

    // Extract packet fields
    assign pkt_type = get_packet_type(arb_monbus_packet);
    assign pkt_protocol = arb_monbus_packet[59:57]; // 3-bit protocol field
    assign pkt_event_code = get_event_code(arb_monbus_packet);
    assign pkt_event_data = get_event_data(arb_monbus_packet);

    // Filter logic
    always_comb begin
        pkt_drop = 1'b0;
        pkt_to_err_fifo = 1'b0;
        pkt_to_write_fifo = 1'b0;
        pkt_event_masked = 1'b0;

        // Only process supported protocols - fix width expansion warning
        if ({29'b0, pkt_protocol} < NUM_PROTOCOLS && arb_monbus_valid) begin

            // Protocol-specific filtering
            case (pkt_protocol)
                3'b000: begin // AXI
                    // Check if packet type is dropped
                    pkt_drop = cfg_axi_pkt_mask[pkt_type];

                    // Check if packet type goes to error FIFO
                    pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;

                    // Check individual event masking
                    case (pkt_type)
                        monitor_pkg::PktTypeError:     pkt_event_masked = cfg_axi_error_mask[pkt_event_code];
                        monitor_pkg::PktTypeTimeout:   pkt_event_masked = cfg_axi_timeout_mask[pkt_event_code];
                        monitor_pkg::PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[pkt_event_code];
                        monitor_pkg::PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[pkt_event_code];
                        monitor_pkg::PktTypePerf:      pkt_event_masked = cfg_axi_perf_mask[pkt_event_code];
                        monitor_pkg::PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[pkt_event_code];
                        monitor_pkg::PktTypeDebug:     pkt_event_masked = cfg_axi_debug_mask[pkt_event_code];
                        default:                       pkt_event_masked = 1'b0;
                    endcase
                end

                3'b001: begin // AXIS (AXI4-Stream)
                    pkt_drop = cfg_axis_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_axis_err_select[pkt_type] && !pkt_drop;

                    case (pkt_type)
                        monitor_pkg::PktTypeError:     pkt_event_masked = cfg_axis_error_mask[pkt_event_code];
                        monitor_pkg::PktTypeTimeout:   pkt_event_masked = cfg_axis_timeout_mask[pkt_event_code];
                        monitor_pkg::PktTypeCompletion: pkt_event_masked = cfg_axis_compl_mask[pkt_event_code];
                        monitor_pkg::PktTypeCredit:    pkt_event_masked = cfg_axis_credit_mask[pkt_event_code];
                        monitor_pkg::PktTypeChannel:   pkt_event_masked = cfg_axis_channel_mask[pkt_event_code];
                        monitor_pkg::PktTypeStream:    pkt_event_masked = cfg_axis_stream_mask[pkt_event_code];
                        default:                       pkt_event_masked = 1'b0;
                    endcase
                end

                3'b010: begin // CORE (fixed from 3'b100)
                    pkt_drop = cfg_core_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_core_err_select[pkt_type] && !pkt_drop;

                    case (pkt_type)
                        monitor_pkg::PktTypeError:     pkt_event_masked = cfg_core_error_mask[pkt_event_code];
                        monitor_pkg::PktTypeTimeout:   pkt_event_masked = cfg_core_timeout_mask[pkt_event_code];
                        monitor_pkg::PktTypeCompletion: pkt_event_masked = cfg_core_compl_mask[pkt_event_code];
                        monitor_pkg::PktTypeThreshold: pkt_event_masked = cfg_core_thresh_mask[pkt_event_code];
                        monitor_pkg::PktTypePerf:      pkt_event_masked = cfg_core_perf_mask[pkt_event_code];
                        monitor_pkg::PktTypeDebug:     pkt_event_masked = cfg_core_debug_mask[pkt_event_code];
                        default:                       pkt_event_masked = 1'b0;
                    endcase
                end

                default: begin
                    pkt_drop = 1'b1; // Drop unsupported protocols
                end
            endcase

            // Final decision - apply event masking
            if (pkt_event_masked) begin
                pkt_drop = 1'b1;
                pkt_to_err_fifo = 1'b0;
            end

            // Packets go to write FIFO if not dropped and not going to error FIFO
            pkt_to_write_fifo = !pkt_drop && !pkt_to_err_fifo;
        end
    end

    // Arbitrated ready based on FIFO availability
    assign arb_monbus_ready = pkt_drop ||
                            (pkt_to_err_fifo && err_fifo_wr_ready) ||
                            (pkt_to_write_fifo && write_fifo_wr_ready);

    // =======================================================================
    // Error/Interrupt FIFO
    // =======================================================================

    assign err_fifo_wr_valid = arb_monbus_valid && pkt_to_err_fifo && !pkt_drop;
    assign err_fifo_wr_data = arb_monbus_packet;

    gaxi_fifo_sync #(
        .REGISTERED     (0),
        .DATA_WIDTH     (64),
        .DEPTH          (FIFO_DEPTH_ERR),
        .INSTANCE_NAME  ("ERROR_INTERRUPT_FIFO")
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
    assign err_fifo_full = !err_fifo_wr_ready;
    assign irq_out = !err_fifo_empty; // Interrupt when FIFO not empty
    // Zero-extend FIFO count to 8 bits (FIFO count is ERR_FIFO_ADDR_WIDTH+1 bits)
    assign err_fifo_count = {{(8-ERR_FIFO_ADDR_WIDTH-1){1'b0}}, err_fifo_count_full};

    // =======================================================================
    // Master Write FIFO
    // =======================================================================

    assign write_fifo_wr_valid = arb_monbus_valid && pkt_to_write_fifo && !pkt_drop;
    assign write_fifo_wr_data = arb_monbus_packet;

    gaxi_fifo_sync #(
        .REGISTERED     (0),
        .DATA_WIDTH     (64),
        .DEPTH          (FIFO_DEPTH_WRITE),
        .INSTANCE_NAME  ("MASTER_WRITE_FIFO")
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

    assign write_fifo_empty = !write_fifo_rd_valid;
    assign write_fifo_full = !write_fifo_wr_ready;
    // Zero-extend FIFO count to 8 bits (FIFO count is WRITE_FIFO_ADDR_WIDTH+1 bits)
    assign write_fifo_count = {{(8-WRITE_FIFO_ADDR_WIDTH-1){1'b0}}, write_fifo_count_full};

    // =======================================================================
    // AXI-Lite Slave Read Interface (Error/Interrupt FIFO Access)
    // =======================================================================

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (DATA_WIDTH),
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

    // Connect backend to error FIFO - simple read interface
    assign fub_rd_arready = !err_fifo_empty;
    assign fub_rd_rvalid = fub_rd_arvalid && fub_rd_arready;
    assign err_fifo_rd_ready = fub_rd_rvalid && fub_rd_rready;

    // Return either the packet data or zero if FIFO empty - fix width issues
    always_comb begin
        fub_rd_rdata = {DATA_WIDTH{1'b0}};  // Default to zero
        if (!err_fifo_empty) begin
            if (DATA_WIDTH == 64) begin
                fub_rd_rdata = err_fifo_rd_data[DATA_WIDTH-1:0];
            end else begin
                // For 32-bit data width, select upper or lower word based on address bit [2]
                // Zero-extend to DATA_WIDTH to avoid width mismatch warnings
                fub_rd_rdata = {{(DATA_WIDTH-32){1'b0}},
                                (fub_rd_araddr[2] ? err_fifo_rd_data[63:32] : err_fifo_rd_data[31:0])};
            end
        end
    end
    assign fub_rd_rresp = 2'b00; // OKAY response

    // =======================================================================
    // Address Counter for Master Writes
    // =======================================================================

    // Calculate next address - fix off-by-one issue
    always_comb begin
        if (DATA_WIDTH == 64) begin
            next_write_addr = current_write_addr + 8;
        end else begin
            next_write_addr = current_write_addr + 4;
        end

        // Check if next address would exceed limit, if so wrap to base
        if (next_write_addr > cfg_limit_addr) begin
            next_write_addr = cfg_base_addr;
        end
    end

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            current_write_addr <= cfg_base_addr;
        end else if (addr_counter_enable) begin
            current_write_addr <= next_write_addr;
        end
    )


    // =======================================================================
    // AXI-Lite Master Write Interface
    // =======================================================================

    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (DATA_WIDTH),
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
    // Write FIFO to Master Write Interface Logic
    // =======================================================================

    typedef enum logic [2:0] {
        WRITE_IDLE       = 3'b000,
        WRITE_ADDR       = 3'b001,
        WRITE_DATA_LOW   = 3'b010,
        WRITE_DATA_HIGH  = 3'b011,
        WRITE_RESP       = 3'b100
    } write_state_t;

    write_state_t write_state;
    logic [63:0]  current_packet;
    logic         upper_word_pending;

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            write_state <= WRITE_IDLE;
            current_packet <= '0;
            upper_word_pending <= 1'b0;
        end else begin
            case (write_state) // Fix case incomplete warning
                WRITE_IDLE: begin
                    if (write_fifo_rd_valid) begin
                        current_packet <= write_fifo_rd_data;
                        write_state <= WRITE_ADDR;
                        upper_word_pending <= (DATA_WIDTH == 32);
                    end
                end

                WRITE_ADDR: begin
                    if (fub_wr_awvalid && fub_wr_awready) begin
                        write_state <= WRITE_DATA_LOW;
                    end
                end

                WRITE_DATA_LOW: begin
                    if (fub_wr_wvalid && fub_wr_wready) begin
                        write_state <= WRITE_RESP;
                    end
                end

                WRITE_RESP: begin
                    if (fub_wr_bvalid && fub_wr_bready) begin
                        if (upper_word_pending && DATA_WIDTH == 32) begin
                            // Need to write upper 32 bits
                            write_state <= WRITE_ADDR;
                            upper_word_pending <= 1'b0;
                        end else begin
                            // Transaction complete
                            write_state <= WRITE_IDLE;
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
    assign fub_wr_awvalid = (write_state == WRITE_ADDR);
    assign fub_wr_awaddr = current_write_addr;
    assign fub_wr_awprot = 3'b000;

    assign fub_wr_wvalid = (write_state == WRITE_DATA_LOW);

    // Fix width issues for write data assignment
    always_comb begin
        if (DATA_WIDTH == 64) begin
            fub_wr_wdata = current_packet[DATA_WIDTH-1:0];
        end else begin
            // For 32-bit data width, send lower or upper word
            // Zero-extend to DATA_WIDTH to avoid width mismatch warnings
            fub_wr_wdata = {{(DATA_WIDTH-32){1'b0}},
                           (upper_word_pending ? current_packet[31:0] : current_packet[63:32])};
        end
    end

    assign fub_wr_wstrb = {(DATA_WIDTH/8){1'b1}}; // All bytes valid

    assign fub_wr_bready = (write_state == WRITE_RESP);

    // FIFO read control - read when starting a new transaction
    assign write_fifo_rd_ready = (write_state == WRITE_IDLE) && write_fifo_rd_valid;

    // Address counter enable - increment after each completed write
    assign addr_counter_enable = (write_state == WRITE_RESP) && fub_wr_bvalid && fub_wr_bready &&
                                (!upper_word_pending || DATA_WIDTH == 64);

endmodule : monbus_axil_group
