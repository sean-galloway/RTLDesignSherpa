`timescale 1ns / 1ps

//==============================================================================
// Module: sram_controller_unit
//
// Description:
//   Single-channel SRAM controller unit containing:
//   - Allocation controller (stream_alloc_ctrl)
//   - FIFO buffer (gaxi_fifo_sync)
//   - Latency bridge (stream_latency_bridge)
//
//   This unit handles one channel's data flow from AXI read engine through
//   buffering to AXI write engine with proper flow control.
//
// Parameters:
//   - DATA_WIDTH: Data width in bits (default: 512)
//   - FIFO_DEPTH: FIFO depth in entries (default: 512)
//
// Interfaces:
//   - Write side: AXI Read Engine → FIFO (valid/ready/data)
//   - Read side: FIFO → Latency Bridge → AXI Write Engine (valid/ready/data)
//   - Allocation: Flow control for read/write engines
//
// Author: RTL Design Sherpa
// Created: 2025-10-30
//==============================================================================

`include "reset_defs.svh"

module sram_controller_unit #(
    parameter int DATA_WIDTH = 512,
    parameter int FIFO_DEPTH = 512,
    parameter int DW = DATA_WIDTH,
    parameter int FD = FIFO_DEPTH
) (
    input  logic          clk,
    input  logic          rst_n,

    // Write interface (AXI Read Engine → FIFO)
    input  logic          axi_rd_sram_valid,
    output logic          axi_rd_sram_ready,
    input  logic [DW-1:0] axi_rd_sram_data,

    // Read interface (FIFO → Latency Bridge → AXI Write Engine)
    output logic          axi_wr_sram_valid,
    input  logic          axi_wr_sram_ready,
    output logic [DW-1:0] axi_wr_sram_data,

    // Allocation interface (Read Engine Flow Control)
    input  logic                  rd_alloc_req,
    input  logic [7:0]            rd_alloc_size,
    output logic [$clog2(FD):0]   rd_space_free,

    // Data available (Write Engine visibility)
    output logic [$clog2(FD):0]   wr_data_available,

    // Debug interface (for catching bridge bugs)
    output logic                  dbg_bridge_pending,
    output logic                  dbg_bridge_out_valid
);

    //==========================================================================
    // Local Parameters
    //==========================================================================

    localparam int ADDR_WIDTH = $clog2(FD);

    // Debug: Check parameter values
    initial begin
        $display("sram_controller_unit: FIFO_DEPTH=%0d, ADDR_WIDTH=%0d", FD, ADDR_WIDTH);
    end

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // Allocation controller outputs
    logic [ADDR_WIDTH:0] alloc_space_free;     // Space from allocation controller

    // FIFO → Latency Bridge (internal connection)
    logic                fifo_rd_valid_internal;
    logic                fifo_rd_ready_internal;
    logic [DW-1:0]       fifo_rd_data_internal;

    // FIFO status
    logic [ADDR_WIDTH:0] fifo_count;
    logic                fifo_empty;
    logic                fifo_full;

    // Latency bridge status
    logic [2:0]          bridge_occupancy;      // Beats held in latency bridge (0-5: 1 in flight + 4 in skid)

    //==========================================================================
    // Allocation Controller (Virtual FIFO for space tracking)
    //==========================================================================
    //
    // CRITICAL: Confusing naming! Allocation controller perspective:
    //   - "wr" side = ALLOCATE (reserve space, advance wr_ptr)
    //   - "rd" side = FULFILL allocation (data arrives, advance rd_ptr, FREE space)
    //
    // This is OPPOSITE of normal FIFO naming where:
    //   - "wr" = fill FIFO (consume space)
    //   - "rd" = drain FIFO (free space)
    //
    // Connection summary:
    //   - alloc_ctrl.wr_valid ← burst allocation request (reserve N beats)
    //   - alloc_ctrl.rd_valid ← FIFO WRITE handshake (data enters, fulfills reservation)
    //
    // When data enters FIFO (axi_rd_sram_valid && ready):
    //   - Allocation rd_ptr advances (reservation fulfilled)
    //   - space_free INCREASES (allocated space is now committed to FIFO)
    //
    //==========================================================================

    stream_alloc_ctrl #(
        .DEPTH(FD),
        .REGISTERED(1)
    ) u_alloc_ctrl (
        .axi_aclk           (clk),
        .axi_aresetn        (rst_n),

        // wr_* = ALLOCATE (reserve space for upcoming burst)
        // Read engine says "I need 16 beats" → wr_ptr += 16 → space_free -= 16
        .wr_valid           (rd_alloc_req),
        .wr_size            (rd_alloc_size),
        .wr_ready           (),

        // rd_* = RELEASE (data exits controller, free space)
        // When data leaves controller → rd_ptr += 1 → space_free += 1
        // Must monitor OUTPUT handshake to accurately track available FIFO space
        .rd_valid           (axi_wr_sram_valid && axi_wr_sram_ready),
        .rd_ready           (),

        // Space tracking
        .space_free         (alloc_space_free),

        // Unused status
        .wr_full            (),
        .wr_almost_full     (),
        .rd_empty           (),
        .rd_almost_empty    ()
    );

    //==========================================================================
    // FIFO Buffer (Physical Data Storage)
    //==========================================================================

    gaxi_fifo_sync #(
        .MEM_STYLE(FIFO_AUTO),          // Let tool decide RAM type
        .REGISTERED(1),                 // Registered read (mimics real SRAM behavior)
        .DATA_WIDTH(DW),
        .DEPTH(FD)
    ) u_channel_fifo (
        // Clock and reset
        .axi_aclk       (clk),
        .axi_aresetn    (rst_n),

        // Write port (from AXI Read Engine)
        .wr_valid       (axi_rd_sram_valid),
        .wr_ready       (axi_rd_sram_ready),  // Direct connection to output
        .wr_data        (axi_rd_sram_data),

        // Read port (to Latency Bridge) - INTERNAL
        .rd_valid       (fifo_rd_valid_internal),
        .rd_ready       (fifo_rd_ready_internal),
        .rd_data        (fifo_rd_data_internal),

        // Status
        .count          (fifo_count)
    );

    //==========================================================================
    // Latency Bridge
    //==========================================================================
    //
    // Handles 1-cycle FIFO read latency, ensuring valid and data are aligned
    // on the output to the AXI Write Engine.
    //
    //==========================================================================

    stream_latency_bridge #(
        .DATA_WIDTH(DW)
    ) u_latency_bridge (
        .clk            (clk),
        .rst_n          (rst_n),

        // Slave (from FIFO)
        .s_data         (fifo_rd_data_internal),
        .s_valid        (fifo_rd_valid_internal),
        .s_ready        (fifo_rd_ready_internal),

        // Master (to AXI Write Engine)
        .m_data         (axi_wr_sram_data),
        .m_valid        (axi_wr_sram_valid),
        .m_ready        (axi_wr_sram_ready),

        // Status (for data available counting)
        .occupancy      (bridge_occupancy),

        // Debug
        .dbg_r_pending      (dbg_bridge_pending),
        .dbg_r_out_valid    (dbg_bridge_out_valid)
    );

    //==========================================================================
    // Note: axi_rd_sram_ready connects directly to FIFO wr_ready
    // No additional registration needed - FIFO already has registered outputs
    //==========================================================================

    //==========================================================================
    // Space/Count Reporting
    //==========================================================================

    // Debug: Monitor data flow
    `ifndef SYNTHESIS
    always @(posedge clk) begin
        if (axi_rd_sram_valid && axi_rd_sram_ready) begin
            $display("CH_UNIT @%t: FIFO WRITE, fifo_count will be %0d -> %0d, bridge_occ=%0d, wr_data_avail=%0d",
                    $time, fifo_count, fifo_count+1, bridge_occupancy, wr_data_available);
        end
        if (fifo_rd_valid_internal && fifo_rd_ready_internal) begin
            $display("CH_UNIT @%t: FIFO DRAIN, fifo_count will be %0d -> %0d, bridge_occ=%0d, wr_data_avail=%0d",
                    $time, fifo_count, fifo_count-1, bridge_occupancy, wr_data_available);
        end
        if (axi_wr_sram_valid && axi_wr_sram_ready) begin
            $display("CH_UNIT @%t: OUTPUT DRAIN, fifo_count=%0d, bridge_occ=%0d, wr_data_avail=%0d",
                    $time, fifo_count, bridge_occupancy, wr_data_available);
        end
    end
    `endif

    // Total data available = FIFO count + latency bridge occupancy
    // COMBINATIONAL - updates immediately when FIFO/bridge state changes
    assign wr_data_available = fifo_count + ($clog2(FD)+1)'(bridge_occupancy);

    // Register rd_space_free to break combinatorial paths to read engine
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            rd_space_free <= ($clog2(FD)+1)'(FD);  // Full space on reset (correct width)
        end else begin
            rd_space_free <= alloc_space_free;
        end
    )

endmodule : sram_controller_unit
