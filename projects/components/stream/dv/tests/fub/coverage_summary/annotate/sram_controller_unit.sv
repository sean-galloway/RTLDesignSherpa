//      // verilator_coverage annotation
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
        //   - SRAM_DEPTH: FIFO depth in entries (default: 512)
        //   - SEG_COUNT_WIDTH (SCW): Width for count signals (default: $clog2(SRAM_DEPTH) + 1)
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
            // Primary parameters (long names for external configuration)
            parameter int DATA_WIDTH = 512,
            parameter int SRAM_DEPTH = 512,              // Depth per channel FIFO
            parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,  // Width of count signals
        
            // Short aliases (for internal use)
            parameter int DW = DATA_WIDTH,
            parameter int SD = SRAM_DEPTH,
            parameter int SCW = SEG_COUNT_WIDTH          // Segment count width
        ) (
 054008     input  logic          clk,
 000112     input  logic          rst_n,
        
            // Allocation interface (Read Engine Flow Control)
 000074     input  logic                  axi_rd_alloc_req,
%000000     input  logic [7:0]            axi_rd_alloc_size,
 000013     output logic [SCW-1:0]        axi_rd_alloc_space_free,
        
            // Write interface (AXI Read Engine → FIFO)
 002322     input  logic                  axi_rd_sram_valid,
 000112     output logic                  axi_rd_sram_ready,
%000000     input  logic [DW-1:0]         axi_rd_sram_data,
        
            // Drain interface (Write Engine Flow Control)
%000000     output logic [SCW-1:0]        axi_wr_drain_data_avail,
 000036     input  logic                  axi_wr_drain_req,
%000000     input  logic [7:0]            axi_wr_drain_size,
        
            // Read interface (FIFO → Latency Bridge → AXI Write Engine)
 000278     output logic                  axi_wr_sram_valid,
 000528     input  logic                  axi_wr_sram_ready,
%000000     output logic [DW-1:0]         axi_wr_sram_data,
        
            // Debug interface (for catching bridge bugs)
 000609     output logic                  dbg_bridge_pending,
 000278     output logic                  dbg_bridge_out_valid
        );
        
            //==========================================================================
            // Local Parameters
            //==========================================================================
        
            localparam int ADDR_WIDTH = $clog2(SD);
        
            // Debug: Check parameter values
 000112     initial begin
 000112         $display("sram_controller_unit: SRAM_DEPTH=%0d, ADDR_WIDTH=%0d", SD, ADDR_WIDTH);
            end
        
            //==========================================================================
            // Internal Signals
            //==========================================================================
        
            // Allocation controller outputs
 000013     logic [ADDR_WIDTH:0] alloc_space_free;     // Space from allocation controller
        
            // Drain controller outputs
%000000     logic [ADDR_WIDTH:0] drain_data_available;  // Data from drain controller
        
            // FIFO → Latency Bridge (internal connection)
 000536     logic                fifo_rd_valid_internal;
 000518     logic                fifo_rd_ready_internal;
%000000     logic [DW-1:0]       fifo_rd_data_internal;
        
            // FIFO status
%000000     logic [ADDR_WIDTH:0] fifo_count;
%000000     logic                fifo_empty;
%000000     logic                fifo_full;
        
            // Latency bridge status
 000406     logic [2:0]          bridge_occupancy;      // Beats held in latency bridge (0-5: 1 in flight + 4 in skid)
        
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
                .DEPTH(SD),
                .REGISTERED(1)
            ) u_alloc_ctrl (
                .axi_aclk           (clk),
                .axi_aresetn        (rst_n),
        
                // wr_* = ALLOCATE (reserve space for upcoming burst)
                // Read engine says "I need 16 beats" → wr_ptr += 16 → space_free -= 16
                .wr_valid           (axi_rd_alloc_req),
                .wr_size            (axi_rd_alloc_size),
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
            // Drain Controller (Virtual FIFO for drain tracking)
            //==========================================================================
            //
            // CRITICAL: Drain controller perspective (opposite of alloc):
            //   - "wr" side = DATA WRITTEN to FIFO (increment wr_ptr, increase data available)
            //   - "rd" side = DRAIN REQUEST from write engine (reserve data, decrement rd_ptr)
            //
            // Connection summary:
            //   - drain_ctrl.wr_valid ← FIFO WRITE handshake (data enters, increment occupancy)
            //   - drain_ctrl.rd_valid ← drain request (reserve N beats for upcoming write burst)
            //
            // When data enters FIFO (axi_rd_sram_valid && ready):
            //   - Drain wr_ptr advances (data available increases)
            //
            // When write engine requests drain (wr_drain_req):
            //   - Drain rd_ptr advances (data reserved for transmission)
            //   - data_available DECREASES (reserved data not available to other requests)
            //
            //==========================================================================
        
            stream_drain_ctrl #(
                .DEPTH(SD),
                .REGISTERED(1)
            ) u_drain_ctrl (
                .axi_aclk           (clk),
                .axi_aresetn        (rst_n),
        
                // wr_* = DATA WRITTEN (increment occupancy)
                // When FIFO receives data → wr_ptr += 1 → data_available += 1
                .wr_valid           (axi_rd_sram_valid && axi_rd_sram_ready),
                .wr_ready           (),
        
                // rd_* = DRAIN REQUEST (reserve data for upcoming write)
                // Write engine says "I need 16 beats" → rd_ptr += 16 → data_available -= 16
                .rd_valid           (axi_wr_drain_req),
                .rd_size            (axi_wr_drain_size),
                .rd_ready           (),
        
                // Data tracking
                .data_available     (drain_data_available),
        
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
                .DEPTH(SD)
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
 027060     always @(posedge clk) begin
 001161         if (axi_rd_sram_valid && axi_rd_sram_ready) begin
 001161             $display("CH_UNIT @%t: FIFO WRITE, fifo_count will be %0d -> %0d, bridge_occ=%0d, axi_wr_drain_data_avail=%0d",
 001161                     $time, fifo_count, fifo_count+1, bridge_occupancy, axi_wr_drain_data_avail);
                end
 000417         if (fifo_rd_valid_internal && fifo_rd_ready_internal) begin
 000417             $display("CH_UNIT @%t: FIFO DRAIN, fifo_count will be %0d -> %0d, bridge_occ=%0d, axi_wr_drain_data_avail=%0d",
 000417                     $time, fifo_count, fifo_count-1, bridge_occupancy, axi_wr_drain_data_avail);
                end
 000264         if (axi_wr_sram_valid && axi_wr_sram_ready) begin
 000264             $display("CH_UNIT @%t: OUTPUT DRAIN, fifo_count=%0d, bridge_occ=%0d, axi_wr_drain_data_avail=%0d",
 000264                     $time, fifo_count, bridge_occupancy, axi_wr_drain_data_avail);
                end
            end
            `endif
        
            // Total data available = drain controller data + latency bridge occupancy
            // The drain controller tracks FIFO only; we must add bridge buffered data
            // COMBINATIONAL - updates immediately when drain/bridge state changes
            assign axi_wr_drain_data_avail = drain_data_available + SCW'(bridge_occupancy);
        
            // Register axi_rd_alloc_space_free to break combinatorial paths to read engine
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    axi_rd_alloc_space_free <= SCW'(SD);  // Full space on reset (correct width)
                end else begin
                    axi_rd_alloc_space_free <= alloc_space_free;
                end
 001232     )
        
        endmodule : sram_controller_unit
        
