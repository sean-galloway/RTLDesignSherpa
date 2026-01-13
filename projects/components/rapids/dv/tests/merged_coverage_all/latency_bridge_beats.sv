//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: beats_latency_bridge
        // Purpose: Simple Latency-1 Bridge with Skid Buffer
        //
        // Description:
        //   Bridges registered FIFO output (1-cycle read latency) to consumer.
        //   Uses simple glue logic + gaxi_fifo_sync skid buffer for backpressure.
        //
        // Architecture:
        //   - Glue logic: Flop tracks FIFO drain in progress
        //   - Skid buffer: 4-deep FIFO smooths backpressure
        //   - No complex ready calculations - skid buffer handles it all!
        //
        // Timing:
        //   Cycle 0: Drain FIFO (s_valid && skid_ready) → r_drain_ip = 1
        //   Cycle 1: Data arrives from FIFO → Push to skid (skid_valid = r_drain_ip)
        //   Cycle N: Consumer drains skid buffer at its own pace
        //
        // Key Features:
        //   - Maintains full throughput when consumer is ready
        //   - Skid buffer absorbs consumer backpressure
        //   - Simple, easy to understand and verify
        //
        // Documentation: projects/components/rapids/PRD.md
        // Subsystem: rapids_fub_beats
        //
        // Author: sean galloway
        // Created: 2025-10-30
        // Redesigned: 2025-11-03 (simplified with skid buffer)
        
        `timescale 1ns / 1ps
        
        `include "reset_defs.svh"
        `include "fifo_defs.svh"
        
        module latency_bridge_beats #(
            // Primary parameters (long names for external configuration)
            parameter int DATA_WIDTH = 64,
            parameter int SKID_DEPTH = 4,  // Skid buffer depth (2-4 recommended)
        
            // Short aliases (for internal use)
            parameter int DW = DATA_WIDTH
        ) (
            // Clock and Reset
 000338     input  logic          clk,
%000006     input  logic          rst_n,
        
            //=========================================================================
            // Upstream Interface (from registered FIFO)
            //=========================================================================
            // Data becomes valid 1 cycle AFTER s_valid && s_ready handshake
 000012     input  logic          s_valid,
 000014     output logic          s_ready,
%000000     input  logic [DW-1:0] s_data,
        
            //=========================================================================
            // Downstream Interface (to consumer)
            //=========================================================================
            // Standard valid/ready handshake
 000018     output logic          m_valid,
%000006     input  logic          m_ready,
%000000     output logic [DW-1:0] m_data,
        
            //=========================================================================
            // Status Interface (for data available counting)
            //=========================================================================
%000008     output logic [2:0]    occupancy,      // Beats in bridge (0-5: 1 in flight + 4 in skid)
        
            //=========================================================================
            // Debug Interface (for catching stuck data)
            //=========================================================================
 000012     output logic          dbg_r_pending,
 000018     output logic          dbg_r_out_valid
        );
        
            //=========================================================================
            // Internal Signals
            //=========================================================================
        
            // Glue logic flop: tracks FIFO drain in progress (data arriving next cycle)
 000012     logic r_drain_ip;
        
            // Skid buffer interface
 000012     logic                 skid_wr_valid;
 000014     logic                 skid_wr_ready;
%000000     logic [DW-1:0]        skid_wr_data;
%000008     logic [$clog2(SKID_DEPTH):0] skid_count;
        
            //=========================================================================
            // Simple Glue Logic
            //=========================================================================
            // Cycle 0: Decide to drain FIFO
            // Cycle 1: Data arrives, push to skid buffer
        
            // Current cycle drain: freeing a slot from skid buffer
%000008     wire w_draining_now = m_valid && m_ready;
        
            // Backpressure Logic: Account for stalled writes only
            //
            // There's a 1-cycle pipeline (r_drain_ip) between accepting from upstream
            // and writing to the FIFO. This means:
            // - Cycle N: Accept from upstream
            // - Cycle N+1: Write to FIFO (skid_wr_valid=1)
            //
            // The FIFO's count and wr_ready update at the clock edge when writes occur.
            // If a write COMPLETES (wr_valid && wr_ready), count updates and that write
            // is NO LONGER pending.
            //
            // If a write is STALLED (wr_valid && !wr_ready), it remains pending and we
            // must account for it.
            //
            // Solution: Only count writes that are STALLED (not completing this cycle)
            //
            // Truth Table (for SKID_DEPTH=4):
            // count | wr_valid | wr_ready | stalled | pending | room | s_ready | Scenario
            // ------|----------|----------|---------|---------|------|---------|------------------
            // 0     | 0        | 1        | 0       | 0       | 1    | 1       | Empty ✓
            // 0     | 1        | 1        | 0       | 0       | 1    | 1       | Writing, completes ✓
            // 3     | 0        | 1        | 0       | 3       | 1    | 1       | Room for 1 ✓
            // 3     | 1        | 1        | 0       | 3       | 1    | 1       | Writing, will be 4 ✓
            // 3     | 1        | 0        | 1       | 4       | 0    | 0       | Write stalled ✗
            // 4     | 0        | 0        | 0       | 4       | 0    | 0       | Full ✗
            //
            // This allows back-to-back accepts as long as writes complete immediately.
%000000     wire w_write_stalled = skid_wr_valid && !skid_wr_ready;
%000008     wire [2:0] pending_count = skid_count + {2'b0, w_write_stalled};
 000014     wire w_room_available = (pending_count < 3'(SKID_DEPTH));
        
            assign s_ready = w_room_available || w_draining_now;
        
            // Drain FIFO when upstream has data AND we can accept
 000012     wire w_drain_fifo = s_valid && s_ready;
        
            // Flop the drain signal to track data in flight
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_drain_ip <= 1'b0;
                end else begin
                    r_drain_ip <= w_drain_fifo;
                end
 000066     )
        
            // When r_drain_ip asserted, data arrived from FIFO this cycle → push to skid
            assign skid_wr_valid = r_drain_ip;
            assign skid_wr_data = s_data;  // Data is stable (registered FIFO output)
        
            //=========================================================================
            // Skid Buffer (handles all backpressure complexity)
            //=========================================================================
        
            gaxi_fifo_sync #(
                .MEM_STYLE(FIFO_AUTO),       // Let tool decide (SRL for small depth)
                .REGISTERED(0),              // No extra latency needed
                .DATA_WIDTH(DW),
                .DEPTH(SKID_DEPTH)
            ) u_skid_buffer (
                .axi_aclk       (clk),
                .axi_aresetn    (rst_n),
        
                // Write port (from glue logic)
                .wr_valid       (skid_wr_valid),
                .wr_ready       (skid_wr_ready),
                .wr_data        (skid_wr_data),
        
                // Read port (to consumer)
                .rd_valid       (m_valid),
                .rd_ready       (m_ready),
                .rd_data        (m_data),
        
                // Status
                .count          (skid_count)
            );
        
            //=========================================================================
            // Occupancy Tracking
            //=========================================================================
            // Total occupancy = data in flight (r_drain_ip) + data in skid buffer
            // Max = 1 (in flight) + SKID_DEPTH (in buffer) = 5 for SKID_DEPTH=4
            // assign occupancy = 3'(r_drain_ip) + skid_count;
            assign occupancy = skid_count;
        
            // Debug: Track occupancy changes and backpressure decisions
            `ifndef SYNTHESIS
%000008     logic [2:0] r_prev_occupancy;
 000172     always @(posedge clk) begin
 000172         r_prev_occupancy <= occupancy;
 000020         if (occupancy != r_prev_occupancy) begin
 000020             $display("BRIDGE @%t: occupancy %0d -> %0d (r_drain_ip=%0d, skid_count=%0d, s_valid=%0d, s_ready=%0d, m_valid=%0d, m_ready=%0d)",
 000020                     $time, r_prev_occupancy, occupancy, r_drain_ip, skid_count, s_valid, s_ready, m_valid, m_ready);
                end
        
                // Debug backpressure calculation when trying to write
 000053         if (s_valid) begin
 000053             $display("BRIDGE @%t: BACKPRESSURE CHECK: s_valid=%b s_ready=%b skid_count=%0d r_drain_ip=%b skid_wr_ready=%b skid_wr_valid=%b stalled=%b pending=%0d room=%b",
 000053                     $time, s_valid, s_ready, skid_count, r_drain_ip, skid_wr_ready, skid_wr_valid, w_write_stalled, pending_count, w_room_available);
                end
            end
            `endif
        
            //=========================================================================
            // Debug Outputs (for backward compatibility)
            //=========================================================================
            assign dbg_r_pending = r_drain_ip;
            assign dbg_r_out_valid = m_valid;
        
        endmodule : latency_bridge_beats
        
