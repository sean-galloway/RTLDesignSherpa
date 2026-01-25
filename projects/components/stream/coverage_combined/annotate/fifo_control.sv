//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: fifo_control
        // Purpose: //   FIFO control logic for asynchronous FIFOs. Generates full/empty and almost-
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: fifo_control
        //==============================================================================
        // Description:
        //   FIFO control logic for asynchronous FIFOs. Generates full/empty and almost-
        //   full/almost-empty flags based on binary pointers that have been synchronized
        //   across clock domains. Supports both combinational (mux) and registered (flop)
        //   output modes for timing optimization.
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   ADDR_WIDTH:
        //     Description: Address width in bits for FIFO indexing
        //     Type: int
        //     Range: 1 to 16
        //     Default: 3
        //     Constraints: DEPTH must equal 2^ADDR_WIDTH (power of 2 depths only)
        //
        //   DEPTH:
        //     Description: FIFO depth (number of entries)
        //     Type: int
        //     Range: 2 to 65536
        //     Default: 16
        //     Constraints: Must be power of 2, must equal 2^ADDR_WIDTH
        //
        //   ALMOST_WR_MARGIN:
        //     Description: Almost-full threshold (entries from full)
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: wr_almost_full asserts when (used >= DEPTH - ALMOST_WR_MARGIN)
        //
        //   ALMOST_RD_MARGIN:
        //     Description: Almost-empty threshold (entries from empty)
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: rd_almost_empty asserts when (used <= ALMOST_RD_MARGIN)
        //
        //   REGISTERED:
        //     Description: Output register mode
        //     Type: int
        //     Range: 0 or 1
        //     Default: 0
        //     Constraints: 0 = Mux mode (combinational), 1 = Flop mode (registered for timing)
        //
        //   Derived Parameters (localparam - computed automatically):
        //     D: Alias for DEPTH
        //     AW: Alias for ADDR_WIDTH
        //     AFULL: Alias for ALMOST_WR_MARGIN (almost-full margin)
        //     AEMPTY: Alias for ALMOST_RD_MARGIN (almost-empty margin)
        //     AFT: Almost-full threshold (DEPTH - ALMOST_WR_MARGIN)
        //     AET: Almost-empty threshold (ALMOST_RD_MARGIN)
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - Designed for asynchronous FIFO applications
        //   - Assumes pointers are already synchronized to appropriate clock domains
        //   - Pointer width is ADDR_WIDTH+1 (extra bit for wrap-around detection)
        //   - REGISTERED=1 adjusts empty logic timing for registered FIFO output
        //   - Full/empty detection uses MSB XOR for wrap-around handling
        //   - Almost-full/almost-empty provide early warning for flow control
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - fifo_async_div2.sv - Async FIFO using this control module
        //   - fifo_async.sv - General async FIFO
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_fifo_control.py (tested via fifo_async* tests)
        //   Run: pytest val/common/test_fifo_async*.py -v
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        module fifo_control #(
            parameter int ADDR_WIDTH = 3,
            parameter int DEPTH = 16,
            parameter int ALMOST_WR_MARGIN = 1,
            parameter int ALMOST_RD_MARGIN = 1,
            parameter int REGISTERED = 0  // 0 = mux mode, 1 = flop mode
        ) (
            // clocks and resets
 000666     input  logic                    wr_clk,
%000002                                     wr_rst_n,
 000666                                     rd_clk,
%000002                                     rd_rst_n,
            // Pointers
%000000     input  logic [ADDR_WIDTH:0]     wr_ptr_bin,
%000000     input  logic [ADDR_WIDTH:0]     wdom_rd_ptr_bin,
%000000     input  logic [ADDR_WIDTH:0]     rd_ptr_bin,
%000000     input  logic [ADDR_WIDTH:0]     rdom_wr_ptr_bin,
%000000     output logic [ADDR_WIDTH:0]     count,
%000000     output logic                    wr_full,
%000000     output logic                    wr_almost_full,
%000002     output logic                    rd_empty,
%000002     output logic                    rd_almost_empty
        );
        
            localparam int D = DEPTH;
            localparam int AW = ADDR_WIDTH;
            localparam int AFULL = ALMOST_WR_MARGIN;
            localparam int AEMPTY = ALMOST_RD_MARGIN;
            localparam int AFT = D - AFULL;
            localparam int AET = AEMPTY;
        
%000000     logic w_wdom_ptr_xor;
%000000     logic w_rdom_ptr_xor;
%000000     logic w_wr_full_d, w_wr_almost_full_d;
%000002     logic w_rd_empty_d, w_rd_almost_empty_d;
            // Widen to [AW:0] to accommodate (AW+1)'(D) without truncation
%000000     logic [AW:0] w_almost_full_count, w_almost_empty_count;
        
            /////////////////////////////////////////////////////////////////////////
            // XOR the two upper bits of the pointers to for use in the full/empty equations
            assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
            assign w_rdom_ptr_xor = rd_ptr_bin[AW] ^ rdom_wr_ptr_bin[AW];
        
            /////////////////////////////////////////////////////////////////////////
            // Full signals
            assign w_wr_full_d = (w_wdom_ptr_xor && (wr_ptr_bin[AW-1:0] == wdom_rd_ptr_bin[AW-1:0]));
        
            // Fixed: Cast D to (AW+1)-bit width to prevent truncation at wraparound
            // For depth=16, AW=4: AW'(16) = 4'b0000 (wrong!), (AW+1)'(16) = 5'b10000 (correct!)
            assign w_almost_full_count = (w_wdom_ptr_xor) ?
                                ((AW+1)'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) :
                                (wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]);
        
            assign w_wr_almost_full_d = w_almost_full_count >= (AW+1)'(AFT);
        
 000339     always_ff @(posedge wr_clk, negedge wr_rst_n) begin
 000022         if (!wr_rst_n) begin
 000022             wr_full <= 'b0;
 000022             wr_almost_full <= 'b0;
 000207         end else begin
 000207             wr_full <= w_wr_full_d;
 000207             wr_almost_full <= w_wr_almost_full_d;
                end
            end
        
            /////////////////////////////////////////////////////////////////////////
            // Empty Signals - Mode-aware write pointer selection
%000000     logic [ADDR_WIDTH:0] w_wr_ptr_for_empty;
%000000     logic w_rdom_ptr_xor_for_empty;
        
            generate
                if (REGISTERED == 1) begin : gen_flop_mode
                    // FLOP mode: Use previous cycle's write pointer to match registered data timing
                    logic [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;
        
                    `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                if (`RST_ASSERTED(rd_rst_n)) begin
                            r_rdom_wr_ptr_bin_delayed <= '0;
                        end else begin
                            r_rdom_wr_ptr_bin_delayed <= rdom_wr_ptr_bin;
                        end
 000022             )
        
        
                    assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
                end else begin : gen_mux_mode
                    // MUX mode: Use current write pointer for immediate data availability
                    assign w_wr_ptr_for_empty = rdom_wr_ptr_bin;
                end
            endgenerate
        
            // Calculate XOR using the mode-appropriate write pointer
            assign w_rdom_ptr_xor_for_empty = rd_ptr_bin[AW] ^ w_wr_ptr_for_empty[AW];
        
            // Empty detection using mode-appropriate write pointer
            assign w_rd_empty_d = (!w_rdom_ptr_xor_for_empty &&
                                    (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]));
        
            /////////////////////////////////////////////////////////////////////////
            // Almost Empty calculation (uses standard timing regardless of mode)
            // Fixed: Cast D to (AW+1)-bit width to prevent truncation at wraparound
            assign w_almost_empty_count = (w_rdom_ptr_xor) ?
                                ((AW+1)'(D) - rd_ptr_bin[AW-1:0] + rdom_wr_ptr_bin[AW-1:0]) :
                                (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);
        
            /* verilator lint_off CMPCONST */
            assign w_rd_almost_empty_d = w_almost_empty_count <= (AW+1)'(AET);
            /* verilator lint_on CMPCONST */
        
            // Fixed: Cast D to (AW+1)-bit width to prevent truncation (count is [AW:0])
            // For depth=16, AW=4: AW'(16) = 4'b0000 (wrong!), (AW+1)'(16) = 5'b10000 (correct!)
%000000     logic [ADDR_WIDTH:0]     w_count, r_count;
        
            assign w_count = (w_rdom_ptr_xor) ?
                        (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0] + (AW+1)'(D)) :
                        (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);
        
            assign count = (REGISTERED == 1) ? r_count : w_count;
        
 000339     always_ff @(posedge rd_clk, negedge rd_rst_n) begin
 000022         if (!rd_rst_n) begin
 000022             rd_empty <= 'b1;
 000022             rd_almost_empty <= 'b0;
 000022             r_count <= 'b0;
 000207         end else begin
 000207             rd_empty <= w_rd_empty_d;
 000207             rd_almost_empty <= w_rd_almost_empty_d;
 000207             r_count <= w_count;
                end
            end
        
        endmodule : fifo_control
        
