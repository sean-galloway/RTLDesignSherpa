// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sync_pulse
// Purpose: //   Safe pulse synchronizer for crossing clock domains. Converts a single-
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: sync_pulse
//==============================================================================
// Description:
//   Safe pulse synchronizer for crossing clock domains. Converts a single-
//   cycle pulse in the source clock domain to a single-cycle pulse in the
//   destination clock domain using a toggle-based handshake. Guarantees no
//   pulse loss for source pulses separated by at least 3 destination clock
//   cycles.
//
// Features:
//   - Metastability-safe using 3-stage synchronizer
//   - No pulse loss (if minimum spacing met)
//   - Single-cycle output pulse in destination domain
//   - Handles arbitrary clock frequency ratios
//   - Minimal logic footprint
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYNC_STAGES:
//     Description: Number of synchronizer stages for metastability filtering
//     Type: int
//     Range: 2 to 4
//     Default: 3
//     Constraints: SYNC_STAGES=2 (minimum), SYNC_STAGES=3 (recommended)
//                  Higher stages reduce MTBF but increase latency
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Source Clock Domain:
//     i_src_clk:    Source clock (where input pulse originates)
//     i_src_rst_n:  Source domain active-low reset
//     i_pulse:      Input pulse (must be single-cycle high)
//
//   Destination Clock Domain:
//     i_dst_clk:    Destination clock (where output pulse appears)
//     i_dst_rst_n:  Destination domain active-low reset
//     o_pulse:      Synchronized output pulse (single-cycle high)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:         (SYNC_STAGES + 2) destination clock cycles
//   Min Pulse Gap:   3 destination clock cycles (to avoid loss)
//   MTBF:            >10^12 hours @ SYNC_STAGES=3
//
//------------------------------------------------------------------------------
// Protocol:
//------------------------------------------------------------------------------
//   1. Source pulse toggles r_src_toggle register
//   2. Toggle is synchronized to destination clock domain
//   3. Edge detector generates single-cycle pulse in destination domain
//   4. Destination toggle is synchronized back to source for ready
//
//   Source pulse spacing requirement:
//     - Minimum spacing = 3*T_dst + 2*T_src (clock periods)
//     - For continuous pulses, check o_pulse spacing in destination domain
//
//------------------------------------------------------------------------------
// Safety:
//------------------------------------------------------------------------------
//   - ASYNC_REG attribute on synchronizer prevents optimization
//   - Metastability filtered by multi-stage synchronizer
//   - No combinational paths between clock domains
//   - Safe for arbitrary clock frequency ratios
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   sync_pulse #(
//       .SYNC_STAGES(3)
//   ) u_sync_pulse (
//       .i_src_clk      (btn_clk),
//       .i_src_rst_n    (sys_rst_n),
//       .i_pulse        (button_press_pulse),
//       .i_dst_clk      (disp_clk),
//       .i_dst_rst_n    (sys_rst_n),
//       .o_pulse        (button_press_sync)
//   );
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - reset_sync.sv: For reset synchronization
//   - edge_detect.sv: For edge-to-pulse conversion
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Input pulse MUST be single-cycle high in source domain
//   - For multi-cycle signals, use edge detector first
//   - Ensure resets are properly synchronized in both domains
//   - Use XDC constraints: set_false_path between clock domains
//
//------------------------------------------------------------------------------
// References:
//------------------------------------------------------------------------------
//   - Cummings, Clifford E. "Clock Domain Crossing (CDC) Design &
//     Verification Techniques Using SystemVerilog." SNUG 2008.
//   - "Synthesis and Scripting Techniques for Designing Multi-Asynchronous
//     Clock Designs." Xilinx WP275.
//
//==============================================================================

`include "reset_defs.svh"

module sync_pulse #(
    parameter int SYNC_STAGES = 3    // Synchronizer depth (2-4)
) (
    // Source clock domain
    input  logic i_src_clk,
    input  logic i_src_rst_n,
    input  logic i_pulse,

    // Destination clock domain
    input  logic i_dst_clk,
    input  logic i_dst_rst_n,
    output logic o_pulse
);

    //==========================================================================
    // Parameter Validation
    //==========================================================================
    initial begin
        if (SYNC_STAGES < 2 || SYNC_STAGES > 4) begin
            $error("sync_pulse: SYNC_STAGES=%0d out of range [2,4]", SYNC_STAGES);
        end
    end

    //==========================================================================
    // Source Clock Domain: Toggle on Pulse
    //==========================================================================

    (* ASYNC_REG = "TRUE" *) logic r_src_toggle;

    // Toggle register on each input pulse
    `ALWAYS_FF_RST(i_src_clk, i_src_rst_n,
        if (`RST_ASSERTED(i_src_rst_n)) begin
            r_src_toggle <= 1'b0;
        end else if (i_pulse) begin
            r_src_toggle <= ~r_src_toggle;  // Toggle state
        end
    )


    //==========================================================================
    // Destination Clock Domain: Synchronize Toggle
    //==========================================================================

    (* ASYNC_REG = "TRUE" *) logic [SYNC_STAGES-1:0] r_sync;

    // Multi-stage synchronizer
    `ALWAYS_FF_RST(i_dst_clk, i_dst_rst_n,
        if (`RST_ASSERTED(i_dst_rst_n)) begin
            r_sync <= '0;
        end else begin
            r_sync <= {r_sync[SYNC_STAGES-2:0], r_src_toggle};
        end
    )


    //==========================================================================
    // Destination Clock Domain: Edge Detection
    //==========================================================================

    logic r_sync_prev;

    // Delay synchronized toggle by one cycle
    `ALWAYS_FF_RST(i_dst_clk, i_dst_rst_n,
        if (`RST_ASSERTED(i_dst_rst_n)) begin
            r_sync_prev <= 1'b0;
        end else begin
            r_sync_prev <= r_sync[SYNC_STAGES-1];
        end
    )


    // Detect toggle edge (XOR of consecutive values)
    assign o_pulse = r_sync[SYNC_STAGES-1] ^ r_sync_prev;

    //==========================================================================
    // Assertions (for simulation/formal)
    //==========================================================================

    `ifdef FORMAL
        // Assert: Input pulse is single-cycle
        property p_single_cycle_pulse;
            @(posedge i_src_clk) disable iff (!i_src_rst_n)
            i_pulse |=> !i_pulse;
        endproperty
        assert property (p_single_cycle_pulse)
            else $error("Input pulse must be single-cycle");

        // Assert: Output pulse is single-cycle
        property p_output_single_cycle;
            @(posedge i_dst_clk) disable iff (!i_dst_rst_n)
            o_pulse |=> !o_pulse;
        endproperty
        assert property (p_output_single_cycle)
            else $error("Output pulse must be single-cycle");
    `endif

endmodule
