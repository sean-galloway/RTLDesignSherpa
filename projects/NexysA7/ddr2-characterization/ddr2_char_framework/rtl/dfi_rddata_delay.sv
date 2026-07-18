// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_rddata_delay
// Purpose: Realign the a7ddrphy read-DATA bus with its read-VALID strobe. The
//          on-silicon ILA proved the a7ddrphy presents dfi_rddata a fixed
//          ~read_latency sys-cycles BEFORE its own dfi_rddata_valid: the correct
//          read-back data sits on dfi_rddata coincident with dfi_rddata_en, but
//          dfi_rddata_valid (which pumice's rd_cl_aligner uses to latch) asserts
//          later, by which point dfi_rddata has returned to 0 -> the controller
//          captures zeros. Delaying dfi_rddata by `sel_i` sys-cycles makes the
//          (delayed) data land concurrent with the late valid, so the capture
//          grabs the right beats. This is the READ mirror of dfi_cmd_delay's
//          write-side alignment; both are a7ddrphy-integration shims, not DRAM
//          JEDEC timings, so pumice stays PHY-agnostic (it correctly captures on
//          dfi_rddata_valid). rddata_valid is passed through here UNCHANGED — it
//          is the timing anchor we align TO.
//
//          RUNTIME-TUNABLE: `sel_i` (0..MAX_DELAY) comes from a CSR (harness
//          DFI_TUNING.rddata_delay), swept live over UART with no rebuild.
//          sel_i=0 is a bit-exact passthrough (default -> no behavior change).
//          Set sel_i = a7ddrphy read_latency (~8 for DDR2/CL3/nphases=2). Change
//          only while idle. See project note: project_ddr2_ila_read_valid_skew.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module dfi_rddata_delay #(
    parameter int DFI_DATA_WIDTH = 64,
    parameter int MAX_DELAY      = 15,  // max runtime-selectable read-data delay
    parameter int SEL_W          = $clog2(MAX_DELAY + 1)
) (
    input  logic                        mc_clk,
    input  logic                        mc_rst_n,

    // ----- runtime delay select (CSR-driven), 0..MAX_DELAY -----
    input  logic [SEL_W-1:0]            sel_i,

    // ----- read-data in (from a7ddrphy) -----
    input  logic [DFI_DATA_WIDTH-1:0]   i_rddata,

    // ----- read-data out (delayed by sel_i, to controller) -----
    output logic [DFI_DATA_WIDTH-1:0]   o_rddata
);

    // MAX_DELAY-deep shift register, zero-initialized.
    logic [DFI_DATA_WIDTH-1:0] r_rddata [MAX_DELAY];

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int i = 0; i < MAX_DELAY; i++) begin
                r_rddata[i] <= '0;
            end
        end else begin
            r_rddata[0] <= i_rddata;
            for (int i = 1; i < MAX_DELAY; i++) begin
                r_rddata[i] <= r_rddata[i-1];
            end
        end
    end)

    // Runtime tap select: sel_i=0 -> passthrough; sel_i=k -> k-deep delayed.
    // With MAX_DELAY = 2**SEL_W-1 the full sel_i range is in-bounds (index
    // sel_i-1 in [0, MAX_DELAY-1]), so no clamp is needed. If a caller lowers
    // MAX_DELAY below 2**SEL_W-1, add a clamp on sel_i here.
    assign o_rddata = (sel_i == 0) ? i_rddata : r_rddata[sel_i-1];

endmodule : dfi_rddata_delay
