// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_cmd_delay
// Purpose: Align the DFI command stream with the write-data stream to satisfy
//          the a7ddrphy's write_latency=0 contract (wrdata CONCURRENT with the
//          WR command). pumice's wr_beat_sequencer only starts pulling write
//          data at WR-command-accept, so dfi_wrdata_en/wrdata emerge a fixed
//          few sys-cycles AFTER the command. We delay the COMMAND bus
//          (address/bank/ras/cas/we/cs/cke/odt) + rddata_en by `sel_i`
//          sys-cycles and pass wrdata/wrdata_en/mask through undelayed, so the
//          (delayed) WR command lands concurrent with its data.
//
//          RUNTIME-TUNABLE: `sel_i` (0..MAX_DELAY) comes from a CSR
//          (harness DFI_TUNING.cmd_delay), so the alignment is swept live over
//          UART with no rebuild — like a production controller. sel_i=0 is a
//          bit-exact passthrough. Change sel_i only while idle (mid-burst
//          changes glitch the pipeline). Delaying the whole command bus
//          uniformly preserves inter-command spacing (tRCD/tRP/tMRD/tRFC);
//          delaying rddata_en with the RD command preserves read timing.
//
//          NOTE: timing-alignment shim for the characterization harness. The
//          general controller fix is wr_beat_sequencer pre-pull.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module dfi_cmd_delay #(
    parameter int DFI_ADDR_BUS_W = 26,
    parameter int DFI_BANK_BUS_W = 6,
    parameter int DFI_CTRL_BUS_W = 2,   // = DFI_RATE
    parameter int DFI_CS_BUS_W   = 2,   // = DFI_RATE
    parameter int DFI_RATE       = 2,
    parameter int MAX_DELAY      = 8,   // max runtime-selectable command delay
    parameter int SEL_W          = $clog2(MAX_DELAY + 1)
) (
    input  logic                        mc_clk,
    input  logic                        mc_rst_n,

    // ----- runtime delay select (CSR-driven), 0..MAX_DELAY -----
    input  logic [SEL_W-1:0]            sel_i,

    // ----- command bus in (from controller) -----
    input  logic [DFI_ADDR_BUS_W-1:0]   i_address,
    input  logic [DFI_BANK_BUS_W-1:0]   i_bank,
    input  logic [DFI_CTRL_BUS_W-1:0]   i_cas_n,
    input  logic [DFI_CTRL_BUS_W-1:0]   i_ras_n,
    input  logic [DFI_CTRL_BUS_W-1:0]   i_we_n,
    input  logic [DFI_CS_BUS_W-1:0]     i_cs_n,
    input  logic [DFI_CS_BUS_W-1:0]     i_cke,
    input  logic [DFI_CS_BUS_W-1:0]     i_odt,
    input  logic [DFI_RATE-1:0]         i_rddata_en,

    // ----- command bus out (delayed by sel_i) -----
    output logic [DFI_ADDR_BUS_W-1:0]   o_address,
    output logic [DFI_BANK_BUS_W-1:0]   o_bank,
    output logic [DFI_CTRL_BUS_W-1:0]   o_cas_n,
    output logic [DFI_CTRL_BUS_W-1:0]   o_ras_n,
    output logic [DFI_CTRL_BUS_W-1:0]   o_we_n,
    output logic [DFI_CS_BUS_W-1:0]     o_cs_n,
    output logic [DFI_CS_BUS_W-1:0]     o_cke,
    output logic [DFI_CS_BUS_W-1:0]     o_odt,
    output logic [DFI_RATE-1:0]         o_rddata_en
);

    // MAX_DELAY-deep shift registers, NOP-initialized (cs_n=1 deselected,
    // ras/cas/we=1) so nothing spurious issues while the pipeline fills.
    logic [DFI_ADDR_BUS_W-1:0] r_address [MAX_DELAY];
    logic [DFI_BANK_BUS_W-1:0] r_bank    [MAX_DELAY];
    logic [DFI_CTRL_BUS_W-1:0] r_cas_n   [MAX_DELAY];
    logic [DFI_CTRL_BUS_W-1:0] r_ras_n   [MAX_DELAY];
    logic [DFI_CTRL_BUS_W-1:0] r_we_n    [MAX_DELAY];
    logic [DFI_CS_BUS_W-1:0]   r_cs_n    [MAX_DELAY];
    logic [DFI_CS_BUS_W-1:0]   r_cke     [MAX_DELAY];
    logic [DFI_CS_BUS_W-1:0]   r_odt     [MAX_DELAY];
    logic [DFI_RATE-1:0]       r_rddata_en [MAX_DELAY];

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int i = 0; i < MAX_DELAY; i++) begin
                r_address[i]   <= '0;
                r_bank[i]      <= '0;
                r_cas_n[i]     <= '1;
                r_ras_n[i]     <= '1;
                r_we_n[i]      <= '1;
                r_cs_n[i]      <= '1;   // deselected NOP
                r_cke[i]       <= '0;
                r_odt[i]       <= '0;
                r_rddata_en[i] <= '0;
            end
        end else begin
            r_address[0]   <= i_address;
            r_bank[0]      <= i_bank;
            r_cas_n[0]     <= i_cas_n;
            r_ras_n[0]     <= i_ras_n;
            r_we_n[0]      <= i_we_n;
            r_cs_n[0]      <= i_cs_n;
            r_cke[0]       <= i_cke;
            r_odt[0]       <= i_odt;
            r_rddata_en[0] <= i_rddata_en;
            for (int i = 1; i < MAX_DELAY; i++) begin
                r_address[i]   <= r_address[i-1];
                r_bank[i]      <= r_bank[i-1];
                r_cas_n[i]     <= r_cas_n[i-1];
                r_ras_n[i]     <= r_ras_n[i-1];
                r_we_n[i]      <= r_we_n[i-1];
                r_cs_n[i]      <= r_cs_n[i-1];
                r_cke[i]       <= r_cke[i-1];
                r_odt[i]       <= r_odt[i-1];
                r_rddata_en[i] <= r_rddata_en[i-1];
            end
        end
    end)

    // Runtime tap select: sel_i=0 -> passthrough; sel_i=k -> k-deep delayed.
    // Clamp to MAX_DELAY so an out-of-range CSR value can't index past the reg.
    logic [SEL_W-1:0] w_sel;
    assign w_sel = (sel_i > SEL_W'(MAX_DELAY)) ? SEL_W'(MAX_DELAY) : sel_i;

    assign o_address   = (w_sel == 0) ? i_address   : r_address[w_sel-1];
    assign o_bank      = (w_sel == 0) ? i_bank      : r_bank[w_sel-1];
    assign o_cas_n     = (w_sel == 0) ? i_cas_n     : r_cas_n[w_sel-1];
    assign o_ras_n     = (w_sel == 0) ? i_ras_n     : r_ras_n[w_sel-1];
    assign o_we_n      = (w_sel == 0) ? i_we_n      : r_we_n[w_sel-1];
    assign o_cs_n      = (w_sel == 0) ? i_cs_n      : r_cs_n[w_sel-1];
    assign o_cke       = (w_sel == 0) ? i_cke       : r_cke[w_sel-1];
    assign o_odt       = (w_sel == 0) ? i_odt       : r_odt[w_sel-1];
    assign o_rddata_en = (w_sel == 0) ? i_rddata_en : r_rddata_en[w_sel-1];

endmodule : dfi_cmd_delay
