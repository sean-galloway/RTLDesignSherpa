// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_cmd_delay
// Purpose: Align the DFI command stream with the write-data stream to satisfy
//          the a7ddrphy's write_latency=0 contract (wrdata CONCURRENT with the
//          WR command). pumice's wr_beat_sequencer only starts pulling write
//          data at WR-command-accept, so dfi_wrdata_en/wrdata emerge a FIXED
//          CMD_DELAY sys-cycles AFTER the command (command pipeline + pull
//          floor; measured = 5 for the nphases=2 / 300 MT/s config). We delay
//          the COMMAND bus (address/bank/ras/cas/we/cs/cke/odt) + rddata_en by
//          CMD_DELAY and pass wrdata/wrdata_en/mask through undelayed, so the
//          (delayed) WR command lands concurrent with its data. Delaying the
//          whole command bus uniformly preserves inter-command spacing
//          (tRCD/tRP/tMRD/tRFC), and delaying rddata_en with the RD command
//          keeps the read command<->rddata_en relationship intact.
//
//          CMD_DELAY=0 is a bit-exact passthrough (default / back-compat).
//
//          NOTE: this is a timing-alignment SHIM for the characterization
//          harness. The general controller fix is wr_beat_sequencer pre-pull
//          (start pulling at scheduler-select so wrdata is ready at command
//          time, eliminating the skew). See wr_beat_sequencer.sv header.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module dfi_cmd_delay #(
    parameter int DFI_ADDR_BUS_W = 26,
    parameter int DFI_BANK_BUS_W = 6,
    parameter int DFI_CTRL_BUS_W = 2,   // = DFI_RATE
    parameter int DFI_CS_BUS_W   = 2,   // = DFI_RATE
    parameter int DFI_RATE       = 2,
    parameter int CMD_DELAY      = 0    // sys-cycles to delay the command bus
) (
    input  logic                        mc_clk,
    input  logic                        mc_rst_n,

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

    // ----- command bus out (delayed) -----
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

    generate
        if (CMD_DELAY == 0) begin : g_passthru
            assign o_address   = i_address;
            assign o_bank      = i_bank;
            assign o_cas_n     = i_cas_n;
            assign o_ras_n     = i_ras_n;
            assign o_we_n      = i_we_n;
            assign o_cs_n      = i_cs_n;
            assign o_cke       = i_cke;
            assign o_odt       = i_odt;
            assign o_rddata_en = i_rddata_en;
        end else begin : g_delay
            // Shift registers, NOP-initialized so nothing spurious issues while
            // the pipeline fills (cs_n=1 deselected, ras/cas/we=1, cke=0 until
            // real traffic arrives — CKE is held by the controller anyway).
            logic [DFI_ADDR_BUS_W-1:0] r_address [CMD_DELAY];
            logic [DFI_BANK_BUS_W-1:0] r_bank    [CMD_DELAY];
            logic [DFI_CTRL_BUS_W-1:0] r_cas_n   [CMD_DELAY];
            logic [DFI_CTRL_BUS_W-1:0] r_ras_n   [CMD_DELAY];
            logic [DFI_CTRL_BUS_W-1:0] r_we_n    [CMD_DELAY];
            logic [DFI_CS_BUS_W-1:0]   r_cs_n    [CMD_DELAY];
            logic [DFI_CS_BUS_W-1:0]   r_cke     [CMD_DELAY];
            logic [DFI_CS_BUS_W-1:0]   r_odt     [CMD_DELAY];
            logic [DFI_RATE-1:0]       r_rddata_en [CMD_DELAY];

            `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
                if (`RST_ASSERTED(mc_rst_n)) begin
                    for (int i = 0; i < CMD_DELAY; i++) begin
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
                    for (int i = 1; i < CMD_DELAY; i++) begin
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

            assign o_address   = r_address[CMD_DELAY-1];
            assign o_bank      = r_bank[CMD_DELAY-1];
            assign o_cas_n     = r_cas_n[CMD_DELAY-1];
            assign o_ras_n     = r_ras_n[CMD_DELAY-1];
            assign o_we_n      = r_we_n[CMD_DELAY-1];
            assign o_cs_n      = r_cs_n[CMD_DELAY-1];
            assign o_cke       = r_cke[CMD_DELAY-1];
            assign o_odt       = r_odt[CMD_DELAY-1];
            assign o_rddata_en = r_rddata_en[CMD_DELAY-1];
        end
    endgenerate

endmodule : dfi_cmd_delay
