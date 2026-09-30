// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: mode_register
// Purpose: Per-rank Mode Register shadow + live decode of MR-derived
//          timing values for use by the rest of the controller.
//
//          On `mr_we_i`, write `mr_data_i` into shadow MR[`mr_index_i`]
//          for `mr_rank_i`. The init_sequencer drives this during
//          DRAM bring-up; a CSR/APB hot-update path drives it later.
//
//          Live decoded outputs:
//            cl_o   : CAS read latency  (DDR2 MR0[6:4], LPDDR2 MR2[3:0])
//            cwl_o  : CAS write latency (DDR2 = CL-1, LPDDR2 MR2[7:4])
//            bl_o   : burst length      (4, 8, or 16 for LPDDR2)
//            al_o   : additive latency  (DDR2 MR1[5:3], LPDDR2: 0)
//            drv_o  : output drive strength (informational; not used)
//            odt_o  : ODT rule          (DDR2 MR1[6,2]; LPDDR2: 0)
//
// v2 status:
//   * MAX_MR_IDX=17 covers both DDR2 (MR0..MR3) and LPDDR2 (MR0..MR16).
//   * LPDDR2 BL decode clips BL16 → BL8 because bl_o is 4-bit. v3 widens
//     bl_o to [4:0] + updates the 3 downstream macros that consume it.
//
// v2 / v3 TODO:
//   * mr_req_o always tied 0 — no hot MR updates issued via the
//     scheduler. Lands when the APB CSR slave provides a write-during-
//     traffic path and the quiet-point handshake is implemented.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scoria_mode_register
    import scoria_pkg::*;
#(
    parameter int NUM_RANKS  = 1,
    parameter int MAX_MR_IDX = 17,   // 0..16; LPDDR2 supports up to MR16
    parameter int RKW        = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  memtype_e             memtype_i,

    // ----- CSR / init-sequencer write port -----
    input  logic                 mr_we_i,
    input  logic [4:0]           mr_index_i,
    input  logic [15:0]          mr_data_i,
    input  logic [RKW-1:0]       mr_rank_i,

    // ----- request channel to scheduler (v1: unused) -----
    output logic                 mr_req_o,
    input  logic                 mr_grant_i,
    output logic [4:0]           mr_req_index_o,
    output logic [15:0]          mr_req_data_o,
    output logic [RKW-1:0]       mr_req_rank_o,

    // ----- live decoded values (driven from rank 0) -----
    output logic [3:0]           cl_o,
    output logic [3:0]           cwl_o,
    output logic [3:0]           bl_o,
    output logic [3:0]           al_o,
    output logic [1:0]           drv_strength_o,
    output logic [1:0]           odt_o,
    // DDR3 additions
    output logic [4:0]           wr_o,        // write recovery, MR0[11:9]
    output logic                 wrlvl_en_o   // MR1[7]: DRAM is in write-leveling mode
);

    //=========================================================================
    // Shadow MRs — one bank of MRs per rank.
    //=========================================================================
    logic [15:0] r_mr_shadow [NUM_RANKS][MAX_MR_IDX];

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned i = 0; i < MAX_MR_IDX; i++) begin
                    r_mr_shadow[k][i] <= 16'h0000;
                end
            end
        end else begin
            if (mr_we_i && mr_index_i < 5'(MAX_MR_IDX)) begin
                r_mr_shadow[mr_rank_i][mr_index_i] <= mr_data_i;
            end
        end
    end)

    //=========================================================================
    // Live decode from rank 0 (multi-rank designs must use matching MR
    // values across ranks; mixed MR per rank is unusual and is a TODO).
    //=========================================================================
    logic [15:0] w_mr0;
    logic [15:0] w_mr1;
    logic [15:0] w_mr2;
    assign w_mr0 = r_mr_shadow[0][0];
    assign w_mr1 = r_mr_shadow[0][1];
    assign w_mr2 = r_mr_shadow[0][2];

    // Combinational next-cycle values for every decoded output.
    logic [3:0] w_cl;
    logic [3:0] w_cwl;
    logic [3:0] w_bl;
    logic [3:0] w_al;
    logic [1:0] w_drv;
    logic [1:0] w_odt;
    logic [4:0] w_wr;
    logic       w_wrlvl_en;

    //=========================================================================
    // DDR3 / LPDDR3 mode-register field map
    //=========================================================================
    // From JESD79-3F Figure 9 (MR0), Figure 11 (MR1), Figure 12 (MR2):
    //
    //   MR0[1:0]   BL              MR1[0]     DLL enable
    //   MR0[2]     CL extension    MR1[4:3]   AL
    //   MR0[3]     read burst type MR1[7]     WRITE LEVELING ENABLE
    //   MR0[6:4]   CL              MR1[9,6,2] Rtt_Nom
    //   MR0[7]     test mode       MR1[1,5]   output driver impedance
    //   MR0[8]     DLL reset       MR2[2:0]   PASR
    //   MR0[11:9]  write recovery  MR2[5:3]   CWL
    //   MR0[12]    precharge-PD    MR2[6]     ASR
    //                              MR2[7]     SRT
    //
    // IMPORTANT -- a spec inconsistency, resolved deliberately. JESD79-3F
    // section 3.4.2.2 states in prose that "CAS Latency is defined by MR0
    // (bits A9-A11)". That contradicts its own Figure 9, where A11:A9 holds
    // WRITE RECOVERY -- and the figure is self-consistent, because the values
    // tabulated against A11:A9 are 16/5/6/7/8/10/12, which are write-recovery
    // cycle counts and cannot be CAS latencies. This module follows the
    // FIGURE: CL at MR0[6:4], WR at MR0[11:9]. Recorded here because the
    // next reader will find the prose and think this is a bug.

    // BL -- DDR3: MR0[1:0] (00 = BL8 fixed, 01 = on-the-fly, 10 = BC4 fixed).
    //       LPDDR3 keeps LPDDR2's MR1[2:0] encoding.
    always_comb begin
        w_bl = 4'd8;
        if (memtype_i == MEMTYPE_DDR3) begin
            unique case (w_mr0[1:0])
                2'b00:   w_bl = 4'd8;   // fixed BL8
                2'b01:   w_bl = 4'd8;   // BC4 or BL8 on the fly; BL8 unless A12 says otherwise
                2'b10:   w_bl = 4'd4;   // fixed BC4
                default: w_bl = 4'd8;
            endcase
        end else begin
            unique case (w_mr1[2:0])
                3'b010:  w_bl = 4'd4;
                3'b011:  w_bl = 4'd8;
                3'b100:  w_bl = 4'd8;   // BL16 clips to 8; bl_o is 4-bit
                default: w_bl = 4'd8;
            endcase
        end
    end

    // CL -- DDR3: MR0[6:4] encodes CL-4 for the commodity range (001 -> 5 ...
    // 111 -> 11), with MR0[2] as the +8 extension used by the fast bins.
    // LPDDR3: RL from the MR2[3:0] RL&WL enum, inherited from LPDDR2.
    logic [3:0] w_lp_rl, w_lp_wl;
    always_comb begin
        unique case (w_mr2[3:0])
            4'b0001: begin w_lp_rl = 4'd3; w_lp_wl = 4'd1; end
            4'b0010: begin w_lp_rl = 4'd4; w_lp_wl = 4'd2; end
            4'b0011: begin w_lp_rl = 4'd5; w_lp_wl = 4'd2; end
            4'b0100: begin w_lp_rl = 4'd6; w_lp_wl = 4'd3; end
            4'b0101: begin w_lp_rl = 4'd7; w_lp_wl = 4'd4; end
            4'b0110: begin w_lp_rl = 4'd8; w_lp_wl = 4'd4; end
            default: begin w_lp_rl = 4'd3; w_lp_wl = 4'd1; end
        endcase
    end

    always_comb begin
        if (memtype_i == MEMTYPE_DDR3) begin
            w_cl = (w_mr0[6:4] == 3'b000) ? 4'd5
                 : (4'(w_mr0[6:4]) + 4'd4 + (w_mr0[2] ? 4'd8 : 4'd0));
        end else begin
            w_cl = w_lp_rl;
        end
    end

    // CWL -- DDR3: MR2[5:3] encodes CWL-5 (000 -> 5 ... 111 -> 12). DDR3 does
    // NOT tie CWL to CL the way DDR2 does (CWL = CL-1), so this is a real
    // decode rather than an arithmetic shortcut. LPDDR3: WL from the enum.
    always_comb begin
        if (memtype_i == MEMTYPE_DDR3) begin
            w_cwl = 4'(w_mr2[5:3]) + 4'd5;
        end else begin
            w_cwl = w_lp_wl;
        end
    end

    // AL -- DDR3: MR1[4:3]; 00 = disabled, 01 = CL-1, 10 = CL-2, 11 reserved.
    always_comb begin
        if (memtype_i == MEMTYPE_DDR3) begin
            unique case (w_mr1[4:3])
                2'b01:   w_al = (w_cl > 4'd1) ? (w_cl - 4'd1) : 4'd0;
                2'b10:   w_al = (w_cl > 4'd2) ? (w_cl - 4'd2) : 4'd0;
                default: w_al = 4'd0;
            endcase
        end else begin
            w_al = 4'd0;   // LPDDR3 has no additive latency
        end
    end

    // Write recovery -- DDR3 MR0[11:9]. 000 is 16, not 4: the encoding is not
    // monotonic and must be a table.
    always_comb begin
        if (memtype_i == MEMTYPE_DDR3) begin
            unique case (w_mr0[11:9])
                3'b000:  w_wr = 5'd16;
                3'b001:  w_wr = 5'd5;
                3'b010:  w_wr = 5'd6;
                3'b011:  w_wr = 5'd7;
                3'b100:  w_wr = 5'd8;
                3'b101:  w_wr = 5'd10;
                3'b110:  w_wr = 5'd12;
                default: w_wr = 5'd14;
            endcase
        end else begin
            w_wr = 5'd0;   // LPDDR3 carries tWR in its own MR / CSR
        end
    end

    // Write leveling enable -- MR1[7], DDR3 only. JESD79-3F: the DRAM enters
    // write-leveling mode when A7 in MR1 is high and exits when it is low.
    // This is the signal scoria_wrlvl_ifc gates its handshake on.
    assign w_wrlvl_en = (memtype_i == MEMTYPE_DDR3) && w_mr1[7];

    // Drive strength + ODT -- informational. DDR3 spreads Rtt_Nom across
    // MR1[9], MR1[6] and MR1[2]; only the low two are surfaced here, which is
    // all the DDR2 port width allowed and all any consumer reads today.
    assign w_drv = (memtype_i == MEMTYPE_DDR3) ? {w_mr1[5], w_mr1[1]} : 2'b00;
    assign w_odt = (memtype_i == MEMTYPE_DDR3) ? {w_mr1[6], w_mr1[2]} : 2'b00;

    //=========================================================================
    // Output registers — strict "every port is Q of a flop".
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            cl_o           <= 4'd0;
            cwl_o          <= 4'd0;
            bl_o           <= 4'd4;
            al_o           <= 4'd0;
            drv_strength_o <= 2'd0;
            odt_o          <= 2'd0;
            wr_o           <= 5'd0;
            wrlvl_en_o     <= 1'b0;
        end else begin
            cl_o           <= w_cl;
            cwl_o          <= w_cwl;
            bl_o           <= w_bl;
            al_o           <= w_al;
            drv_strength_o <= w_drv;
            odt_o          <= w_odt;
            wr_o           <= w_wr;
            wrlvl_en_o     <= w_wrlvl_en;
        end
    end)

    //=========================================================================
    // mr_req channel — unused in v1, but still flopped for consistency.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            mr_req_o       <= 1'b0;
            mr_req_index_o <= '0;
            mr_req_data_o  <= '0;
            mr_req_rank_o  <= '0;
        end else begin
            mr_req_o       <= 1'b0;
            mr_req_index_o <= '0;
            mr_req_data_o  <= '0;
            mr_req_rank_o  <= '0;
        end
    end)

    wire unused_v1 = |{ mr_grant_i, w_mr0[15:7], w_mr1[15:7],
                        w_mr2[15:8] };

endmodule : scoria_mode_register
