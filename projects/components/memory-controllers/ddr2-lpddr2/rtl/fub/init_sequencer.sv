// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: init_sequencer
// Purpose: Post-reset DRAM bring-up sequencer.
//
//          Sequence (DDR2 simplified):
//            1. Assert dfi_init_start_o; wait for dfi_init_complete_i
//               (the PHY runs its own init dance — DLL lock, training,
//               …).
//            2. Drive MR loads in JEDEC order: MR2, MR3, MR1, MR0
//               via the mode_register write port.
//            3. Drive ZQCL once (DDR3+ only; we issue zqcl_req_o for
//               parity with the wider design but accept any grant).
//            4. Assert init_done_o = 1.
//
//          init_busy_o = 1 during steps 1..3; the scheduler uses this
//          to gate all normal-traffic commands.
//
// v1 (TODO):
//   * Real MR data values are hard-coded placeholders here. A future
//     CSR/APB front-end should program the desired MR values into
//     scratch regs and have init_sequencer read them.
//   * LPDDR2 init differs significantly (MR loads via CA bus,
//     ZQ Init instead of ZQCL). v1 only handles DDR2 init flow.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module init_sequencer
    import ddr2_lpddr2_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  memtype_e    memtype_i,

    // ----- DFI status -----
    output logic        dfi_init_start_o,
    input  logic        dfi_init_complete_i,

    // ----- MR-sequenced write port (mux'd with CSR by core_macro) -----
    output logic        mr_seq_we_o,
    output logic [4:0]  mr_seq_index_o,
    output logic [15:0] mr_seq_data_o,
    output logic        zqcl_req_o,
    input  logic        zqcl_grant_i,

    // ----- status -----
    output logic        init_busy_o,
    output logic        init_done_o
);

    //=========================================================================
    // FSM states
    //=========================================================================
    typedef enum logic [3:0] {
        S_RESET     = 4'd0,
        S_DFI_INIT  = 4'd1,    // wait for PHY init complete
        S_MR_MR2    = 4'd2,    // load MR2
        S_MR_MR3    = 4'd3,
        S_MR_MR1    = 4'd4,
        S_MR_MR0    = 4'd5,
        S_ZQCL      = 4'd6,    // issue ZQ calibration
        S_DONE      = 4'd7
    } state_e;

    state_e r_state;

    //=========================================================================
    // Default MR values for DDR2 (placeholder programming):
    //   MR0: BL=4 (010), CL=5 (101), tWR=4 (010), DLL_RESET=1
    //   MR1: AL=0, ODS=normal, Rtt=disabled, DLL_EN=1
    //   MR2: SRT=0, ASR=0 (basic config)
    //   MR3: reserved (zero)
    //
    // TODO: drive these from CSR scratch regs so software can override.
    //=========================================================================
    localparam logic [15:0] DDR2_MR0_DEFAULT =
        // [12]=PD, [11:9]=tWR(010=4), [8]=DLL_RESET, [7]=test_mode,
        // [6:4]=CL(101=5), [3]=BT, [2:0]=BL(010=4)
        16'h0152;
    localparam logic [15:0] DDR2_MR1_DEFAULT =
        // [12]=Qoff, [11]=RDQS, [10]=DQS#, [9:7]=OCD, [6,2]=Rtt,
        // [5:3]=AL(000=0), [1]=ODS, [0]=DLL_EN(0=enable)
        16'h0000;
    localparam logic [15:0] DDR2_MR2_DEFAULT = 16'h0000;
    localparam logic [15:0] DDR2_MR3_DEFAULT = 16'h0000;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state <= S_RESET;
        end else begin
            unique case (r_state)
                S_RESET:    r_state <= S_DFI_INIT;
                S_DFI_INIT: if (dfi_init_complete_i) r_state <= S_MR_MR2;
                S_MR_MR2:   r_state <= S_MR_MR3;
                S_MR_MR3:   r_state <= S_MR_MR1;
                S_MR_MR1:   r_state <= S_MR_MR0;
                S_MR_MR0:   r_state <= S_ZQCL;
                S_ZQCL:     if (zqcl_grant_i) r_state <= S_DONE;
                S_DONE:     r_state <= S_DONE;     // stay here
                default:    r_state <= S_RESET;
            endcase
        end
    end)

    //=========================================================================
    // Next-cycle decoded outputs (combinational on r_state).
    //=========================================================================
    logic        w_mr_seq_we;
    logic [4:0]  w_mr_seq_index;
    logic [15:0] w_mr_seq_data;

    always_comb begin
        w_mr_seq_we    = 1'b0;
        w_mr_seq_index = 5'd0;
        w_mr_seq_data  = 16'd0;
        unique case (r_state)
            S_MR_MR2: begin
                w_mr_seq_we    = 1'b1;
                w_mr_seq_index = 5'd2;
                w_mr_seq_data  = (memtype_i == MEMTYPE_DDR2)
                               ? DDR2_MR2_DEFAULT : 16'd0;
            end
            S_MR_MR3: begin
                w_mr_seq_we    = 1'b1;
                w_mr_seq_index = 5'd3;
                w_mr_seq_data  = (memtype_i == MEMTYPE_DDR2)
                               ? DDR2_MR3_DEFAULT : 16'd0;
            end
            S_MR_MR1: begin
                w_mr_seq_we    = 1'b1;
                w_mr_seq_index = 5'd1;
                w_mr_seq_data  = (memtype_i == MEMTYPE_DDR2)
                               ? DDR2_MR1_DEFAULT : 16'd0;
            end
            S_MR_MR0: begin
                w_mr_seq_we    = 1'b1;
                w_mr_seq_index = 5'd0;
                w_mr_seq_data  = (memtype_i == MEMTYPE_DDR2)
                               ? DDR2_MR0_DEFAULT : 16'd0;
            end
            default: ;
        endcase
    end

    //=========================================================================
    // Strict-flop outputs.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dfi_init_start_o <= 1'b0;
            mr_seq_we_o      <= 1'b0;
            mr_seq_index_o   <= 5'd0;
            mr_seq_data_o    <= 16'd0;
            zqcl_req_o       <= 1'b0;
            init_busy_o      <= 1'b1;
            init_done_o      <= 1'b0;
        end else begin
            dfi_init_start_o <= (r_state != S_RESET);
            mr_seq_we_o      <= w_mr_seq_we;
            mr_seq_index_o   <= w_mr_seq_index;
            mr_seq_data_o    <= w_mr_seq_data;
            zqcl_req_o       <= (r_state == S_ZQCL);
            init_busy_o      <= (r_state != S_DONE);
            init_done_o      <= (r_state == S_DONE);
        end
    end)

endmodule : init_sequencer
