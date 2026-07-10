// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: init_sequencer
// Purpose: Post-reset DRAM bring-up sequencer — full JEDEC DDR2 init.
//
//          DDR2 sequence (mirrors LiteDRAM's get_ddr2_phy_init_sequence,
//          litedram/init.py — the reference proven on the Nexys A7 board):
//            1. Assert dfi_init_start_o; wait dfi_init_complete_i (PHY runs
//               its own DLL-lock / IO training). Then wait tINIT (CKE settle).
//            2. Precharge All.
//            3. Load EMR3=0, EMR2=0, EMR/MR1=0 (JEDEC order MR3, MR2, MR1).
//            4. Load MR0 + DLL-reset (0x532: BL4/CL3/tWR3/DLL_RESET); wait for
//               the DLL to lock (~200 DRAM clocks).
//            5. Precharge All.
//            6. Auto Refresh x2 (each followed by tRFC).
//            7. Load MR0 WITHOUT DLL-reset (0x432) — clears the reset bit.
//            8. EMR/MR1 + OCD Default (0x380) -> EMR/MR1 + OCD Exit (0x000).
//            9. init_done_o = 1.
//
//          Commands are ISSUED TO THE DRAM (not just shadowed): the sequencer
//          drives a command-request port (init_cmd_valid_o/op/bank/row) that
//          the scheduler forwards to dfi_cmd_formatter while init_busy_o is
//          high (the scheduler stays in S_IDLE and owns nothing else during
//          init, and dfi_cmd_formatter is always cmd_ready — so a single-cycle
//          init_cmd pulse issues exactly one command; no grant handshake is
//          needed). Each command occupies its state for one cycle, then the
//          FSM parks in S_WAIT for the JEDEC inter-command delay.
//
//          The mode_register shadow is updated in lockstep (mr_seq_we_o) so
//          the controller's live CL/CWL/BL decode tracks what was programmed.
//
//          LPDDR2: issues the 3 EMR + MR0 MRS writes with LPDDR2 defaults then
//          finishes (its JEDEC init — MR63 reset / MR10 ZQ / per-step tINIT —
//          is a v3 TODO; DDR2 is the validated path).
//
// History: was a "simplified" 4-MR shadow-only walk that NEVER issued MRS/
//   precharge/refresh to the DRAM. On the DFI-loopback sim the memory model
//   stores/returns data regardless of init, so it passed; on real DDR2 the
//   read DLL never locked (no proper reset+refresh) and no IDELAY tap found a
//   read eye. This full sequence fixes on-board bring-up.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module init_sequencer
    import pumice_pkg::*;
#(
    parameter int ROW_WIDTH = 14,
    parameter int NUM_BANKS = 8,
    parameter int BKW       = $clog2(NUM_BANKS)
)(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  memtype_e    memtype_i,

    // ----- JEDEC init-sequence waits (CSR-backed, MC cycles) -----
    input  logic [15:0] t_init_wait_i,   // CKE / tINIT settle
    input  logic [15:0] t_dll_wait_i,    // DLL lock (tDLLK)
    input  logic [7:0]  t_mrd_wait_i,    // post mode-register-set (tMRD)
    input  logic [7:0]  t_rp_wait_i,     // post precharge (tRP)
    input  logic [7:0]  t_rfc_wait_i,    // post auto-refresh (tRFC)

    // ----- DFI status -----
    output logic        dfi_init_start_o,
    input  logic        dfi_init_complete_i,

    // ----- MR-shadow write port (mux'd with CSR by command_scheduler_macro) -
    output logic        mr_seq_we_o,
    output logic [4:0]  mr_seq_index_o,
    output logic [15:0] mr_seq_data_o,

    // ----- DRAM command request into the scheduler (issued while init_busy) -
    output logic              init_cmd_valid_o,
    output dram_op_e          init_cmd_op_o,
    output logic [BKW-1:0]    init_cmd_bank_o,   // MR index (MRS) / bank
    output logic [ROW_WIDTH-1:0] init_cmd_row_o, // MR data (MRS) — wide path

    // ----- legacy ZQCL handshake (DDR3+; DDR2 has no ZQCL) — tied off -----
    output logic        zqcl_req_o,
    input  logic        zqcl_grant_i,

    // ----- status -----
    output logic        init_busy_o,
    output logic        init_done_o
);

    //=========================================================================
    // Mode-register data (DDR2). MR0 mirrors LiteDRAM's mr + reset_dll:
    //   mr = log2(BL=4)=2 | (CL=3 << 4)=0x30 | (tWR=3 << 9)=0x400 = 0x432
    //   reset_dll = 1 << 8 = 0x100  ->  MR0+reset_dll = 0x532
    //   MR1(EMR)=0 (Rtt disabled, ODS full — matches LiteDRAM); OCD default =
    //   EMR | (7<<7) = 0x380; OCD exit = EMR = 0.
    //=========================================================================
    localparam logic [15:0] DDR2_MR0_DLL  = 16'h0532;  // BL4/CL3/tWR3/DLL_RESET
    localparam logic [15:0] DDR2_MR0       = 16'h0432;  // same, DLL_RESET cleared
    localparam logic [15:0] DDR2_MR1       = 16'h0000;
    localparam logic [15:0] DDR2_MR1_OCD   = 16'h0380;  // OCD calibration default
    localparam logic [15:0] DDR2_MR2       = 16'h0000;
    localparam logic [15:0] DDR2_MR3       = 16'h0000;

    // LPDDR2 defaults (skeleton — see header).
    localparam logic [15:0] LPDDR2_MR1     = 16'h0082;  // BL4, nWR=3
    localparam logic [15:0] LPDDR2_MR2     = 16'h0004;  // RL3/WL1
    localparam logic [15:0] LPDDR2_MR3     = 16'h0001;  // DS=34ohm

    //=========================================================================
    // Inter-command wait counts (mc_clk cycles). One-time init, so generous
    // margins are fine. At sys=37.5 MHz / CK=150 MHz these comfortably cover
    // the JEDEC minimums (tINIT/tRP/tMRD/tRFC + DLL lock 200 CK).
    //=========================================================================
    // JEDEC init waits — now CSR-backed (INIT_TIMING0/1), zero-extended to the
    // 16-bit countdown. Defaults live in the CSR (512/256/8/8/16). Was hardcoded.
    logic [15:0] W_INIT, W_RP, W_MRD, W_DLL, W_RFC;
    assign W_INIT = t_init_wait_i;              // CKE / tINIT settle
    assign W_RP   = {8'd0, t_rp_wait_i};        // tRP after precharge
    assign W_MRD  = {8'd0, t_mrd_wait_i};       // tMRD after mode-reg load
    assign W_DLL  = t_dll_wait_i;               // DLL lock (tDLLK)
    assign W_RFC  = {8'd0, t_rfc_wait_i};       // tRFC after auto-refresh

    //=========================================================================
    // FSM
    //=========================================================================
    typedef enum logic [4:0] {
        S_RESET    = 5'd0,
        S_DFI_INIT = 5'd1,   // wait PHY init complete
        S_PREA1    = 5'd2,   // Precharge All (pre-EMR)
        S_EMR3     = 5'd3,
        S_EMR2     = 5'd4,
        S_EMR1     = 5'd5,
        S_MR0_DLL  = 5'd6,   // MR0 + DLL reset
        S_PREA2    = 5'd7,   // Precharge All (pre-refresh)
        S_REF1     = 5'd8,
        S_REF2     = 5'd9,
        S_MR0      = 5'd10,  // MR0 (DLL reset cleared)
        S_OCD_DEF  = 5'd11,  // EMR + OCD default
        S_OCD_EXIT = 5'd12,  // EMR + OCD exit
        S_WAIT     = 5'd13,  // inter-command delay, then -> r_next
        S_DONE     = 5'd14
    } state_e;

    state_e             r_state;
    state_e             r_next;    // state to resume after S_WAIT
    logic [15:0]        r_wait;    // countdown
    logic               w_is_ddr2;
    assign w_is_ddr2 = (memtype_i == MEMTYPE_DDR2);

    //=========================================================================
    // Next-state + wait scheduling. Each command state is occupied for exactly
    // ONE cycle (unconditional -> S_WAIT), so init_cmd_valid_o (decoded below)
    // is a single-cycle pulse per command.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state <= S_RESET;
            r_next  <= S_RESET;
            r_wait  <= 16'd0;
        end else begin
            unique case (r_state)
                S_RESET:    r_state <= S_DFI_INIT;
                S_DFI_INIT: if (dfi_init_complete_i) begin
                                r_wait  <= W_INIT;
                                r_next  <= w_is_ddr2 ? S_PREA1 : S_EMR2;
                                r_state <= S_WAIT;
                            end
                // JEDEC JESD79-2 mode-register order: EMRS(2), EMRS(3), EMRS(1),
                // then MRS(0)+DLL-reset.
                S_PREA1:    begin r_wait <= W_RP;  r_next <= S_EMR2;    r_state <= S_WAIT; end
                S_EMR2:     begin r_wait <= W_MRD; r_next <= S_EMR3;    r_state <= S_WAIT; end
                S_EMR3:     begin r_wait <= W_MRD; r_next <= S_EMR1;    r_state <= S_WAIT; end
                S_EMR1:     begin r_wait <= W_MRD; r_next <= S_MR0_DLL; r_state <= S_WAIT; end
                S_MR0_DLL:  begin r_wait <= W_DLL;
                                  r_next <= w_is_ddr2 ? S_PREA2 : S_DONE;
                                  r_state <= S_WAIT; end
                S_PREA2:    begin r_wait <= W_RP;  r_next <= S_REF1;    r_state <= S_WAIT; end
                S_REF1:     begin r_wait <= W_RFC; r_next <= S_REF2;    r_state <= S_WAIT; end
                S_REF2:     begin r_wait <= W_RFC; r_next <= S_MR0;     r_state <= S_WAIT; end
                S_MR0:      begin r_wait <= W_MRD; r_next <= S_OCD_DEF; r_state <= S_WAIT; end
                S_OCD_DEF:  begin r_wait <= W_MRD; r_next <= S_OCD_EXIT;r_state <= S_WAIT; end
                S_OCD_EXIT: begin r_wait <= W_MRD; r_next <= S_DONE;    r_state <= S_WAIT; end
                S_WAIT:     if (r_wait == 16'd0) r_state <= r_next;
                            else                 r_wait  <= r_wait - 16'd1;
                S_DONE:     r_state <= S_DONE;
                default:    r_state <= S_RESET;
            endcase
        end
    end)

    //=========================================================================
    // Per-state command + shadow decode (combinational). The command state is
    // occupied one cycle -> single-cycle pulse; the scheduler registers it.
    //=========================================================================
    always_comb begin
        init_cmd_valid_o = 1'b0;
        init_cmd_op_o    = OP_NOP;
        init_cmd_bank_o  = '0;
        init_cmd_row_o   = '0;
        mr_seq_we_o      = 1'b0;
        mr_seq_index_o   = 5'd0;
        mr_seq_data_o    = 16'd0;

        unique case (r_state)
            S_PREA1, S_PREA2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_PREA;
            end
            S_REF1, S_REF2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_REF;
            end
            S_EMR3: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(3);
                init_cmd_row_o   = ROW_WIDTH'(w_is_ddr2 ? DDR2_MR3 : LPDDR2_MR3);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd3;
                mr_seq_data_o    = w_is_ddr2 ? DDR2_MR3 : LPDDR2_MR3;
            end
            S_EMR2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(2);
                init_cmd_row_o   = ROW_WIDTH'(w_is_ddr2 ? DDR2_MR2 : LPDDR2_MR2);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd2;
                mr_seq_data_o    = w_is_ddr2 ? DDR2_MR2 : LPDDR2_MR2;
            end
            S_EMR1: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(w_is_ddr2 ? DDR2_MR1 : LPDDR2_MR1);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = w_is_ddr2 ? DDR2_MR1 : LPDDR2_MR1;
            end
            S_MR0_DLL: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(0);
                // LPDDR2 MR0 is read-only -> write 0.
                init_cmd_row_o   = ROW_WIDTH'(w_is_ddr2 ? DDR2_MR0_DLL : 16'd0);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd0;
                mr_seq_data_o    = w_is_ddr2 ? DDR2_MR0_DLL : 16'd0;
            end
            S_MR0: begin  // DDR2-only (LPDDR2 jumps to DONE after S_MR0_DLL)
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(0);
                init_cmd_row_o   = ROW_WIDTH'(DDR2_MR0);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd0;
                mr_seq_data_o    = DDR2_MR0;
            end
            S_OCD_DEF: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(DDR2_MR1_OCD);
                // OCD is a transient calibration mode; leave the shadow at the
                // final EMR value (updated by S_OCD_EXIT) so decode is stable.
            end
            S_OCD_EXIT: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(DDR2_MR1);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = DDR2_MR1;
            end
            default: ;
        endcase
    end

    //=========================================================================
    // Status outputs (registered — strict flop outputs, house style).
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dfi_init_start_o <= 1'b0;
            zqcl_req_o       <= 1'b0;
            init_busy_o      <= 1'b1;
            init_done_o      <= 1'b0;
        end else begin
            dfi_init_start_o <= (r_state != S_RESET);
            zqcl_req_o       <= 1'b0;   // DDR2 has no ZQCL
            init_busy_o      <= (r_state != S_DONE);
            init_done_o      <= (r_state == S_DONE);
        end
    end)

    wire _unused = &{1'b0, zqcl_grant_i};

endmodule : init_sequencer
