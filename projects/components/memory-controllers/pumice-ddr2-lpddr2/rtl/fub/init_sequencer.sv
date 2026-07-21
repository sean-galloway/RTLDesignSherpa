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
//          LPDDR2 sequence (JEDEC JESD209-2F §3.4.1 power-up + §3.5 MRs):
//            1. dfi_init_start; wait dfi_init_complete; tINIT settle.
//            2. MRW(MR63) = Reset (OP don't-care); wait tINIT4.
//            3. MRW(MR10) = 0xFF ZQ Init Calibration; wait tZQINIT.
//            4. MRW(MR1) = BL8/nWR3 (0x23), MRW(MR2) = RL3/WL1 (0x01),
//               MRW(MR3) = DS 40ohm (0x02) — configure the device.
//            5. init_done.
//          The MR index (MA, up to MR63) + data (OP) are carried in the ROW
//          request field packed as {MA[5:0], OP[7:0]} (dfi_cmd_formatter unpacks
//          it for the LPDDR2 CA MRW word — a 3-bit bank port can't reach MR10/63).
//          Only MR1/MR2/MR3 update the CL/CWL/BL decode shadow; MR63/MR10 are
//          issued to the DRAM but not shadowed.
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

    // ----- DDR2 mode-register values (CSR-backed: MR0..MR3.VAL) -----
    // The init FSM loads these onto the DRAM address bus for the JEDEC MRS
    // sequence. Runtime-programmable so software can (a) retune CL/BL/tWR and
    // (b) DEFEAT AN ARBITRARY A-LANE MAPPING on a board where MRS address bits
    // land on scrambled DRAM pins — sweep MRx.VAL + re-run init until reads are
    // clean. Reset defaults (RDL) reproduce the JEDEC values, so the default
    // init is bit-identical to the old hardcoded localparams. The DLL-reset
    // MR0 write ORs in bit 8 (DLL_RESET); OCD-default ORs A[9:7]=111 into MR1.
    input  logic [15:0] mr0_i,           // MR0 base (BL/CL/tWR)
    input  logic [15:0] mr1_i,           // MR1 / EMR (ODT, ODS, DLL-en)
    input  logic [15:0] mr2_i,           // MR2 / EMR2
    input  logic [15:0] mr3_i,           // MR3 / EMR3

    // Re-run the JEDEC MRS chain WITHOUT a controller reset (CTRL.init_force_
    // restart). A rising edge restarts the FSM at S_RESET, re-loading the (CSR)
    // MR values — the only way to apply a freshly-written MRx.VAL, since a
    // soft_reset would wipe the CSRs before init could read them.
    input  logic        init_restart_i,

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
    //   mr = log2(BL=8)=3 | (CL=3 << 4)=0x30 | (tWR=3 << 9)=0x400 = 0x433
    //   reset_dll = 1 << 8 = 0x100  ->  MR0+reset_dll = 0x533
    //   MR1(EMR)=0 (Rtt disabled, ODS full — matches LiteDRAM); OCD default =
    //   EMR | (7<<7) = 0x380; OCD exit = EMR = 0.
    // BL8 (MR0[2:0]=011): at nphases=4 a BL8 x16 read fills one full 128b DFI
    // word in ONE 8-slot PHY event (BL4 filled only 4 of 8 slots -> stale
    // half; the on-silicon read-fail root cause). log2(BL) encoding: 2=BL4,
    // 3=BL8.
    //=========================================================================
    // MR values are now CSR-backed (mr0_i..mr3_i, defaults set in the RDL to the
    // JEDEC values documented above). Only the transient bit-masks the init FSM
    // applies on top of the base MR values remain as constants here:
    localparam logic [15:0] DDR2_DLL_RESET = 16'h0100;  // MR0 A8: DLL reset (first MR0 load)
    localparam logic [15:0] DDR2_OCD_DEF   = 16'h0380;  // MR1 A[9:7]=111: OCD calibration default

    // LPDDR2 mode-register OP (data) values — JEDEC JESD209-2F §3.5. 8-bit OP;
    // the index (MA) is a separate field packed with OP into the row request.
    localparam logic [7:0] LPDDR2_MR63_OP = 8'h00;  // MRW(63) Reset — OP don't-care
    localparam logic [7:0] LPDDR2_MR10_OP = 8'hFF;  // MR10 ZQ Init Calibration
    localparam logic [7:0] LPDDR2_MR1_OP  = 8'h23;  // MR1: nWR3(001)|WC0|BT0|BL8(011)
    localparam logic [7:0] LPDDR2_MR2_OP  = 8'h01;  // MR2: RL3/WL1 (default)
    localparam logic [7:0] LPDDR2_MR3_OP  = 8'h02;  // MR3: DS 40ohm (default)
    // MR indices (MA). MR10/MR63 exceed the 5-bit shadow index -> not shadowed.
    localparam int LPDDR2_MR63 = 63;
    localparam int LPDDR2_MR10 = 10;

    // Pack {MA[5:0], OP[7:0]} into the ROW request field (dfi_cmd_formatter
    // unpacks row[13:8]=MA, row[7:0]=OP for the LPDDR2 CA MRW word).
    function automatic logic [ROW_WIDTH-1:0] mrw_row(input int idx, input logic [7:0] op);
        mrw_row = ROW_WIDTH'((32'(idx[5:0]) << 8) | 32'(op));
    endfunction

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
        S_DONE     = 5'd14,
        // ----- LPDDR2-only MRW sequence -----
        S_L_RESET  = 5'd15,  // MRW(MR63) Reset
        S_L_ZQ     = 5'd16,  // MRW(MR10) ZQ Init Calibration
        S_L_MR1    = 5'd17,  // MRW(MR1) BL/nWR
        S_L_MR2    = 5'd18,  // MRW(MR2) RL/WL
        S_L_MR3    = 5'd19   // MRW(MR3) drive strength
    } state_e;

    state_e             r_state;
    state_e             r_next;    // state to resume after S_WAIT
    logic [15:0]        r_wait;    // countdown
    logic               w_is_ddr2;
    assign w_is_ddr2 = (memtype_i == MEMTYPE_DDR2);

    // Rising-edge detect on the CTRL.init_force_restart level -> single restart.
    logic r_restart_d, w_restart_pulse;
    assign w_restart_pulse = init_restart_i & ~r_restart_d;
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) r_restart_d <= 1'b0;
        else                         r_restart_d <= init_restart_i;
    end)

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
        end else if (w_restart_pulse) begin
            // Force re-init (CTRL.init_force_restart): replay the MRS chain with
            // the current CSR MR values. S_DFI_INIT re-checks dfi_init_complete
            // (held high post-PHY-init), then the JEDEC sequence re-runs.
            r_state <= S_RESET;
            r_next  <= S_RESET;
            r_wait  <= 16'd0;
        end else begin
            unique case (r_state)
                S_RESET:    r_state <= S_DFI_INIT;
                S_DFI_INIT: if (dfi_init_complete_i) begin
                                r_wait  <= W_INIT;
                                r_next  <= w_is_ddr2 ? S_PREA1 : S_L_RESET;
                                r_state <= S_WAIT;
                            end
                // JEDEC JESD79-2 mode-register order: EMRS(2), EMRS(3), EMRS(1),
                // then MRS(0)+DLL-reset.
                S_PREA1:    begin r_wait <= W_RP;  r_next <= S_EMR2;    r_state <= S_WAIT; end
                S_EMR2:     begin r_wait <= W_MRD; r_next <= S_EMR3;    r_state <= S_WAIT; end
                S_EMR3:     begin r_wait <= W_MRD; r_next <= S_EMR1;    r_state <= S_WAIT; end
                S_EMR1:     begin r_wait <= W_MRD; r_next <= S_MR0_DLL; r_state <= S_WAIT; end
                S_MR0_DLL:  begin r_wait <= W_DLL;
                                  r_next <= S_PREA2;  // DDR2-only path
                                  r_state <= S_WAIT; end
                S_PREA2:    begin r_wait <= W_RP;  r_next <= S_REF1;    r_state <= S_WAIT; end
                S_REF1:     begin r_wait <= W_RFC; r_next <= S_REF2;    r_state <= S_WAIT; end
                S_REF2:     begin r_wait <= W_RFC; r_next <= S_MR0;     r_state <= S_WAIT; end
                S_MR0:      begin r_wait <= W_MRD; r_next <= S_OCD_DEF; r_state <= S_WAIT; end
                S_OCD_DEF:  begin r_wait <= W_MRD; r_next <= S_OCD_EXIT;r_state <= S_WAIT; end
                S_OCD_EXIT: begin r_wait <= W_MRD; r_next <= S_DONE;    r_state <= S_WAIT; end
                // ----- LPDDR2 MRW chain: Reset -> ZQ -> MR1 -> MR2 -> MR3 -----
                // Reuse the CSR waits: W_INIT covers tINIT4, W_DLL covers tZQINIT,
                // W_MRD covers post-MRW (tMRW).
                S_L_RESET:  begin r_wait <= W_INIT; r_next <= S_L_ZQ;   r_state <= S_WAIT; end
                S_L_ZQ:     begin r_wait <= W_DLL;  r_next <= S_L_MR1;  r_state <= S_WAIT; end
                S_L_MR1:    begin r_wait <= W_MRD;  r_next <= S_L_MR2;  r_state <= S_WAIT; end
                S_L_MR2:    begin r_wait <= W_MRD;  r_next <= S_L_MR3;  r_state <= S_WAIT; end
                S_L_MR3:    begin r_wait <= W_MRD;  r_next <= S_DONE;   r_state <= S_WAIT; end
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
            // S_EMR*/S_MR0* are DDR2-only (LPDDR2 uses the S_L_* chain below).
            S_EMR3: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(3);
                init_cmd_row_o   = ROW_WIDTH'(mr3_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd3;
                mr_seq_data_o    = mr3_i;
            end
            S_EMR2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(2);
                init_cmd_row_o   = ROW_WIDTH'(mr2_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd2;
                mr_seq_data_o    = mr2_i;
            end
            S_EMR1: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(mr1_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = mr1_i;
            end
            S_MR0_DLL: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(0);
                init_cmd_row_o   = ROW_WIDTH'(mr0_i | DDR2_DLL_RESET);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd0;
                mr_seq_data_o    = mr0_i | DDR2_DLL_RESET;
            end
            // ----- LPDDR2 MRW chain -----
            S_L_RESET: begin  // MRW(MR63) Reset — issued, not shadowed
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(LPDDR2_MR63, LPDDR2_MR63_OP);
            end
            S_L_ZQ: begin     // MRW(MR10) ZQ Init — issued, not shadowed
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(LPDDR2_MR10, LPDDR2_MR10_OP);
            end
            S_L_MR1: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(1, LPDDR2_MR1_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = {8'd0, LPDDR2_MR1_OP};
            end
            S_L_MR2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(2, LPDDR2_MR2_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd2;
                mr_seq_data_o    = {8'd0, LPDDR2_MR2_OP};
            end
            S_L_MR3: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(3, LPDDR2_MR3_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd3;
                mr_seq_data_o    = {8'd0, LPDDR2_MR3_OP};
            end
            S_MR0: begin  // DDR2-only (LPDDR2 jumps to DONE after S_MR0_DLL)
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(0);
                init_cmd_row_o   = ROW_WIDTH'(mr0_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd0;
                mr_seq_data_o    = mr0_i;
            end
            S_OCD_DEF: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(mr1_i | DDR2_OCD_DEF);
                // OCD is a transient calibration mode; leave the shadow at the
                // final EMR value (updated by S_OCD_EXIT) so decode is stable.
            end
            S_OCD_EXIT: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(mr1_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = mr1_i;
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
