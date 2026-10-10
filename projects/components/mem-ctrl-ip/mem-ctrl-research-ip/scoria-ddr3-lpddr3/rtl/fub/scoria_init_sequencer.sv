// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: init_sequencer
// Purpose: Post-reset DRAM bring-up sequencer — full JEDEC DDR2 init.
//
//          DDR3 sequence -- JESD79-3F "Power-up Initialization", verbatim
//          in the spec's order, because the order is not ours to choose:
//            1.  Power ramp (board-level, not this module).
//            2.  RESET# de-asserted, then wait 500 us before CKE goes active.
//            3.  Clocks stable >= 10 ns or 5 tCK before CKE; a NOP/Deselect
//                registered before CKE high. CKE must then stay continuously
//                high until tDLLK AND tZQinit have expired.
//            4.  ODT held statically through init (LOW if RTT_NOM is to be
//                enabled in MR1) -- driven by the harness, noted here because
//                the sequencer owns the window.
//            5.  Wait tXPR = max(tXS, 5 tCK) after CKE high, before the first MRS.
//            6.  MRS -> MR2
//            7.  MRS -> MR3
//            8.  MRS -> MR1, DLL enabled
//            9.  MRS -> MR0, DLL reset
//            10. ZQCL, to start ZQ calibration
//            11. Wait for BOTH tDLLK and tZQinit
//            12. Ready.
//
//          Note what DDR3 does NOT need and DDR2 did: no precharge-all, no
//          double auto-refresh, no OCD default/exit pair, and no second MR0
//          load to clear the DLL-reset bit (it is self-clearing -- JESD79-3F
//          3.4.2.4). The DDR3 sequence is genuinely shorter than DDR2's.
//
//          RESET# IS A PIN, not a command. That is the structural difference
//          from pumice: this sequencer drives dram_reset_n_o and holds a timed
//          window, rather than only issuing commands.
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

module scoria_init_sequencer
    import scoria_pkg::*;
#(
    parameter int ROW_WIDTH = 14,
    parameter int NUM_BANKS = 8,
    parameter int BKW       = $clog2(NUM_BANKS)
)(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  memtype_e    memtype_i,

    // DDR3: RESET# is a device PIN the sequencer owns (JESD79-3F step 2).
    output logic        dram_reset_n_o,

    // ----- JEDEC init-sequence waits (CSR-backed, MC cycles) -----
    input  logic [15:0] t_init_wait_i,   // CKE / tINIT settle
    input  logic [15:0] t_dll_wait_i,
    // DDR3 additions, both runtime CSRs like every other enforced timing
    input  logic [15:0] t_xpr_wait_i,      // tXPR = max(tXS, 5 tCK), step 5
    input  logic [15:0] t_zqinit_wait_i,   // tZQinit, step 11    // DLL lock (tDLLK)
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
    localparam logic [15:0] DDR3_DLL_RESET = 16'h0100;  // MR0 A8: DLL reset (self-clearing)

    // LPDDR2 mode-register OP (data) values — JEDEC JESD209-2F §3.5. 8-bit OP;
    // the index (MA) is a separate field packed with OP into the row request.
    localparam logic [7:0] LPDDR3_MR63_OP = 8'h00;  // MRW(63) Reset — OP don't-care
    localparam logic [7:0] LPDDR3_MR10_OP = 8'hFF;  // MR10 ZQ Init Calibration
    localparam logic [7:0] LPDDR3_MR1_OP  = 8'h23;  // MR1: nWR3(001)|WC0|BT0|BL8(011)
    localparam logic [7:0] LPDDR3_MR2_OP  = 8'h01;  // MR2: RL3/WL1 (default)
    localparam logic [7:0] LPDDR3_MR3_OP  = 8'h02;  // MR3: DS 40ohm (default)
    // MR indices (MA). MR10/MR63 exceed the 5-bit shadow index -> not shadowed.
    localparam int LPDDR3_MR63 = 63;
    localparam int LPDDR3_MR10 = 10;

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
    logic [15:0] W_INIT, W_RP, W_MRD, W_DLL, W_RFC, W_XPR, W_ZQINIT;
    assign W_INIT = t_init_wait_i;              // CKE / tINIT settle
    assign W_RP   = {8'd0, t_rp_wait_i};        // tRP after precharge
    assign W_MRD  = {8'd0, t_mrd_wait_i};       // tMRD after mode-reg load
    assign W_DLL  = t_dll_wait_i;               // DLL lock (tDLLK)
    assign W_RFC  = {8'd0, t_rfc_wait_i};       // tRFC (unused on DDR3: no init refresh)
    assign W_XPR    = t_xpr_wait_i;             // tXPR before the first MRS
    assign W_ZQINIT = t_zqinit_wait_i;          // tZQinit, waited with tDLLK

    //=========================================================================
    // FSM
    //=========================================================================
    typedef enum logic [4:0] {
        S_RESET    = 5'd0,
        S_DFI_INIT = 5'd1,   // wait PHY init complete
        // ----- DDR3 chain (JESD79-3F power-up) -----
        S_D3_RSTN  = 5'd2,   // RESET# asserted
        S_D3_CKE   = 5'd3,   // RESET# released; 500 us before CKE active
        S_D3_XPR   = 5'd4,   // CKE high; tXPR before the first MRS
        S_D3_MR2   = 5'd5,
        S_D3_MR3   = 5'd6,
        S_D3_MR1   = 5'd7,   // DLL enable
        S_D3_MR0   = 5'd8,   // DLL reset (self-clearing)
        S_D3_ZQCL  = 5'd9,
        S_D3_LOCK  = 5'd10,  // wait tDLLK AND tZQinit
        S_WAIT     = 5'd13,  // inter-command delay, then -> r_next
        S_DONE     = 5'd14,
        // ----- LPDDR3 MRW chain; inherited from LPDDR2, same MR encoding -----
        S_L_RESET  = 5'd15,  // MRW(MR63) Reset
        S_L_ZQ     = 5'd16,  // MRW(MR10) ZQ Init Calibration
        S_L_MR1    = 5'd17,
        S_L_MR2    = 5'd18,
        S_L_MR3    = 5'd19
    } state_e;

    state_e             r_state;
    state_e             r_next;    // state to resume after S_WAIT
    logic               r_rstn_released;  // DDR3 RESET# has been let go
    logic [15:0]        r_wait;    // countdown
    logic               w_is_ddr3;
    assign w_is_ddr3 = (memtype_i == MEMTYPE_DDR3);

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
            r_rstn_released <= 1'b0;
            r_wait  <= 16'd0;
        end else if (w_restart_pulse) begin
            // Force re-init (CTRL.init_force_restart): replay the MRS chain with
            // the current CSR MR values. S_DFI_INIT re-checks dfi_init_complete
            // (held high post-PHY-init), then the JEDEC sequence re-runs.
            r_state <= S_RESET;
r_next  <= S_RESET;
            r_rstn_released <= 1'b0;
            r_wait  <= 16'd0;
        end else begin
            unique case (r_state)
                S_RESET:    r_state <= S_DFI_INIT;
                S_DFI_INIT: if (dfi_init_complete_i) begin
                                r_wait  <= W_INIT;
                                r_next  <= w_is_ddr3 ? S_D3_RSTN : S_L_RESET;
                                r_state <= S_WAIT;
                            end
                // JESD79-3F: RESET# low, then 500 us before CKE, then tXPR
                // before the first MRS. W_INIT carries the 500 us (a CSR, so
                // it can be shortened in simulation -- 50,000 cycles at
                // 100 MHz is real time nobody wants in a testbench).
                S_D3_RSTN:  begin r_wait <= W_INIT; r_next <= S_D3_CKE;  r_state <= S_WAIT; end
                S_D3_CKE:   begin
                                // Reaching CKE is the release point: RESET#
                                // high, then CKE low for the 500 us window,
                                // then tXPR. Latched, so nothing downstream
                                // can re-assert the pin.
                                r_rstn_released <= 1'b1;
                                r_wait <= W_XPR; r_next <= S_D3_XPR; r_state <= S_WAIT;
                            end
                S_D3_XPR:   begin r_wait <= W_MRD;  r_next <= S_D3_MR2;  r_state <= S_WAIT; end
                // MR order is the spec's: MR2, MR3, MR1, MR0. Not sorted --
                // MR1 carries DLL enable and MR0 carries DLL reset, so the
                // order encodes a dependency. pumice got its DDR2 equivalent
                // wrong once (EMRS3 before EMRS2); this is a citation.
                S_D3_MR2:   begin r_wait <= W_MRD;  r_next <= S_D3_MR3;  r_state <= S_WAIT; end
                S_D3_MR3:   begin r_wait <= W_MRD;  r_next <= S_D3_MR1;  r_state <= S_WAIT; end
                S_D3_MR1:   begin r_wait <= W_MRD;  r_next <= S_D3_MR0;  r_state <= S_WAIT; end
                S_D3_MR0:   begin r_wait <= W_MRD;  r_next <= S_D3_ZQCL; r_state <= S_WAIT; end
                S_D3_ZQCL:  begin
                                // Step 11: wait for BOTH tDLLK and tZQinit.
                                // Taking the larger is what "both" means.
                                r_wait  <= (W_DLL > W_ZQINIT) ? W_DLL : W_ZQINIT;
                                r_next  <= S_D3_LOCK;
                                r_state <= S_WAIT;
                            end
                S_D3_LOCK:  r_state <= S_DONE;

                // ---- LPDDR3: MRW(MR63) reset, ZQ init, then MR1/2/3 ----
                // These arms were MISSING. The states existed and their
                // command decode existed, but with no next-state arm they fell
                // to `default: r_state <= S_RESET`, so LPDDR3 looped
                // S_RESET -> S_DFI_INIT -> S_L_RESET -> S_RESET forever and
                // init never completed. Dropped when this sequencer was ported
                // from pumice, which has the equivalent LPDDR2 chain wired.
                // Found by test_scoria_init_sequencer's lpddr3_path_differs.
                S_L_RESET:  begin r_wait <= W_INIT; r_next <= S_L_ZQ;  r_state <= S_WAIT; end
                S_L_ZQ:     begin r_wait <= W_DLL;  r_next <= S_L_MR1; r_state <= S_WAIT; end
                S_L_MR1:    begin r_wait <= W_MRD;  r_next <= S_L_MR2; r_state <= S_WAIT; end
                S_L_MR2:    begin r_wait <= W_MRD;  r_next <= S_L_MR3; r_state <= S_WAIT; end
                S_L_MR3:    begin r_wait <= W_MRD;  r_next <= S_DONE;  r_state <= S_WAIT; end

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
        // RESET# is LATCHED released, not decoded from the state set. The
        // original decoded it, and getting that right is harder than it looks:
        //
        //   every command state is occupied for exactly ONE cycle, then the FSM
        //   parks in S_WAIT. So the low period the pin actually needs -- the
        //   JESD79-3F 200 us power-up window, carried by W_INIT -- is spent in
        //   S_WAIT, not in S_D3_RSTN. The first version listed S_RESET,
        //   S_DFI_INIT and S_D3_RSTN and therefore drove RESET# low for a
        //   single 10 ns cycle and released it for the whole window.
        //
        // Enumerating the S_WAITs instead does not fix it either: there are TWO
        // on the way (r_next = S_D3_RSTN, then r_next = S_D3_CKE) and adding
        // only the second leaves a high-low-high glitch on a device pin. That
        // is not a hypothetical -- it is what the second attempt at this line
        // did, and reset_n_pin caught it again.
        //
        // A latch says the intended thing once: asserted from reset until the
        // sequence reaches CKE, then released and never re-asserted without a
        // restart. LPDDR3 has no RESET# pin, so it reads high throughout.
        dram_reset_n_o   = !w_is_ddr3 || r_rstn_released;

        unique case (r_state)
            // ---- DDR3: four MRS loads in the spec's order, then ZQCL ----
            // bank = MR index (BA0-BA2 select MR0..MR3, JESD79-3F Table 6),
            // row  = MR data. Identical decode to pumice's; only the ORDER
            // and the absent DDR2-only steps differ.
            S_D3_MR2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(2);
                init_cmd_row_o   = ROW_WIDTH'(mr2_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd2;
                mr_seq_data_o    = mr2_i;
            end
            S_D3_MR3: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(3);
                init_cmd_row_o   = ROW_WIDTH'(mr3_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd3;
                mr_seq_data_o    = mr3_i;
            end
            S_D3_MR1: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(1);
                init_cmd_row_o   = ROW_WIDTH'(mr1_i);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = mr1_i;
            end
            S_D3_MR0: begin
                // MR0 with A8 (DLL reset) forced high. The bit is
                // SELF-CLEARING per JESD79-3F 3.4.2.4, which is why DDR3
                // needs no second MR0 load to clear it -- DDR2 did, and
                // pumice has that extra state. The SHADOW is written with
                // mr0_i unmodified, so the controller's CL/CWL/BL decode
                // tracks the steady-state value rather than the reset pulse.
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_bank_o  = BKW'(0);
                init_cmd_row_o   = ROW_WIDTH'(mr0_i | DDR3_DLL_RESET);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd0;
                mr_seq_data_o    = mr0_i;
            end
            S_D3_ZQCL: begin
                // Step 10. Bank/address are don't-care; the formatter drives
                // A10 = 1 for the long calibration.
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_ZQCL;
            end
            S_L_RESET: begin  // MRW(MR63) Reset — issued, not shadowed
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(LPDDR3_MR63, LPDDR3_MR63_OP);
            end
            S_L_ZQ: begin     // MRW(MR10) ZQ Init — issued, not shadowed
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(LPDDR3_MR10, LPDDR3_MR10_OP);
            end
            S_L_MR1: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(1, LPDDR3_MR1_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd1;
                mr_seq_data_o    = {8'd0, LPDDR3_MR1_OP};
            end
            S_L_MR2: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(2, LPDDR3_MR2_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd2;
                mr_seq_data_o    = {8'd0, LPDDR3_MR2_OP};
            end
            S_L_MR3: begin
                init_cmd_valid_o = 1'b1;
                init_cmd_op_o    = OP_MRS;
                init_cmd_row_o   = mrw_row(3, LPDDR3_MR3_OP);
                mr_seq_we_o      = 1'b1;
                mr_seq_index_o   = 5'd3;
                mr_seq_data_o    = {8'd0, LPDDR3_MR3_OP};
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

endmodule : scoria_init_sequencer
