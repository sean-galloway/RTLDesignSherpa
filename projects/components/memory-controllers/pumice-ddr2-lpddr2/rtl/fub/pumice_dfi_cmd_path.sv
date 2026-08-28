// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_cmd_path
// Purpose: DFI-domain command path. Pops the abstract command stream (from the
//          CDC cmd FIFO), unpacks {op,rank,bank,row,col,ap}, and drives the
//          multi-phase DFI command bus via the silicon-proven dfi_cmd_formatter.
//          Emits wr_fire/rd_fire strobes (+ op) so the write serializer / read
//          aligner can schedule their data phases relative to the command.
//
// Runs entirely on dfi_clk (the CDC is the only crossing). One command per DFI
// cycle; for BL8 @ nphases=4 that is full DQ bandwidth.
//
// SUB-DFI-WORD BURST PACKING (task #146):
//   When one DFI word packs N_SUBCMD > 1 JEDEC bursts (the board: gear 1:4 + x16
//   BL4 => a BL4 burst is only 2 of the fixed nphases=4 phases, so N_SUBCMD=2
//   BL4 reads share ONE 128b DFI word), the N_SUBCMD sub-column-commands of a
//   single scheduled column command are issued in ONE DFI cycle at command
//   phases {base_phase, base_phase + sub_phase_stride, ...} (each sub at
//   col + sub*sub_col_stride). The a7ddrphy de-interleaver anchors each sub's
//   BL beats to its command phase, so all N_SUBCMD anchored runs land in the
//   SAME DFI word -> fully packed, zero stale (the earlier over-consecutive-
//   cycles expansion left the other phase-pair stale -> the on-board 2/4 read
//   corruption). ONE wr_fire/rd_fire group strobe is emitted for the whole
//   packed group, so the data path drives/captures the single DFI word once.
//   N_SUBCMD/SUB_COL_STRIDE/SUB_PHASE_STRIDE here are the COMPILE-TIME MAX
//   (build-for-max) that SIZE the fabric; the ACTIVE values are the runtime
//   n_subcmd_i/sub_col_stride_i/sub_phase_stride_i inputs (from the bl+gear
//   CSRs). At the board/default config the runtime values equal the MAX =>
//   bit-identical. MAX==1 => legacy single-command path (one formatter, phase 0).
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_cmd_path
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_RATE       = 4,
    // DQ-bus occupancy of one column burst in DFI cycles (= BL/DFI_RATE = the
    // burst's DFI-word count). A column (RD/WR) command owns the shared DQ bus
    // for this many cycles, so the next column command must be held that long or
    // its burst data collides with the previous burst. 1 => no pacing (issue a
    // column every cycle, valid only when BL == DFI_RATE).
    parameter int COL_BURST_CYC  = 1,
    // Sub-DFI-word burst packing (task #146). N_SUBCMD sub-column-commands of one
    // scheduled column command are issued in ONE DFI cycle at command phases
    // {base, base+SUB_PHASE_STRIDE, ...} and columns {col, col+SUB_COL_STRIDE,
    // ...}. These are the COMPILE-TIME MAX (build-for-max); the ACTIVE values are
    // the runtime n_subcmd_i/sub_col_stride_i/sub_phase_stride_i inputs.
    // MAX==1 => legacy single-command path.
    parameter int N_SUBCMD        = 1,
    parameter int SUB_COL_STRIDE  = 1,
    // Compile MAX DFI-phase stride between packed sub-bursts (= BL_PUMICE, the
    // active DRAM beats per burst = the phases one BL occupies). Sizes the phase
    // arithmetic; the ACTIVE stride is the runtime sub_phase_stride_i.
    parameter int SUB_PHASE_STRIDE = 1,
    parameter int DFI_ADDR_WIDTH = 14,
    parameter int DFI_BANK_WIDTH = 3,
    parameter int DFI_CTRL_WIDTH = 1,
    parameter int DFI_CS_WIDTH   = NUM_RANKS,

    parameter int DFI_ADDR_BUS_W = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W   = DFI_CS_WIDTH * DFI_RATE,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    // Packed command word: {ap, col, row, bank, rank, op}  (matches the
    // scheduler's cmd FIFO packing).
    parameter int CMD_DW = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1,
    // Sub-command COUNT width: holds the value N_SUBCMD (1..N_SUBCMD), so it
    // needs clog2(N_SUBCMD+1) bits (clog2(N) alone cannot represent N).
    parameter int SUBW_MAX = $clog2(N_SUBCMD + 1)
) (
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,
    input  memtype_e                   memtype_i,
    input  logic [PHW-1:0]             rd_phase_i,
    input  logic [PHW-1:0]             wr_phase_i,
    // ---- runtime sub-DFI-word framing (from bl+gear CSRs; <= compile MAX) ----
    // n_subcmd_i        : active sub-column commands packed into one DFI word (>=1).
    // sub_col_stride_i  : active device-word column stride between sub-bursts.
    // sub_phase_stride_i: active DFI-phase stride between sub-bursts (= bl_pumice).
    // Wrong values are BAD CONFIG, not a synth mismatch (sized for MAX above).
    input  logic [SUBW_MAX-1:0]        n_subcmd_i,
    input  logic [COL_WIDTH-1:0]       sub_col_stride_i,
    input  logic [PHW-1:0]             sub_phase_stride_i,

    // ---- abstract command in (from CDC cmd FIFO) ----
    input  logic                       cmd_valid_i,
    output logic                       cmd_ready_o,
    input  logic [CMD_DW-1:0]          cmd_data_i,

    // ---- DFI command bus (to dfi_signal_pack / PHY) ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,

    // ---- fire strobes to the data paths (1-cycle, on accepted command) ----
    output logic                       wr_fire_o,   // WR / WRA issued
    output logic                       rd_fire_o,   // RD / RDA issued
    input  logic                       rd_op_ready_i, // rd aligner has a free slot
    output logic [RKW-1:0]             fire_rank_o
);

    // ---- unpack the command word ----
    logic                w_ap;
    logic [COL_WIDTH-1:0] w_col;
    logic [ROW_WIDTH-1:0] w_row;
    logic [BKW-1:0]       w_bank;
    logic [RKW-1:0]       w_rank;
    dram_op_e             w_op;
    assign {w_ap, w_col, w_row, w_bank, w_rank, w_op} = cmd_data_i;

    // ---- DQ-bus occupancy pacing (column commands only) --------------------
    // A column command's burst owns the DQ bus for COL_BURST_CYC DFI cycles.
    // Hold the NEXT column command until that window clears; ACT/PRE/REF do not
    // touch the DQ bus and flow freely. In-order: a stalled column at the FIFO
    // head backpressures everything behind it (and, via the CDC, the arbiter).
    localparam int PCW = (COL_BURST_CYC <= 1) ? 1 : $clog2(COL_BURST_CYC);
    logic          w_is_wr, w_is_rd, w_is_col;
    assign w_is_wr  = (w_op == OP_WR) || (w_op == OP_WRA);
    assign w_is_rd  = (w_op == OP_RD) || (w_op == OP_RDA);
    assign w_is_col = w_is_wr || w_is_rd;

    logic [PCW-1:0] r_col_pace;
    logic           w_col_ok, w_gate;
    assign w_col_ok = (r_col_pace == '0);
    // Column pacing (DQ occupancy) AND, for reads, the aligner's outstanding-op
    // backpressure: hold a RD command if the read aligner's tracking queue is
    // full so no return is ever untracked. Sized so it never fires in steady
    // state (MAX_OUTSTANDING >= RD_CAM_DEPTH).
    assign w_gate   = ((!w_is_col) || w_col_ok) && (!w_is_rd || rd_op_ready_i);

    // ---- sub-DFI-word burst packing (task #146) ----------------------------
    // A column command that packs n_subcmd_i JEDEC bursts into one DFI word is
    // driven as n_subcmd_i sub-column-commands issued in ONE DFI cycle, each on
    // its own DFI phase (base + s*sub_phase_stride) at col + s*sub_col_stride.
    // One dfi_cmd_formatter per sub places its command on its phase; the buses
    // MERGE (cs/ctrl AND, addr/bank/odt OR) into a single multi-phase word, since
    // each active sub owns a DISTINCT phase and inactive subs/other phases are
    // NOP (cs_n/ctrl all-ones, addr/bank/odt zero). Non-column ops and the
    // runtime n_subcmd_i==1 case use ONLY sub 0 on the base phase => bit-identical
    // to the legacy single-formatter path. The whole packed group is one accepted
    // command (one FIFO pop, one fire) — the a7ddrphy returns/launches the packed
    // DFI word once.
    logic [SUBW_MAX-1:0] w_n_sub;   // active count, clamped to >=1
    assign w_n_sub = (n_subcmd_i == '0) ? SUBW_MAX'(1) : n_subcmd_i;

    // Base command phase: RD on rd_phase, WR on wr_phase, everything else phase 0.
    logic [PHW-1:0] w_base_phase;
    always_comb begin
        unique case (w_op)
            OP_RD, OP_RDA: w_base_phase = rd_phase_i;
            OP_WR, OP_WRA: w_base_phase = wr_phase_i;
            default:       w_base_phase = '0;
        endcase
    end

    // Per-sub placed command buses (one formatter each). Merged below.
    logic [DFI_ADDR_BUS_W-1:0] w_sub_address [N_SUBCMD];
    logic [DFI_BANK_BUS_W-1:0] w_sub_bank    [N_SUBCMD];
    logic [DFI_CTRL_BUS_W-1:0] w_sub_cas_n   [N_SUBCMD];
    logic [DFI_CTRL_BUS_W-1:0] w_sub_ras_n   [N_SUBCMD];
    logic [DFI_CTRL_BUS_W-1:0] w_sub_we_n    [N_SUBCMD];
    logic [DFI_CS_BUS_W-1:0]   w_sub_cs_n    [N_SUBCMD];
    logic [DFI_CS_BUS_W-1:0]   w_sub_odt     [N_SUBCMD];
    logic [N_SUBCMD-1:0]       w_sub_fmt_ready;

    genvar gs;
    generate
        for (gs = 0; gs < N_SUBCMD; gs++) begin : g_sub
            // This sub is active only when s < w_n_sub. Sub 0 is ALWAYS active
            // (non-column ops and n_subcmd==1 use it alone on the base phase).
            logic                sub_active;
            logic [PHW-1:0]      sub_phase;
            logic [COL_WIDTH-1:0] sub_col;
            assign sub_active = cmd_valid_i && w_gate
                              && (SUBW_MAX'(gs) < w_n_sub);
            // Phase / column for this sub. Only column ops fan out; ACT/PRE/REF/
            // MRS keep sub 0 on the base phase (their gs>0 subs are inactive).
            assign sub_phase  = w_base_phase
                              + PHW'(PHW'(gs) * sub_phase_stride_i);
            assign sub_col    = w_col
                              + COL_WIDTH'(COL_WIDTH'(gs) * sub_col_stride_i);

            // Drive this sub's command on sub_phase via rd_phase_i/wr_phase_i.
            // For a column op the base_phase IS rd/wr_phase, so passing sub_phase
            // as BOTH places the command correctly regardless of RD vs WR.
            dfi_cmd_formatter #(
                .NUM_RANKS      (NUM_RANKS),
                .NUM_BANKS      (NUM_BANKS),
                .ROW_WIDTH      (ROW_WIDTH),
                .COL_WIDTH      (COL_WIDTH),
                .BURST_LEN_WIDTH(BURST_LEN_WIDTH),
                .DFI_RATE       (DFI_RATE),
                .DFI_ADDR_WIDTH (DFI_ADDR_WIDTH),
                .DFI_BANK_WIDTH (DFI_BANK_WIDTH),
                .DFI_CTRL_WIDTH (DFI_CTRL_WIDTH),
                .DFI_CS_WIDTH   (DFI_CS_WIDTH)
            ) u_fmt (
                .mc_clk       (dfi_clk),
                .mc_rst_n     (dfi_rstn),
                .memtype_i    (memtype_i),
                .cmd_valid_i  (sub_active),
                .cmd_ready_o  (w_sub_fmt_ready[gs]),
                .cmd_op_i     (w_op),
                .cmd_rank_i   (w_rank),
                .cmd_bank_i   (w_bank),
                .cmd_row_i    (w_row),
                .cmd_col_i    (sub_col),
                .cmd_len_i    ('0),
                .rd_phase_i   (sub_phase),
                .wr_phase_i   (sub_phase),
                .dfi_address_o(w_sub_address[gs]),
                .dfi_bank_o   (w_sub_bank[gs]),
                .dfi_cas_n_o  (w_sub_cas_n[gs]),
                .dfi_ras_n_o  (w_sub_ras_n[gs]),
                .dfi_we_n_o   (w_sub_we_n[gs]),
                .dfi_cs_n_o   (w_sub_cs_n[gs]),
                .dfi_odt_o    (w_sub_odt[gs])
            );
        end
    endgenerate

    // Merge the per-sub placed buses into ONE multi-phase command word. Each
    // active sub owns a distinct phase; every other phase (and every inactive
    // sub) is NOP: cs_n/ras_n/cas_n/we_n = all-ones, addr/bank/odt = 0. So:
    //   * cs_n / *_n : AND across subs — a 0 (selected / asserted) on a sub's
    //     own phase wins; NOP all-ones elsewhere leaves the merge at NOP.
    //   * addr/bank/odt : OR across subs — the placed value on a sub's phase
    //     survives; 0 elsewhere.
    always_comb begin
        dfi_address_o = '0;
        dfi_bank_o    = '0;
        dfi_odt_o     = '0;
        dfi_cas_n_o   = '1;
        dfi_ras_n_o   = '1;
        dfi_we_n_o    = '1;
        dfi_cs_n_o    = '1;
        for (int s = 0; s < N_SUBCMD; s++) begin
            dfi_address_o |= w_sub_address[s];
            dfi_bank_o    |= w_sub_bank[s];
            dfi_odt_o     |= w_sub_odt[s];
            dfi_cas_n_o   &= w_sub_cas_n[s];
            dfi_ras_n_o   &= w_sub_ras_n[s];
            dfi_we_n_o    &= w_sub_we_n[s];
            dfi_cs_n_o    &= w_sub_cs_n[s];
        end
    end

    // Accept the (whole packed) command this cycle: sub 0's formatter is always
    // ready (it registers a constant 1), the pacing/backpressure gate is open.
    logic w_fmt_ready, w_fire;
    assign w_fmt_ready = w_sub_fmt_ready[0];
    assign w_fire      = cmd_valid_i && w_gate && w_fmt_ready;

    // Pop the FIFO once for the whole packed group (single cycle).
    assign cmd_ready_o = w_fmt_ready && w_gate;

    // DQ-occupancy pacing counter: loaded to COL_BURST_CYC-1 on the accepted
    // column group. COL_BURST_CYC==1 => loads 0 => never blocks. The packed
    // group occupies exactly one DFI word (BL_WORDS==1 in the sub-word regime).
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_col_pace <= '0;
        end else begin
            if (r_col_pace != '0) r_col_pace <= r_col_pace - 1'b1;
            if (w_fire && w_is_col) r_col_pace <= PCW'(COL_BURST_CYC - 1);
        end
    )

    // Group fire strobes (registered 1 cycle to align with the formatter's
    // registered command outputs). Emitted ONCE per column command for the whole
    // packed group — so the write serializer / read aligner drive/capture the
    // single DFI word exactly once even though N_SUBCMD DRAM commands were issued
    // (on N_SUBCMD phases of the SAME cycle).
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            wr_fire_o   <= 1'b0;
            rd_fire_o   <= 1'b0;
            fire_rank_o <= '0;
        end else begin
            wr_fire_o   <= w_fire && w_is_wr;
            rd_fire_o   <= w_fire && w_is_rd;
            fire_rank_o <= w_rank;
        end
    )

    // ---- ELABORATION assertion: RTL MIRROR of the DV contract ---------------
    // This mirrors CocoTBFramework.components.dfi.dfi_timing.bl_anchored_slot_mask
    // (the single source of truth the DV BFM + model proof use). The sub-word
    // packing geometry MUST satisfy the same power-of-two / burst rules so the
    // a7ddrphy de-interleaver packs all N_SUBCMD anchored runs into one DFI word:
    //   * DFI_RATE (nphases) is a power of two.
    //   * The compile-MAX phase stride (SUB_PHASE_STRIDE = BL_PUMICE) times
    //     N_SUBCMD covers exactly all DFI_RATE phases (N_SUBCMD * BL_PUMICE ==
    //     DFI_RATE): the N sub anchors {0, BL_PUMICE, 2*BL_PUMICE, ...} tile the
    //     nphases-phase cycle with no overlap and no gap -> zero stale.
    //   * The last sub's anchor (N_SUBCMD-1)*SUB_PHASE_STRIDE stays in range.
    // Non-sub-word builds (N_SUBCMD==1) trivially satisfy this.
    // synthesis translate_off
    initial begin
        assert ((DFI_RATE > 0) && ((DFI_RATE & (DFI_RATE - 1)) == 0))
            else $fatal(1, "pumice_dfi_cmd_path: DFI_RATE(%0d) must be power-of-two (RTL mirror of dfi_timing.bl_anchored_slot_mask nphases rule)", DFI_RATE);
        if (N_SUBCMD > 1) begin
            assert (N_SUBCMD * SUB_PHASE_STRIDE == DFI_RATE)
                else $fatal(1, "pumice_dfi_cmd_path: N_SUBCMD(%0d)*SUB_PHASE_STRIDE(%0d) != DFI_RATE(%0d) - sub-word anchors do not tile the DFI cycle (RTL mirror of the anchored-slot-mask contract)", N_SUBCMD, SUB_PHASE_STRIDE, DFI_RATE);
            assert ((N_SUBCMD - 1) * SUB_PHASE_STRIDE < DFI_RATE)
                else $fatal(1, "pumice_dfi_cmd_path: last sub anchor out of range");
        end
    end
    // synthesis translate_on

endmodule : pumice_dfi_cmd_path
