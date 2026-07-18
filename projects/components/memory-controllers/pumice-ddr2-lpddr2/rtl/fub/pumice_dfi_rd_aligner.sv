// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_rd_aligner
// Purpose: DFI read-data alignment (dfi_clk). On an admitted READ op, drive
//          dfi_rddata_en for the read window starting t_rddata_en DFI cycles
//          later; capture dfi_rddata as the PHY returns it and push one
//          DFI-word/cycle into the read CDC FIFO {last, resp, data}.
//
//          MULTI-OUTSTANDING with a safe valid/ready handshake: a read is
//          admitted on op_valid_i && op_ready_o. Up to MAX_OUTSTANDING reads may
//          be in flight (data returns many cycles after the command, and reads
//          issue every tCCD). op_ready_o deasserts when MAX_OUTSTANDING reads are
//          already outstanding, backpressuring READ-command issue so the aligner
//          never loses track. Size MAX_OUTSTANDING >= the read CAM depth and
//          op_ready never deasserts in steady state (the CAM is the admission
//          gate) — the handshake is the just-in-case safety net.
//
//          Two knobs the rearchitecture had conflated are now separate:
//            EN_CYC   = rddata_en window width (DFI cycles = DRAM DQ-bus
//                       occupancy of one read, ceil(BL/DFI_RATE)).
//            BL_WORDS = DFI words captured + pushed per read.
//          These are equal only when the pumice DRAM beat == the device word.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_rd_aligner #(
    parameter int DFI_DATA_WIDTH  = 128,
    parameter int DFI_RATE        = 2,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int BL_WORDS        = 4,          // DFI words captured per read
    parameter int EN_CYC          = BL_WORDS,   // rddata_en window width (DQ occupancy)
    parameter int MAX_OUTSTANDING = 8,          // outstanding-read tracking depth (exposed)
    parameter int RDEN_W          = 8,
    // Per-beat read-DESKEW: the a7ddrphy returns the two 64b beats of a 128b DFI
    // word at DIFFERENT capture latencies (the two packed sub-reads arrive skewed
    // in time), so a single whole-word capture takes one beat correct and the
    // other stale. deskew_lo/hi independently delay the LOW/HIGH 64b beat capture
    // by 0..(2^DESKEW_W-1) DFI cycles to realign them. Trainable at bring-up
    // (sweep for beats_mismatched==0). deskew=0/0 is BIT-IDENTICAL (a plain pipe).
    // Param-controlled width: 1 bit (0..1 DFI cycle) is all the a7ddrphy half-word
    // skew needs and keeps the delay-lines to ONE stage (timing-friendly on tight
    // boards); widen only for a PHY with a >1-cycle beat skew.
    parameter int DESKEW_W        = 1           // bits per deskew field (max 2^W-1)
) (
    input  logic                        dfi_clk,
    input  logic                        dfi_rstn,

    input  logic [RDEN_W-1:0]           t_rddata_en_i,   // RD cmd -> rddata_en
    input  logic [DESKEW_W-1:0]         deskew_lo_i,     // low 64b beat capture delay
    input  logic [DESKEW_W-1:0]         deskew_hi_i,     // high 64b beat capture delay

    // Outstanding-read op interface (from pumice_dfi_cmd_path / scheduler).
    // A read is admitted (its rddata_en scheduled, its return tracked) on
    // op_valid_i && op_ready_o. op_ready_o = queue not full -> backpressure.
    input  logic                        op_valid_i,
    output logic                        op_ready_o,

    // DFI read-data bus (from PHY)
    output logic [DFI_EN_WIDTH-1:0]     dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]   dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]  dfi_rddata_valid_i,

    // read FIFO push (DFI-word granular): {data, resp, last} -> CDC rddata FIFO
    output logic                        rd_valid_o,
    input  logic                        rd_ready_i,
    output logic [DFI_DATA_WIDTH-1:0]   rd_data_o,
    output logic [1:0]                  rd_resp_o,
    output logic                        rd_last_o
);

    localparam logic [1:0] RESP_OKAY = 2'b00;
    localparam int CNTW = (BL_WORDS > 1) ? $clog2(BL_WORDS) : 1;
    localparam int OSW  = $clog2(MAX_OUTSTANDING + 1);

    // ---- admission + backpressure ------------------------------------------
    // r_outstanding = reads admitted but not yet fully captured. op_ready drops
    // when MAX_OUTSTANDING are in flight; issuing more reads then stalls until a
    // return frees a slot.
    logic [OSW-1:0] r_outstanding;
    logic           w_admit, w_read_done;
    assign op_ready_o = (r_outstanding < OSW'(MAX_OUTSTANDING));
    assign w_admit    = op_valid_i && op_ready_o;

    // ---- rddata_en window: a STATELESS delay line, EN_CYC wide --------------
    // A read admitted k cycles ago is "due" its rddata_en window over the cycles
    // [t_rddata_en, t_rddata_en+EN_CYC-1] after admit. Track admits in a shift
    // register and assert enable whenever any in-flight admit is inside its own
    // window -> any cadence (contiguous or tCCD-bubbled) handled by construction.
    localparam int MAX_RDDATA_EN = 31;                 // DFI cycles; DDR2/3 rd-lat fits
    localparam int PIPE          = MAX_RDDATA_EN + EN_CYC;

    logic [PIPE-1:0] r_age;
    logic [PIPE:0]   w_fired;
    assign w_fired = {r_age, w_admit};

    logic w_en;
    always_comb begin
        w_en = 1'b0;
        for (int b = 0; b < EN_CYC; b++) begin
            automatic int unsigned idx = int'(t_rddata_en_i) + b;
            if (idx <= PIPE) w_en |= w_fired[idx];
        end
    end
    assign dfi_rddata_en_o = w_en ? {DFI_EN_WIDTH{1'b1}} : '0;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) r_age <= '0;
        else                         r_age <= {r_age[PIPE-2:0], w_admit};
    )

    // ---- per-beat DESKEW: independent LO/HI 64b capture delay lines ----------
    localparam int HW   = DFI_DATA_WIDTH / 2;          // one 64b beat
    localparam int DMAX = (1 << DESKEW_W) - 1;         // max deskew (DFI cycles)

    // Registered pipe of each raw 64b beat + word-valid. Element k = the value
    // (k+1) cycles ago; "age 0" is the COMBINATIONAL current input (below), so
    // deskew 0/0 adds NO latency.
    logic [HW-1:0]  r_lo_p [DMAX];
    logic [HW-1:0]  r_hi_p [DMAX];
    logic [DMAX-1:0] r_vld_p;
    logic           w_raw_valid;
    assign w_raw_valid = |dfi_rddata_valid_i;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            for (int k = 0; k < DMAX; k++) begin r_lo_p[k] <= '0; r_hi_p[k] <= '0; end
            r_vld_p <= '0;
        end else begin
            r_lo_p[0]  <= dfi_rddata_i[HW-1:0];
            r_hi_p[0]  <= dfi_rddata_i[DFI_DATA_WIDTH-1:HW];
            r_vld_p[0] <= w_raw_valid;
            for (int k = 1; k < DMAX; k++) begin
                r_lo_p[k]  <= r_lo_p[k-1];
                r_hi_p[k]  <= r_hi_p[k-1];
                r_vld_p[k] <= r_vld_p[k-1];
            end
        end
    )

    // Capture at the (runtime) max-deskew delay so ADDED LATENCY == the actual
    // skew; tap each beat at age (maxsk - its deskew) — the later beat taps age 0
    // (live), the earlier beat taps back to align with it. age 0 => combinational
    // current. deskew 0/0 => maxsk 0 => rd_data_o == dfi_rddata_i with the RAW
    // valid => BIT-IDENTICAL, zero added latency.
    logic [DESKEW_W-1:0] w_maxsk, w_lo_age, w_hi_age;
    logic [HW-1:0]       w_lo_al, w_hi_al;
    assign w_maxsk  = (deskew_lo_i > deskew_hi_i) ? deskew_lo_i : deskew_hi_i;
    assign w_lo_age = w_maxsk - deskew_lo_i;
    assign w_hi_age = w_maxsk - deskew_hi_i;
    assign w_lo_al  = (w_lo_age == '0) ? dfi_rddata_i[HW-1:0]
                                       : r_lo_p[int'(w_lo_age) - 1];
    assign w_hi_al  = (w_hi_age == '0) ? dfi_rddata_i[DFI_DATA_WIDTH-1:HW]
                                       : r_hi_p[int'(w_hi_age) - 1];

    // ---- capture: BL_WORDS per outstanding read, in order -------------------
    // Capture only while a read is outstanding (a WIDE admit->return gate that
    // drops truly-stray valids arriving with nothing in flight). r_rcnt counts
    // words within the current read; the BL_WORDS-th word marks last and retires
    // one outstanding read.
    logic [CNTW:0] r_rcnt;
    logic          w_word_valid, w_cap_fire;
    assign w_word_valid = (w_maxsk == '0) ? w_raw_valid : r_vld_p[int'(w_maxsk) - 1];
    assign w_cap_fire   = w_word_valid && (r_outstanding != '0) && rd_ready_i;
    assign w_read_done  = w_cap_fire && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

    assign rd_valid_o = w_word_valid && (r_outstanding != '0);
    assign rd_data_o  = {w_hi_al, w_lo_al};
    assign rd_resp_o  = RESP_OKAY;
    assign rd_last_o  = rd_valid_o && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

    // ---- param-gated on-silicon deskew debug (mark_debug) --------------------
    // Compiled only with +define+DESKEW_DEBUG (the ILA build), zero cost to the
    // release build. Answers the board question that sim can't: does the deskew
    // CSR actually reach THIS aligner, and does it shift the captured word?
    //   - w_dbg_deskew_lo/hi : the deskew value arriving at the aligner (proves
    //                          the CSR->core->layer->aligner thread on silicon).
    //   - w_dbg_rd_raw       : the raw two 64b beats straight off the PHY bus.
    //   - w_dbg_rd_data      : the DESKEWED word pushed to the CDC FIFO.
    // If deskew_hi steps 0..1 and w_dbg_rd_data's high beat visibly shifts ->
    // deskew works, the real skew != the model (case b). If it never shifts ->
    // the value isn't reaching the aligner (case a, a thread gap).
`ifdef DESKEW_DEBUG
    (* mark_debug = "true" *) logic [DESKEW_W-1:0]        w_dbg_deskew_lo;
    (* mark_debug = "true" *) logic [DESKEW_W-1:0]        w_dbg_deskew_hi;
    (* mark_debug = "true" *) logic [DFI_DATA_WIDTH-1:0]  w_dbg_rd_raw;
    (* mark_debug = "true" *) logic [DFI_DATA_WIDTH-1:0]  w_dbg_rd_data;
    (* mark_debug = "true" *) logic                       w_dbg_word_valid;
    (* mark_debug = "true" *) logic                       w_dbg_rd_valid;
    assign w_dbg_deskew_lo  = deskew_lo_i;
    assign w_dbg_deskew_hi  = deskew_hi_i;
    assign w_dbg_rd_raw     = dfi_rddata_i;
    assign w_dbg_rd_data    = rd_data_o;
    assign w_dbg_word_valid = w_word_valid;
    assign w_dbg_rd_valid   = rd_valid_o;
`endif

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_rcnt        <= '0;
            r_outstanding <= '0;
        end else begin
            r_outstanding <= r_outstanding
                           + (w_admit     ? OSW'(1) : OSW'(0))
                           - (w_read_done ? OSW'(1) : OSW'(0));
            if (w_cap_fire) begin
                if (r_rcnt == (CNTW+1)'(BL_WORDS - 1)) r_rcnt <= '0;   // read done
                else                                    r_rcnt <= r_rcnt + 1'b1;
            end
        end
    )

endmodule : pumice_dfi_rd_aligner
