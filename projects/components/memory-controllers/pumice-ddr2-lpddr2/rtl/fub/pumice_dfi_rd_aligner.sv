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
    parameter int RDEN_W          = 8
) (
    input  logic                        dfi_clk,
    input  logic                        dfi_rstn,

    input  logic [RDEN_W-1:0]           t_rddata_en_i,   // RD cmd -> rddata_en

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

    // ---- capture: BL_WORDS per outstanding read, in order -------------------
    // Capture only while a read is outstanding (a WIDE admit->return gate that
    // drops truly-stray valids arriving with nothing in flight). r_rcnt counts
    // words within the current read; the BL_WORDS-th word marks last and retires
    // one outstanding read.
    // Second gate: the ENABLE-WINDOW credit. The a7ddrphy asserts a PREAMBLE
    // dfi_rddata_valid one cycle BEFORE this read's enable window with the
    // device not driving DQ; r_outstanding does NOT exclude it (the read IS
    // outstanding then), so capturing it fires rd_last a word early and shifts
    // the whole stream. Credit accrues per ENABLE cycle and is spent per
    // captured word, so it cannot be non-zero before the window opens.
    //
    // COMBINATIONAL, and that is the whole difference between this working and
    // not. Under the a7_read_gated model the device drives data INSIDE the
    // enable window -- data and enable land on the SAME cycle -- so a purely
    // registered credit still reads 0 on the first enable cycle and drops the
    // first word. That is what broke the two a7gated uart cases when this was
    // tried with a registered credit (2026-09-15), and it is what dcaedce4b
    // ("make enable-window credit combinational") was fixing in July before it
    // too was reverted. Include this cycle's enable in the available credit.
    localparam int CRDW = $clog2((PIPE + 1) * BL_WORDS + 2) + 1;
    logic [CRDW-1:0] r_credit, w_credit_avail;
    assign w_credit_avail = r_credit + CRDW'(w_en ? 1 : 0);

    logic [CNTW:0] r_rcnt;
    logic          w_word_valid, w_cap_fire;
    assign w_word_valid = (|dfi_rddata_valid_i) && (w_credit_avail != '0);
    assign w_cap_fire   = w_word_valid && (r_outstanding != '0) && rd_ready_i;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) r_credit <= '0;
        else                         r_credit <= w_credit_avail
                                                 - CRDW'(w_cap_fire ? 1 : 0);
    )
    assign w_read_done  = w_cap_fire && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

    assign rd_valid_o = w_word_valid && (r_outstanding != '0);
    assign rd_data_o  = dfi_rddata_i;
    assign rd_resp_o  = RESP_OKAY;
    assign rd_last_o  = rd_valid_o && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

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

    // dfi_rddata_valid carries no backpressure: a beat presented while the
    // downstream FIFO is full is GONE, the burst framing goes short, and
    // the AR-order drain wedges behind it. The sizing contract (return
    // FIFO >= reads-in-flight (pumice_rd_return_ring DEPTH) x BL_WORDS)
    // makes this unreachable; the assertion
    // turns any future sizing break into a hard failure instead of a
    // silent data drop.
`ifndef SYNTHESIS
    // ---- credit-gate probe (+define+RD_ALIGN_TRACE) -------------------------
    // The enable-window credit is meant to reject exactly one thing: the PHY
    // preamble valid that arrives BEFORE this read's window. If it ever rejects
    // a valid that the device really was driving, that beat is gone and the
    // burst framing goes short -- the same damage the preamble does, from the
    // other direction. These two counters separate those cases, so "the credit
    // is eating real data" is a number rather than a theory.
    //
    //   blocked_pre  a valid rejected with NO read outstanding      -> stray/preamble
    //   blocked_real a valid rejected WHILE a read was outstanding  -> a DROPPED
    //                BEAT. Not "small is fine": this is a stream aligner, so a
    //                single dropped word shifts every later beat by one and the
    //                run ends "read engine did not complete" with the whole
    //                remainder mismatched. Any nonzero blocked_real is a defect
    //                in either the gate or the model driving it.
    //
    // The credit is CUMULATIVE, so a device whose valid leads the enable window
    // by a constant offset only trips this ONCE -- on the first read, before any
    // enable has minted credit. After that, credit banked from earlier enables
    // covers each early return. So a count of 1 does not mean "nearly right"; it
    // means "the very first return was thrown away".
    //
    // first_blk_* snapshots that first rejection so the cause is a reading, not
    // an inference: en_cycles==0 there proves the valid ARRIVED BEFORE ANY
    // ENABLE (an unphysical device model), while en_cycles>0 means credit was
    // minted and then mis-spent (a real gate bug).
    integer dbg_valids, dbg_captured, dbg_blocked_pre, dbg_blocked_real;
    integer dbg_en_cycles;
    integer dbg_first_en_time, dbg_first_valid_time;
    integer dbg_first_blk_time, dbg_first_blk_captured, dbg_first_blk_en_cycles;
    integer dbg_first_blk_outst;
    always @(posedge dfi_clk or negedge dfi_rstn)
        if (!dfi_rstn) begin
            dbg_valids <= 0; dbg_captured <= 0;
            dbg_blocked_pre <= 0; dbg_blocked_real <= 0;
            dbg_en_cycles <= 0;
            dbg_first_en_time <= -1; dbg_first_valid_time <= -1;
            dbg_first_blk_time <= -1; dbg_first_blk_captured <= -1;
            dbg_first_blk_en_cycles <= -1; dbg_first_blk_outst <= -1;
        end else begin
            if (|dfi_rddata_valid_i) dbg_valids <= dbg_valids + 1;
            if (w_cap_fire)          dbg_captured <= dbg_captured + 1;
            if (w_en)                dbg_en_cycles <= dbg_en_cycles + 1;
            if (w_en && (dbg_first_en_time < 0))
                dbg_first_en_time <= 32'($time);
            if ((|dfi_rddata_valid_i) && (dbg_first_valid_time < 0))
                dbg_first_valid_time <= 32'($time);
            if ((|dfi_rddata_valid_i) && (w_credit_avail == '0)) begin
                if (r_outstanding == '0) dbg_blocked_pre  <= dbg_blocked_pre + 1;
                else                     dbg_blocked_real <= dbg_blocked_real + 1;
                if (dbg_first_blk_time < 0) begin
                    dbg_first_blk_time      <= 32'($time);
                    dbg_first_blk_captured  <= dbg_captured;
                    dbg_first_blk_en_cycles <= dbg_en_cycles;
                    dbg_first_blk_outst     <= 32'(r_outstanding);
                end
            end
`ifdef RD_ALIGN_TRACE
            if (|dfi_rddata_valid_i)
                $display("RD_ALIGN @%0t valid data=%h credit=%0d(avail %0d) outst=%0d rcnt=%0d -> %s",
                         $time, dfi_rddata_i, r_credit, w_credit_avail,
                         r_outstanding, r_rcnt,
                         (w_credit_avail == '0) ? "BLOCKED" : "captured");
`endif
        end

    final begin
        $display("RD_ALIGNER probe: valids=%0d captured=%0d blocked_pre=%0d blocked_real=%0d",
                 dbg_valids, dbg_captured, dbg_blocked_pre, dbg_blocked_real);
        $display("RD_ALIGNER probe: en_cycles=%0d first_en=%0d first_valid=%0d",
                 dbg_en_cycles, dbg_first_en_time, dbg_first_valid_time);
        $display("RD_ALIGNER probe: first_block t=%0d captured_before=%0d en_cycles_before=%0d outst=%0d",
                 dbg_first_blk_time, dbg_first_blk_captured,
                 dbg_first_blk_en_cycles, dbg_first_blk_outst);
    end

    always @(posedge dfi_clk)
        if (dfi_rstn) begin
            assert (!(rd_valid_o && !rd_ready_i))
              else $error("RD_ALIGNER @%0t: read beat LOST (return FIFO full; rcnt=%0d outst=%0d) -- return-path sizing contract broken",
                          $time, r_rcnt, r_outstanding);
        end
`endif

endmodule : pumice_dfi_rd_aligner
