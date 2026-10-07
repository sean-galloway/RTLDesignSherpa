// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_beat_packer
// Description: Repacks a bit stream so only a block's LAST beat is partial.
//
//   bch_encoder_core finishes its data phase and starts parity on a FRESH beat,
//   so when k does not fill a beat its output carries a partial beat
//   MID-codeword. bch_decoder_core's contract is the opposite: in_keep may be
//   partial only on a block's last beat, and given one earlier it flags the
//   block mis-framed and passes it through uncorrected. This block closes the
//   gap by accumulating bits and emitting full beats while it can, flushing
//   whatever remains as a final partial beat on the block boundary.
//
//   The bit sequence is unchanged; only the beat alignment is. The beat COUNT
//   can shrink, which is the point: a packed codeword is exactly ceil(n/B)
//   beats.
//
// Parameters:
//   BITS_PER_BEAT  B bits per beat, bit 0 in the low lane
//
// Notes:
//   - The accumulator holds 2B bits. Input is accepted while at most B are
//     held, so there is always room for a whole beat; a full beat is emitted
//     while at least B are held. Both can happen in the same cycle.
//   - in_keep must be low-aligned, which is the house contract.
//   - While flushing a block the input is held off for the cycle or two the
//     tail takes. That costs throughput only at a block boundary, where the
//     encoder is draining its parity anyway.
module bch_beat_packer #(
    parameter int BITS_PER_BEAT = 8,
    // derived
    parameter int DATA_WIDTH    = BITS_PER_BEAT
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    input  logic                       in_valid,
    output logic                       in_ready,
    input  logic [DATA_WIDTH-1:0]      in_data,
    input  logic [BITS_PER_BEAT-1:0]   in_keep,   // low-aligned
    input  logic                       in_last,

    output logic                       out_valid,
    input  logic                       out_ready,
    output logic [DATA_WIDTH-1:0]      out_data,
    output logic [BITS_PER_BEAT-1:0]   out_keep,  // partial ONLY with out_last
    output logic                       out_last
);

    localparam int M   = 1;                         // one bit per "symbol"
    localparam int S   = BITS_PER_BEAT;             // symbols per beat = bits
    localparam int ACC = 2 * S;                     // accumulator, in bits
    localparam int HW  = $clog2(ACC + 1);            // width of the held count

    logic [ACC*M-1:0] r_acc;
    logic [HW-1:0]    r_held;
    logic             r_flush;                      // in_last seen, tail pending
    // While flushing, how many of the held bits belong to the block being
    // closed out. The accumulator is a bit FIFO -- oldest in the low lanes --
    // so the next block's head can sit ABOVE the tail without mixing with it.
    logic [HW-1:0]    r_cur;

    // -- how many bits this input beat carries -------------------------------
    logic [HW-1:0] w_cnt;
    always_comb begin
        w_cnt = '0;
        for (int j = 0; j < S; j++) if (in_keep[j]) w_cnt = w_cnt + HW'(1);
    end

    logic             w_in_fire, w_out_fire;
    logic [HW-1:0]    w_avail;        // bits eligible to leave this cycle
    logic [HW-1:0]    w_shift;        // bits leaving
    logic [HW-1:0]    w_base;         // where an accepted beat appends
    logic [DATA_WIDTH-1:0] w_masked;

    // -- fall-through merge --------------------------------------------------
    logic [HW-1:0] w_ft_total;        // held + arriving, the merge's material
    logic          w_ft_full;         // the merge fills a whole beat
    logic          w_ft_last;         // the merge IS the block's tail
    logic          w_ft;              // any fall-through emit this cycle

    assign w_ft_total = r_held + w_cnt;
    assign w_ft_full  = !r_flush && in_valid
                      && (r_held != '0) && (r_held < HW'(S))
                      && (w_ft_total >= HW'(S));
    assign w_ft_last  = !r_flush && in_valid && in_last
                      && (r_held != '0) && (r_held < HW'(S))
                      && (w_ft_total <= HW'(S));
    assign w_ft       = w_ft_full || w_ft_last;

    // -- handshakes ----------------------------------------------------------
    assign in_ready  = ((w_cnt <= (HW'(ACC) - w_base)) || (w_ft && out_ready))
                    && !r_flush;
    assign w_avail   = r_flush ? r_cur : r_held;
    assign out_valid = (w_avail >= HW'(S)) || (r_flush && (w_avail != '0)) || w_ft;

    logic w_full_beat;
    assign w_full_beat = (w_avail >= HW'(S)) || w_ft_full;
    assign out_last    = (r_flush && (w_avail <= HW'(S)) && (w_avail != '0))
                      || w_ft_last;

    assign out_data = w_ft ? (r_acc[0 +: DATA_WIDTH] | (w_masked << (r_held * M)))
                           :  r_acc[0 +: DATA_WIDTH];

    always_comb begin
        if (w_ft_last) begin
            for (int j = 0; j < S; j++) out_keep[j] = (HW'(j) < w_ft_total);
        end else begin
            out_keep = {S{1'b1}};
            if (!w_full_beat)
                for (int j = 0; j < S; j++) out_keep[j] = (HW'(j) < w_avail);
        end
    end

    // -- the accumulator -----------------------------------------------------
    assign w_in_fire  = in_valid  && in_ready;
    assign w_out_fire = out_valid && out_ready;

    logic [HW-1:0] w_emit;            // bits leaving, either source
    logic [HW-1:0] w_consume;         // of those, lanes eaten from the input

    always_comb begin
        w_emit    = w_full_beat ? HW'(S) : (w_ft_last ? w_ft_total : w_avail);
        w_shift   = '0;
        w_consume = '0;
        if (w_out_fire) begin
            w_shift   = w_ft ? r_held : w_emit;
            w_consume = w_ft ? (w_emit - r_held) : '0;
        end
        w_base = r_held - w_shift;
        w_masked = '0;
        for (int j = 0; j < S; j++)
            if (in_keep[j]) w_masked[j*M +: M] = in_data[j*M +: M];
    end

    localparam int SHW = $clog2(ACC * M + 1);
    logic [SHW-1:0]   w_shift_bits, w_base_bits, w_consume_bits;
    logic [ACC*M-1:0] w_next_acc;

    assign w_shift_bits   = SHW'(w_shift * M);
    assign w_base_bits    = SHW'(w_base  * M);
    assign w_consume_bits = SHW'(w_consume * M);

    always_comb begin
        w_next_acc = r_acc >> w_shift_bits;
        if (w_in_fire)
            w_next_acc = w_next_acc
                       | (({{(ACC-S)*M{1'b0}}, w_masked} >> w_consume_bits)
                          << w_base_bits);
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_acc <= '0; r_held <= '0; r_flush <= 1'b0; r_cur <= '0;
        end else begin
            r_acc  <= w_next_acc;
            r_held <= w_base + (w_in_fire ? (w_cnt - w_consume) : HW'(0));
            if (w_in_fire && in_last) begin
                if (w_ft_last && w_out_fire) begin
                    r_flush <= 1'b0;
                    r_cur   <= '0;
                end else begin
                    r_flush <= 1'b1;
                    r_cur   <= w_base + (w_cnt - w_consume);
                end
            end else if (w_out_fire && out_last) begin
                r_flush <= 1'b0;
                r_cur   <= '0;
            end else if (r_flush) begin
                r_cur   <= r_cur - w_shift;
            end
        end
    end

endmodule
