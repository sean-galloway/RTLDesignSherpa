// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_beat_packer
// Description: Repacks a symbol stream so only a block's LAST beat is partial.
//
//   rs_encoder_core finishes its data phase and starts parity on a FRESH beat,
//   so when k does not fill a beat its output carries a partial beat
//   MID-codeword. rs_decoder_core's contract is the opposite: in_keep may be
//   partial only on a block's last beat, and given one earlier it flags the
//   block mis-framed and passes it through uncorrected. That made an encoder
//   output undecodable at those profiles (PRD D9b) -- RS(255,239) and RS(15,9)
//   at 4 symbols per beat, among 124 in a small sweep.
//
//   This block closes the gap. It accumulates symbols and emits full beats
//   while it can, flushing whatever remains as a final partial beat on the
//   block boundary. The symbol sequence is unchanged; only the beat alignment
//   is. The beat COUNT can shrink -- RS(15,9) goes from 5 beats to 4 -- which
//   is the point: the encoder's layout wastes the lanes after a mid-codeword
//   partial, and a packed codeword is exactly ceil(n/S) beats.
//
// Parameters:
//   SYMBOL_WIDTH      GF(2^m) symbol width, m
//   SYMBOLS_PER_BEAT  S symbols per beat, symbol 0 in the low lanes
//
// Notes:
//   - The accumulator holds 2S symbols. Input is accepted while at most S are
//     held, so there is always room for a whole beat; a full beat is emitted
//     while at least S are held. Both can happen in the same cycle, so the
//     steady-state rate is one beat in and one beat out.
//   - in_keep must be low-aligned, which is the house contract. A hole in the
//     middle of a beat would be silently closed up rather than flagged, and
//     nothing in this design produces one.
//   - While flushing a block the input is held off for the cycle or two the
//     tail takes. That costs throughput only at a block boundary, where the
//     encoder is draining its parity anyway.
module rs_beat_packer #(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int SYMBOLS_PER_BEAT = 4,
    // derived
    parameter int DATA_WIDTH       = SYMBOL_WIDTH * SYMBOLS_PER_BEAT
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic [SYMBOLS_PER_BEAT-1:0] in_keep,   // low-aligned
    input  logic                        in_last,

    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,  // partial ONLY with out_last
    output logic                        out_last
);

    localparam int M   = SYMBOL_WIDTH;
    localparam int S   = SYMBOLS_PER_BEAT;
    localparam int ACC = 2 * S;                    // accumulator, in symbols
    localparam int HW  = $clog2(ACC + 1);          // width of the held count

    logic [ACC*M-1:0] r_acc;
    logic [HW-1:0]    r_held;
    logic             r_flush;                     // in_last seen, tail pending

    // -- how many symbols this input beat carries --------------------------
    logic [HW-1:0] w_cnt;
    always_comb begin
        w_cnt = '0;
        for (int j = 0; j < S; j++) if (in_keep[j]) w_cnt = w_cnt + HW'(1);
    end

    // -- handshakes --------------------------------------------------------
    // Accept while at most S are held: cnt <= S, so 2S is always enough.
    // Hold off during a flush so the tail of one block cannot be mixed with
    // the head of the next.
    assign in_ready  = (r_held <= HW'(S)) && !r_flush;
    assign out_valid = (r_held >= HW'(S)) || (r_flush && (r_held != '0));

    // A full beat unless this is the block's tail. out_last rides the final
    // emit: with the flush pending and no more than S held, this is it.
    logic w_full_beat;
    assign w_full_beat = (r_held >= HW'(S));
    assign out_last    = r_flush && (r_held <= HW'(S));
    assign out_data    = r_acc[0 +: DATA_WIDTH];

    always_comb begin
        out_keep = {S{1'b1}};
        if (!w_full_beat)
            for (int j = 0; j < S; j++) out_keep[j] = (HW'(j) < r_held);
    end

    // -- the accumulator ---------------------------------------------------
    logic             w_in_fire, w_out_fire;
    logic [HW-1:0]    w_shift;        // symbols leaving
    logic [HW-1:0]    w_base;         // where an accepted beat appends
    logic [DATA_WIDTH-1:0] w_masked;

    assign w_in_fire  = in_valid  && in_ready;
    assign w_out_fire = out_valid && out_ready;

    always_comb begin
        w_shift = '0;
        if (w_out_fire) w_shift = w_full_beat ? HW'(S) : r_held;
        w_base = r_held - w_shift;
        // only the kept lanes carry meaning; zero the rest so the append is
        // a clean OR rather than depending on what the producer left behind
        w_masked = '0;
        for (int j = 0; j < S; j++)
            if (in_keep[j]) w_masked[j*M +: M] = in_data[j*M +: M];
    end

    // Next accumulator, as a wire rather than a procedural local: shift out
    // what was emitted this cycle, then append what was accepted. Both can
    // happen together, which is what keeps the steady-state rate at one beat.
    // The shift amounts are in BITS and must be computed at full width.
    // Writing them as `w_shift * HW'(M)` makes the product HW bits wide, and a
    // shift of S symbols at m = 8 is 32 bits, which truncates to 0 in a 4-bit
    // HW -- the accumulator then never drains and each new beat is OR-ed on
    // top of the one still sitting in the low lanes. The symptom is specific:
    // the beat count, keep contract and out_last placement all stay CORRECT,
    // because those are computed from the symbol count, and only the data is
    // wrong, from the second beat onward. Multiplying by the int localparam M
    // keeps the expression 32 bits wide.
    localparam int SHW = $clog2(ACC * M + 1);
    logic [SHW-1:0]   w_shift_bits, w_base_bits;
    logic [ACC*M-1:0] w_next_acc;

    assign w_shift_bits = SHW'(w_shift * M);
    assign w_base_bits  = SHW'(w_base  * M);

    always_comb begin
        w_next_acc = r_acc >> w_shift_bits;
        if (w_in_fire)
            w_next_acc = w_next_acc
                       | ({{(ACC-S)*M{1'b0}}, w_masked} << w_base_bits);
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_acc <= '0; r_held <= '0; r_flush <= 1'b0;
        end else begin
            r_acc  <= w_next_acc;
            r_held <= w_base + (w_in_fire ? w_cnt : HW'(0));
            if (w_in_fire && in_last)        r_flush <= 1'b1;
            else if (w_out_fire && out_last) r_flush <= 1'b0;
        end
    end

endmodule
