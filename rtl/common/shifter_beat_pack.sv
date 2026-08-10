// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: shifter_beat_pack
// Purpose: Packs incoming CHUNK_BITS-wide entries into a 2×CHUNK_BITS
//          staging register and drains configurable-size "beats" out
//          the low end. All shift/load/mux logic lives in this one
//          module so callers (e.g. an aligner needing to pack DFI
//          cycles into DRAM beats) don't have to invent their own
//          shift-and-compensate scheme.
//
//          Interface:
//          * push_valid/push_ready/push_data — one CHUNK_BITS entry
//            per handshake. push_ready asserts whenever there is
//            room for another whole chunk (i.e. count + CHUNK_BITS
//            <= 2*CHUNK_BITS).
//          * pop_valid/pop_ready/pop_data     — one beat per
//            handshake. Beat width in bits = 8 × (cfg_beat_bytes_m1
//            + 1). pop_valid asserts whenever the register holds at
//            least one whole beat.
//          * cfg_beat_bytes_m1 (8 bits, held stable per burst) —
//            selects the beat width. Encoded as (bytes - 1) so the
//            field covers 1..256 bytes across its 256 values.
//          * empty / count_bits_o — status for the wrapper.
//
//          Same-cycle push + pop is normal; the always_comb next-
//          state pattern applies pop first (drain low bits, shift
//          down), then push (indexed part-select at the post-pop
//          tail). A single NBA writes r_data / r_count so no
//          internal last-assignment race is possible.
//
//          Sizing guidance: pick CHUNK_BITS and MAX_BEAT_BYTES so
//          that any runtime beat width you'll use fits in the 2N
//          storage (i.e. cfg_beat_bytes × 8 <= 2 × CHUNK_BITS).
//          The parameters are independent so callers can right-size
//          both the ingress chunk width and the egress beat cap.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module shifter_beat_pack #(
    parameter int CHUNK_BITS     = 128,
    parameter int MAX_BEAT_BYTES = 16,
    // Runtime cfg field width. 8 bits → beat_bytes ∈ 1..256, 4 bits
    // → 1..16, etc. Set to whatever the caller actually needs to
    // encode; the internal beat-width plumbing scales with it.
    parameter int CFG_BITS       = 8,
    // Depth of the staging register in "chunks" (CHUNK_BITS units).
    // Default 2 = the "current + prefetched-next" arrangement. Bump
    // for callers that need to absorb a whole burst's worth before
    // it starts draining. Timing degrades with depth because the
    // pop-side barrel shifter widens.
    parameter int DEPTH_CHUNKS   = 2,

    // ---- derived (do not override) ----
    parameter int MAX_BEAT_BITS  = MAX_BEAT_BYTES * 8,
    parameter int STORAGE_BITS   = DEPTH_CHUNKS * CHUNK_BITS,
    parameter int COUNT_BITS     = $clog2(STORAGE_BITS + 1),
    // Index width for r_data / w_v_data part-selects. r_count uses one
    // extra bit so it can represent the "full" value (STORAGE_BITS),
    // but the part-select's base only needs to address 0..STORAGE_BITS-1.
    parameter int IDX_BITS       = $clog2(STORAGE_BITS)
) (
    input  logic                       clk,
    input  logic                       rst_n,

    // Beat width in bytes − 1. 0 → 1 byte; (2**CFG_BITS − 1) → 2**CFG_BITS bytes.
    input  logic [CFG_BITS-1:0]        cfg_beat_bytes_m1,

    // ---- push (from FIFO / upstream) ----
    input  logic                       push_valid,
    output logic                       push_ready,
    input  logic [CHUNK_BITS-1:0]      push_data,

    // ---- pop (one beat per handshake) ----
    output logic                       pop_valid,
    input  logic                       pop_ready,
    output logic [MAX_BEAT_BITS-1:0]   pop_data,

    // ---- status ----
    output logic                       empty,
    output logic [COUNT_BITS-1:0]      count_bits_o
);

    // ---------------------------------------------------------------
    // Elaboration-time contract: a beat must be strictly smaller
    // than the staging window, otherwise the module cannot
    // guarantee forward progress. DEPTH_CHUNKS must be at least 2
    // — a single-chunk staging register can't hold any partial-
    // beat residue while a new chunk lands.
    // ---------------------------------------------------------------
    initial begin : g_sizing_check
        if (DEPTH_CHUNKS < 2) begin
            $error("shifter_beat_pack: DEPTH_CHUNKS (%0d) must be >= 2",
                   DEPTH_CHUNKS);
        end
        if (MAX_BEAT_BITS >= STORAGE_BITS) begin
            $error("shifter_beat_pack: MAX_BEAT_BITS (%0d) must be < STORAGE_BITS (%0d = DEPTH_CHUNKS*CHUNK_BITS)",
                   MAX_BEAT_BITS, STORAGE_BITS);
        end
    end

    // ---------------------------------------------------------------
    // Registered state
    // ---------------------------------------------------------------
    logic [STORAGE_BITS-1:0]  r_data;
    logic [COUNT_BITS-1:0]    r_count;

    // ---------------------------------------------------------------
    // Runtime beat width in bits.
    //
    // Widen the cfg field by 4 bits so it can represent the biggest
    // beat any CFG_BITS-wide cfg can encode: (2**CFG_BITS) × 8. The
    // extra +3 accounts for the ×8 (byte→bit), the extra +1 for the
    // `bytes_m1 + 1`. The instantiator's MAX_BEAT_BYTES caps what
    // actually reaches pop_data; this width is just the counter math.
    // ---------------------------------------------------------------
    localparam int BEAT_BITS_W = CFG_BITS + 4;
    logic [BEAT_BITS_W-1:0] w_beat_bits;
    assign w_beat_bits =
        ({{(BEAT_BITS_W-CFG_BITS){1'b0}}, cfg_beat_bytes_m1}
         + {{(BEAT_BITS_W-1){1'b0}}, 1'b1}) << 3;

    // ---------------------------------------------------------------
    // Handshake / status combinational
    // ---------------------------------------------------------------
    assign empty      = (r_count == '0);
    // Room for another whole chunk: post-push count would be <= storage.
    assign push_ready = (r_count <= COUNT_BITS'(STORAGE_BITS - CHUNK_BITS));
    // COMMON-015: compare in the WIDER domain. This used to be
    //     (r_count >= COUNT_BITS'(w_beat_bits))
    // and a runtime cfg_beat_bytes_m1 encoding a beat wider than
    // 2**COUNT_BITS-1 truncated to 0 -- pop_valid degenerated to
    // (r_count != 0), the pop shifted w_v_data by the true (huge) width and
    // subtracted 0 from the count, so the packer asserted pop_valid forever
    // against corrupted accounting. Silent data corruption, where a stall
    // would have been obvious. Widening the comparison turns that misuse into
    // a clean stall: an over-wide beat simply never satisfies pop_valid.
    localparam int CMP_W = (BEAT_BITS_W > COUNT_BITS) ? BEAT_BITS_W : COUNT_BITS;
    logic [CMP_W-1:0] w_count_cmp, w_beat_cmp;
    assign w_count_cmp = CMP_W'(r_count);
    assign w_beat_cmp  = CMP_W'(w_beat_bits);

    assign pop_valid  = (w_count_cmp >= w_beat_cmp)
                     && (r_count != '0);

    // Low MAX_BEAT_BITS of r_data. MAX_BEAT_BITS < STORAGE_BITS
    // by definition (a beat is always strictly smaller than the
    // 2-chunk staging window), so a plain slice is well-defined.
    // When cfg_beat_bytes*8 < MAX_BEAT_BITS the upper bits are
    // stale bytes from the next beat in the pipe — the consumer
    // already knows the beat width from cfg and reads only the
    // low (cfg_beat_bytes_m1 + 1)*8 bits.
    assign pop_data = r_data[MAX_BEAT_BITS-1:0];

    // ---------------------------------------------------------------
    // Next-state — pop first, push second. Single NBA at the end
    // eliminates any internal same-cycle race.
    // ---------------------------------------------------------------
    logic [STORAGE_BITS-1:0] w_v_data;
    logic [COUNT_BITS-1:0]   w_v_count;

    always_comb begin
        w_v_data  = r_data;
        w_v_count = r_count;

        // 1. Pop — drain the low w_beat_bits, shift storage down.
        if (pop_valid && pop_ready) begin
            w_v_data  = w_v_data >> w_beat_bits;
            // Safe by construction now: the pop only fires when the wide
            // compare above passed, so w_beat_bits <= r_count <=
            // 2**COUNT_BITS-1 and this cast is exact.
            w_v_count = w_v_count - COUNT_BITS'(w_beat_bits);
        end

        // 2. Push — land the new chunk at [w_v_count +: CHUNK_BITS].
        //    w_v_count here is the POST-pop occupancy, so the push
        //    lands right above the still-valid bits, whether or not
        //    a pop fired this cycle.
        if (push_valid && push_ready) begin
            w_v_data[w_v_count[IDX_BITS-1:0] +: CHUNK_BITS] = push_data;
            w_v_count = w_v_count + COUNT_BITS'(CHUNK_BITS);
        end
    end

    `ALWAYS_FF_RST(clk, rst_n, begin
        if (`RST_ASSERTED(rst_n)) begin
            r_data  <= '0;
            r_count <= '0;
        end else begin
            r_data  <= w_v_data;
            r_count <= w_v_count;
        end
    end)

    assign count_bits_o = r_count;

endmodule : shifter_beat_pack
