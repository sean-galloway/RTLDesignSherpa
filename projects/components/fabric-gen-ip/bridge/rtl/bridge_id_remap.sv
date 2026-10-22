`timescale 1ns / 1ps
`include "reset_defs.svh"
//==============================================================================
// Module: bridge_id_remap
// Description: Per-master, per-direction transaction-ID remap table.
//
// Purpose:
//   Inside the fabric a transaction ID is {master index, master-local ID}.
//   Carrying the master's own ID as the local part makes every slave-side ID,
//   and every per-ID structure downstream (the width converters keep R state
//   per ID), as wide as the widest master's ID plus the index bits: an 8-bit
//   master behind a 5-master bridge gives 11-bit IDs and 2048-entry per-ID
//   tables. A master can only have DEPTH requests in flight per direction,
//   so at most DEPTH distinct IDs are live at once, and $clog2(DEPTH) bits
//   name them all. This table hands out those short names (slots).
//
//   Request: the request's ID is matched against the live entries. A hit
//   reuses that entry's slot, so requests of one ID keep one fabric ID and
//   stay ordered at the slave; a miss takes the lowest free slot. The slot is
//   the local part of the fabric ID.
//   Response: the slot in the returned ID indexes the table and gives back
//   the original ID. The entry frees when its last outstanding response is
//   taken.
//
//   The table also keeps each live ID's target (one-hot slave select) and an
//   optional per-ID metadata word (the request's trace, on trace-echo ports),
//   and refuses a request whose ID is live toward a different target or with
//   different metadata (req_ok): responses of one ID must return in order,
//   and two slaves cannot order between themselves.
//
// Parameters:
//   ID_WIDTH  - the master's ID width, >= 1
//   DEPTH     - outstanding requests (the master's max_outstanding), a power
//               of two 2..64; slots are $clog2(DEPTH) bits
//   NUM_TGT   - width of the one-hot target select, >= 1
//   META_WIDTH - per-ID metadata bits, >= 1 (tie req_meta off if unused)
//
// Notes:
//   - req_slot, req_ok are combinational from req_id/req_tgt/req_meta and
//     registered state; full is a registered flag. The caller gates its
//     handshake with req_ok && !full and pushes on the handshake.
//   - full is high when DEPTH requests are outstanding, so a miss always
//     finds a free slot: a live entry has at least one request outstanding.
//   - One push and one pop per cycle. A pop is counted the cycle after it is
//     taken, so the entry it frees, and the outstanding count, follow a
//     cycle late (out_cnt then includes it): conservative, never early.
//   - rsp_id/rsp_meta are combinational from rsp_slot; a response must carry
//     a slot that has a request outstanding.
//   - The table is written into the lowest free slot every cycle, with no
//     dependence on the request: a free entry's contents are don't-care, and
//     the push that makes it live is the cycle it captures. Keeping the ID
//     compare out of the write enable is what timing needs (it was the
//     fabric's worst path, ID -> hit -> slot encode -> decode -> CE).
//   - Properties are proven in formal/bridge/bridge_id_remap.
//==============================================================================

module bridge_id_remap #(
    parameter int ID_WIDTH   = 8,
    parameter int DEPTH      = 16,
    parameter int NUM_TGT    = 4,
    parameter int META_WIDTH = 1,
    localparam int SW        = $clog2(DEPTH)
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    // Request (lookup is combinational; push on the request handshake)
    input  logic [ID_WIDTH-1:0]   req_id,
    input  logic [NUM_TGT-1:0]    req_tgt,
    input  logic [META_WIDTH-1:0] req_meta,
    input  logic                  req_push,
    output logic [SW-1:0]         req_slot,
    output logic                  req_ok,
    output logic                  full,

    // Response (pop on the handshake of a request's final response)
    input  logic [SW-1:0]         rsp_slot,
    input  logic                  rsp_pop,
    output logic [ID_WIDTH-1:0]   rsp_id,
    output logic [META_WIDTH-1:0] rsp_meta,

    // Requests outstanding, 0..DEPTH (a pop counts a cycle late)
    output logic [SW:0]           out_cnt
);

    logic [ID_WIDTH-1:0]   r_id   [DEPTH];
    logic [NUM_TGT-1:0]    r_tgt  [DEPTH];
    logic [META_WIDTH-1:0] r_meta [DEPTH];
    logic [SW:0]           r_cnt  [DEPTH];
    logic [DEPTH-1:0]      r_live;        // r_cnt[i] != 0, kept as a flag

    // ---- request lookup ----------------------------------------------------
    // At most one live entry holds a given ID, so w_hit is one-hot or zero and
    // the hit slot is an AND-OR over it rather than an encoded index mux.
    logic [DEPTH-1:0]      w_hit;
    logic [DEPTH-1:0]      w_bad;         // hit, but toward another target/meta
    logic                  w_any_hit;
    logic [SW-1:0]         w_hit_slot, w_free_slot;
    logic [DEPTH-1:0]      w_free_oh;     // lowest free entry, one-hot (or 0)

    always_comb begin
        w_hit_slot = '0;
        for (int i = 0; i < DEPTH; i++) begin
            w_hit[i] = r_live[i] && (r_id[i] == req_id);
            w_bad[i] = w_hit[i] &&
                       (!(|(r_tgt[i] & req_tgt)) || (r_meta[i] != req_meta));
            if (w_hit[i]) begin
                w_hit_slot = w_hit_slot | SW'(i);
            end
        end
        w_any_hit = |w_hit;
        // Lowest free slot, encoded and one-hot (registered state only)
        w_free_slot = '0;
        w_free_oh   = '0;
        for (int i = DEPTH - 1; i >= 0; i--) begin
            if (!r_live[i]) begin
                w_free_slot = SW'(i);
                w_free_oh   = DEPTH'(1) << i;
            end
        end
    end

    assign req_slot = w_any_hit ? w_hit_slot : w_free_slot;
    // At most one entry hits, so "the hit agrees" is "no entry hits and
    // disagrees": one flat reduction, not an AND-OR mux of the hit's fields
    // followed by the compare (this gates AW/AR valid into the fabric).
    assign req_ok   = !(|w_bad);

    // ---- response restore --------------------------------------------------
    assign rsp_id   = r_id[rsp_slot];
    assign rsp_meta = r_meta[rsp_slot];

    // ---- state -------------------------------------------------------------
    // The pop is registered and counted a cycle late. rsp_slot comes out of
    // the response mux behind the path arbiter; decoding it into a count the
    // same cycle was the slowest path in the adapter. A late decrement only
    // keeps an entry live, and the table full, one cycle longer.
    logic [SW:0]      r_out_cnt;
    logic             r_pop;
    logic [SW-1:0]    r_pop_slot;
    logic [1:0]       w_net;   // {push, registered pop} on the outstanding count
    logic [DEPTH-1:0] w_inc, w_dec;

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            // one-hot direct: no encode of req_slot and compare back
            w_inc[i] = req_push && (w_any_hit ? w_hit[i] : w_free_oh[i]);
            w_dec[i] = r_pop    && (r_pop_slot == SW'(i));
        end
    end

    assign w_net   = {req_push, r_pop};
    assign out_cnt = r_out_cnt;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_cnt[i] <= '0;
            end
            r_live     <= '0;
            r_out_cnt  <= '0;
            full       <= 1'b0;
            r_pop      <= 1'b0;
            r_pop_slot <= '0;
        end else begin
            r_pop      <= rsp_pop;
            r_pop_slot <= rsp_slot;
            for (int i = 0; i < DEPTH; i++) begin
                r_cnt[i]  <= r_cnt[i] + (SW+1)'(w_inc[i]) - (SW+1)'(w_dec[i]);
                r_live[i] <= w_inc[i] || (r_cnt[i] > (SW+1)'(1)) ||
                             ((r_cnt[i] == (SW+1)'(1)) && !w_dec[i]);
            end
            case (w_net)
                2'b10:   r_out_cnt <= r_out_cnt + 1'b1;
                2'b01:   r_out_cnt <= r_out_cnt - 1'b1;
                default: r_out_cnt <= r_out_cnt;
            endcase
            full <= ((r_out_cnt == (SW+1)'(DEPTH))     && (w_net != 2'b01)) ||
                    ((r_out_cnt == (SW+1)'(DEPTH - 1)) && (w_net == 2'b10));
        end
    )

    // ID, target and metadata are only read while the entry is live, so the
    // lowest FREE entry is written every cycle with the current request: on
    // a miss push it captures the request as it goes live; on any other
    // cycle it writes an entry nobody reads. A hit leaves its live entry
    // alone (it already holds this ID, target and metadata -- req_ok). No
    // reset needed.
    always_ff @(posedge aclk) begin
        for (int i = 0; i < DEPTH; i++) begin
            if (w_free_oh[i]) begin
                r_id[i]   <= req_id;
                r_tgt[i]  <= req_tgt;
                r_meta[i] <= req_meta;
            end
        end
    end

endmodule : bridge_id_remap
