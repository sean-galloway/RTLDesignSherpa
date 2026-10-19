// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal proof for bridge_id_remap (projects/components/fabric-gen-ip/bridge/rtl):
// the per-master transaction-ID remap table in a bridge master adapter.
//
// Configuration: ID_WIDTH=3, DEPTH=4 slots, NUM_TGT=2, META_WIDTH=1. Eight
// IDs over four slots, so IDs must share and recycle slots; two targets, so
// the same-ID-same-target gate is exercised.
//
// Environment:
//   requester -- any ID, one-hot target and metadata every cycle; pushes only
//                what the table accepts (req_ok && !full), as the adapter's
//                gate does.
//   responder -- pops a slot only while that slot has a request outstanding
//                (a shadow count per slot, from the slot each push was given).
//                Responses of one slot come back in push order: one slot is
//                one fabric ID, and the fabric keeps one ID's responses in
//                order.
//
// One request is WATCHED: the f_pick-th push, any of the first 16. From its
// push until its own response is taken:
//
// Proven:
//   ap_restore    a response on its slot restores its ID and metadata
//   ap_no_alias   no request of another ID is given its slot
//   ap_same_slot  every request of its ID is given its slot
//   ap_gate       a request of its ID toward another target, or with other
//                 metadata, is refused (req_ok low)
//   ap_count      out_cnt equals the requests outstanding plus a pop taken
//                 last cycle (the table counts a pop a cycle late); full is
//                 out_cnt == DEPTH
// Covered:
//   cp_recycle    the watched request answered after its slot has been
//                 reused, with every slot busy at some point

`timescale 1ns / 1ps

module formal_bridge_id_remap (
    input logic aclk,
    input logic aresetn
);

    localparam int IDW   = 3;
    localparam int DEPTH = 4;
    localparam int NT    = 2;
    localparam int MW    = 1;
    localparam int SW    = 2;

    (* anyseq *)   logic [IDW-1:0] f_id;
    (* anyseq *)   logic [NT-1:0]  f_tgt;
    (* anyseq *)   logic [MW-1:0]  f_meta;
    (* anyseq *)   logic           f_push_go, f_pop_go;
    (* anyseq *)   logic [SW-1:0]  f_pop_slot;
    (* anyconst *) logic [3:0]     f_pick;

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // ---- DUT -----------------------------------------------------------------
    logic [SW-1:0]  req_slot, rsp_slot;
    logic           req_ok, full, req_push, rsp_pop;
    logic [IDW-1:0] rsp_id;
    logic [MW-1:0]  rsp_meta;
    logic [SW:0]    out_cnt;

    bridge_id_remap #(
        .ID_WIDTH(IDW), .DEPTH(DEPTH), .NUM_TGT(NT), .META_WIDTH(MW)
    ) dut (
        .aclk, .aresetn,
        .req_id(f_id), .req_tgt(f_tgt), .req_meta(f_meta), .req_push,
        .req_slot, .req_ok, .full,
        .rsp_slot, .rsp_pop, .rsp_id, .rsp_meta,
        .out_cnt
    );

    // ---- environment -----------------------------------------------------------
    reg [SW:0] f_cnt [DEPTH];          // requests outstanding per slot
    reg [4:0]  f_npush;                // pushes so far (saturating)

    always @(*) assume ((f_tgt != '0) && ((f_tgt & (f_tgt - 1'b1)) == '0));  // one-hot

    assign req_push = aresetn && f_push_go && req_ok && !full;
    assign rsp_slot = f_pop_slot;
    assign rsp_pop  = aresetn && f_pop_go && (f_cnt[f_pop_slot] != '0);

    integer k;
    always @(posedge aclk) begin
        if (!aresetn) begin
            for (k = 0; k < DEPTH; k = k + 1) f_cnt[k] <= '0;
            f_npush <= '0;
        end else begin
            for (k = 0; k < DEPTH; k = k + 1)
                f_cnt[k] <= f_cnt[k] + (SW+1)'(req_push && (req_slot == SW'(k)))
                                     - (SW+1)'(rsp_pop  && (rsp_slot == SW'(k)));
            if (req_push && (f_npush != 5'h1F)) f_npush <= f_npush + 1'b1;
        end
    end

    // ---- the watched request ---------------------------------------------------
    reg            w_live, w_done;
    reg [IDW-1:0]  w_id;
    reg [SW-1:0]   w_slot;
    reg [NT-1:0]   w_tgt;
    reg [MW-1:0]   w_meta;
    reg [SW:0]     w_ahead;            // older requests on its slot still out
    reg            w_reused;           // its slot took another push after it

    wire w_take = req_push && (f_npush == {1'b0, f_pick}) && !w_live && !w_done;

    always @(posedge aclk) begin
        if (!aresetn) begin
            w_live   <= 1'b0;
            w_done   <= 1'b0;
            w_reused <= 1'b0;
            w_ahead  <= '0;
        end else if (w_take) begin
            w_live  <= 1'b1;
            w_id    <= f_id;
            w_slot  <= req_slot;
            w_tgt   <= f_tgt;
            w_meta  <= f_meta;
            w_ahead <= f_cnt[req_slot] - (SW+1)'(rsp_pop && (rsp_slot == req_slot));
        end else if (w_live) begin
            if (req_push && (req_slot == w_slot)) w_reused <= 1'b1;
            if (rsp_pop && (rsp_slot == w_slot)) begin
                if (w_ahead != '0) begin
                    w_ahead <= w_ahead - 1'b1;
                end else begin
                    w_live <= 1'b0;
                    w_done <= 1'b1;
                end
            end
        end
    end

    reg          f_pop_q;              // a pop taken last cycle, not yet counted
    always @(posedge aclk) f_pop_q <= aresetn && rsp_pop;

    reg [SW+2:0] f_sum;
    always @(*) begin
        f_sum = (SW+3)'(f_pop_q);
        for (k = 0; k < DEPTH; k = k + 1) f_sum = f_sum + (SW+3)'(f_cnt[k]);
    end

    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 3) begin
            ap_count: assert ((SW+3)'(out_cnt) == f_sum && full == (out_cnt == (SW+1)'(DEPTH)));
            if (w_live) begin
                if (rsp_pop && (rsp_slot == w_slot))
                    ap_restore:   assert (rsp_id == w_id && rsp_meta == w_meta);
                if (req_push && (req_slot == w_slot))
                    ap_no_alias:  assert (f_id == w_id);
                if (req_push && (f_id == w_id))
                    ap_same_slot: assert (req_slot == w_slot);
                if ((f_id == w_id) && ((f_tgt != w_tgt) || (f_meta != w_meta)))
                    ap_gate:      assert (!req_ok);
            end
            cp_recycle: cover (w_done && w_reused && f_npush >= 5'd8);
            cp_full:    cover (full && w_live);
        end
    end

endmodule
