// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for ioapic_deliv_merge -- multi-IOAPIC routing, N delivery
// channels merged onto one (RLB-008).
//
// Every property is on PORTS. The arbiter's state is internal and stays that
// way: internal visibility fails on this toolchain for these blocks (see the
// rtc_config_regs proof header for the four routes that were tried). What
// matters here is visible at the boundary anyway -- that exactly one source is
// served at a time, that the merged payload is THAT source's, and that the
// retry goes back only to it.
//
//   P1  at most one source is ready at a time. Two would mean two IOAPICs
//       believing the same delivery slot consumed their message.
//   P2  at most one source is told to retry.
//   P3  retry only ever goes to a source that is simultaneously ready, i.e.
//       to the one whose handshake is completing. Broadcasting retry would
//       make every other IOAPIC replay an interrupt that was never theirs.
//   P4  a retry downstream is not invented upstream: if any source is told to
//       retry, m_retry is actually asserted.
//   P5  src_ready implies the merged channel is both valid and ready -- no
//       source is told its message went out when nothing went out.
//   P6  ROUTING, the reason this module exists: when the merged channel is
//       valid, its payload is the payload of the source named by m_src_id.
//       Getting this wrong delivers IOAPIC A's vector labelled as B's.
//   P7  the source named by m_src_id is actually requesting.
//
// PACKING. sv2v flattens UNPACKED array ports (src_vector, src_dest,
// src_deliv_mode) into packed vectors with REVERSE element order: element i
// lands at [((N-1)-i)*W +: W]. The already-packed vector ports (src_valid,
// src_dest_mode, src_ready, src_retry) are NOT reordered. Conflating the two
// is what made ap_grant_in_set fail against correct RTL in the sibling proof,
// so the two kinds are indexed differently below on purpose.

module formal_ioapic_deliv_merge (
    input logic clk,
    input logic rst_n
);

    localparam int NS  = 2;                 // sources
    localparam int SIW = (NS > 1) ? $clog2(NS) : 1;

    // Packed vector ports: normal bit order.
    (* anyseq *) reg [NS-1:0]    src_valid;
    (* anyseq *) reg [NS-1:0]    src_dest_mode;
    // Unpacked array ports, flattened by sv2v: REVERSE element order.
    (* anyseq *) reg [NS*8-1:0]  src_vector;
    (* anyseq *) reg [NS*8-1:0]  src_dest;
    (* anyseq *) reg [NS*3-1:0]  src_deliv_mode;

    (* anyseq *) reg             m_ready;
    (* anyseq *) reg             m_retry;

    wire [NS-1:0]   src_ready;
    wire [NS-1:0]   src_retry;
    wire            m_valid;
    wire [7:0]      m_vector;
    wire [7:0]      m_dest;
    wire            m_dest_mode;
    wire [2:0]      m_deliv_mode;
    wire [SIW-1:0]  m_src_id;

    ioapic_deliv_merge #(.NUM_SRC(NS)) dut (
        .clk            (clk),
        .rst_n          (rst_n),
        .src_valid      (src_valid),
        .src_vector     (src_vector),
        .src_dest       (src_dest),
        .src_dest_mode  (src_dest_mode),
        .src_deliv_mode (src_deliv_mode),
        .src_ready      (src_ready),
        .src_retry      (src_retry),
        .m_valid        (m_valid),
        .m_vector       (m_vector),
        .m_dest         (m_dest),
        .m_dest_mode    (m_dest_mode),
        .m_deliv_mode   (m_deliv_mode),
        .m_src_id       (m_src_id),
        .m_ready        (m_ready),
        .m_retry        (m_retry)
    );

    // ------------------------------------------------------------------
    // Reset sequence
    // ------------------------------------------------------------------
    // REQUIRED, and its absence is a real counterexample generator rather than
    // a formality. This DUT is sequential: without it, yosys starts the
    // arbiter's flops at anyinit values (they appear in the trace as
    // u_arb/_witness_/anyinit_procdff_*), so `grant` can be 2'b11 at step 1
    // with no reset ever applied and ap_ready_onehot0 fails against a module
    // that is perfectly correct. The arbiter drives grant one-hot-or-zero in
    // operation -- w_next_grant is cleared then one bit set -- and clears it
    // on reset; the counterexample was purely an unreachable initial state.
    //
    // The sibling ioapic_lowest_pri_arb proof has no such block because that
    // module is combinational and holds no state. Same idiom as
    // formal_drain_ctrl_beats.sv and formal_axi_write_engine.sv.
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    // ------------------------------------------------------------------
    // Environment: sources obey the delivery handshake
    // ------------------------------------------------------------------
    // A source may not withdraw src_valid before its src_ready. That is the
    // valid/ready contract, not a convenience: ioapic_core holds
    // irq_out_valid until irq_out_ready, and this merge runs the arbiter in
    // ACK mode, which HOLDS a grant until the ack. Without this assumption the
    // solver withdraws a request mid-grant and ap_src_requesting fails at
    // step 3 -- a real counterexample, but only to stimulus no conforming
    // producer can generate.
    //
    // It is stated as an assumption rather than by weakening P7 on purpose: if
    // a source ever DID drop valid mid-grant, m_valid would stand for a source
    // no longer asking, and that is worth continuing to assert against.
    // (formal_drain_ctrl_beats.sv constrains its handshakes the same way.)
    integer k;
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0) begin
            for (k = 0; k < NS; k = k + 1) begin
                if ($past(src_valid[k]) && !$past(src_ready[k]))
                    assume (src_valid[k]);
            end
        end
    end

    // The selected source's payload, restated independently of the DUT's mux.
    // Reverse element order for the flattened unpacked arrays; m_src_id itself
    // is a plain index.
    wire [7:0] f_sel_vector     = src_vector    [((NS-1)-m_src_id)*8 +: 8];
    wire [7:0] f_sel_dest       = src_dest      [((NS-1)-m_src_id)*8 +: 8];
    wire [2:0] f_sel_deliv_mode = src_deliv_mode[((NS-1)-m_src_id)*3 +: 3];
    // Packed port: NOT reordered.
    wire       f_sel_dest_mode  = src_dest_mode [m_src_id];
    wire       f_sel_valid      = src_valid     [m_src_id];

    always @(posedge clk) begin
        if (rst_n) begin
            ap_ready_onehot0:     assert ($onehot0(src_ready));                  // P1
            ap_retry_onehot0:     assert ($onehot0(src_retry));                  // P2
            ap_retry_only_ready:  assert ((src_retry & ~src_ready) == '0);       // P3
            if (src_retry != '0)
                ap_retry_real:    assert (m_retry);                              // P4
            if (src_ready != '0) begin
                ap_ready_needs_m: assert (m_valid && m_ready);                   // P5
            end
            if (m_valid) begin
                ap_route_vector:  assert (m_vector     == f_sel_vector);         // P6
                ap_route_dest:    assert (m_dest       == f_sel_dest);
                ap_route_mode:    assert (m_dest_mode  == f_sel_dest_mode);
                ap_route_deliv:   assert (m_deliv_mode == f_sel_deliv_mode);
                ap_src_requesting: assert (f_sel_valid);                         // P7
            end
        end
    end

    // Reachability. Without these the asserts can pass vacuously -- a merge
    // that never grants satisfies every property above.
    always @(posedge clk) begin
        if (rst_n) begin
            cp_merge_src0:    cover (m_valid && (m_src_id == 0) && m_ready);
            cp_merge_src1:    cover (m_valid && (m_src_id == 1) && m_ready);
            cp_retry_routed:  cover (src_retry != '0);
            cp_backpressure:  cover (m_valid && !m_ready);
            cp_both_request:  cover (src_valid == '1 && m_valid && m_ready);
        end
    end

endmodule
