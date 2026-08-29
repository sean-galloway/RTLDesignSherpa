// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Formal proof for apbx_xbar_2to2_mixed -- the mixed-version APB crossbar
// (m0=APB4, m1=APB5, s0=APB5, s1=APB4).
//
// WHY THIS EXISTS. Mixed-version gating was proven only through
// apbx_xbar_thin_mixed, and that harness was deleted with the thin core on
// 2026-08-27. That left the generated fabric's version gating covered by
// simulation alone -- one directed test, sampling. This restores a proof, for
// the variant that actually carries the behaviour.
//
// WHAT IS DIFFERENT FROM THE THIN PROOF, and it matters. The thin core took
// versions as PARAMETERS, so every port had every sideband pin and the gate was
// a mask; its properties A and B ("an APB4 slave is never DRIVEN with sideband",
// "an APB4 master never RECEIVES it") were the real content. Here the versions
// are STRUCTURAL: m0 and s1 have no sideband pins at all. Those two properties
// are therefore vacuous by construction and are deliberately not restated --
// asserting them would look like coverage while proving nothing. The port-list
// fact is checked where it belongs, structurally, by
// test_apbx_xbar_2to2_mixed.py's hasattr sweep.
//
// What remains genuinely provable is the part the structure does NOT give for
// free: that the fabric neither invents sideband on an APB4 master's behalf,
// nor fabricates completer sideband that no APB5 slave produced.

`include "reset_defs.svh"

module formal_apbx_xbar_2to2_mixed #(
    // 18 is the floor, not a preference: the slave index is offset[16] and the
    // range check spans BASE_ADDR + 2*64KB, so a narrower bus cannot express a
    // decode at all.
    parameter int AW = 18,
    parameter int DW = 32,
    parameter int SW = DW / 8
) (
    input logic clk,
    input logic rst_n,

    // m0 is APB4: no sideband pins exist to drive.
    input logic                  m0_apb_PSEL,
    input logic                  m0_apb_PENABLE,
    input logic [AW-1:0]         m0_apb_PADDR,
    input logic                  m0_apb_PWRITE,
    input logic [DW-1:0]         m0_apb_PWDATA,
    input logic [SW-1:0]         m0_apb_PSTRB,
    input logic [2:0]            m0_apb_PPROT,

    // m1 is APB5.
    input logic                  m1_apb_PSEL,
    input logic                  m1_apb_PENABLE,
    input logic [AW-1:0]         m1_apb_PADDR,
    input logic                  m1_apb_PWRITE,
    input logic [DW-1:0]         m1_apb_PWDATA,
    input logic [SW-1:0]         m1_apb_PSTRB,
    input logic [2:0]            m1_apb_PPROT,
    input logic                  m1_apb_PAUSER,
    input logic                  m1_apb_PWUSER,

    // s0 is APB5, s1 is APB4.
    input logic [DW-1:0]         s0_apb_PRDATA,  s1_apb_PRDATA,
    input logic                  s0_apb_PSLVERR, s1_apb_PSLVERR,
    input logic                  s0_apb_PREADY,  s1_apb_PREADY,
    input logic                  s0_apb_PWAKEUP,
    input logic                  s0_apb_PRUSER,
    input logic                  s0_apb_PBUSER
);

    logic [DW-1:0] m0_apb_PRDATA, m1_apb_PRDATA;
    logic          m0_apb_PSLVERR, m1_apb_PSLVERR;
    logic          m0_apb_PREADY,  m1_apb_PREADY;
    logic          m1_apb_PWAKEUP, m1_apb_PRUSER, m1_apb_PBUSER;

    logic          s0_apb_PSEL, s1_apb_PSEL;
    logic          s0_apb_PENABLE, s1_apb_PENABLE;
    logic [AW-1:0] s0_apb_PADDR, s1_apb_PADDR;
    logic          s0_apb_PWRITE, s1_apb_PWRITE;
    logic [DW-1:0] s0_apb_PWDATA, s1_apb_PWDATA;
    logic [SW-1:0] s0_apb_PSTRB, s1_apb_PSTRB;
    logic [2:0]    s0_apb_PPROT, s1_apb_PPROT;
    logic          s0_apb_PAUSER, s0_apb_PWUSER;

    apbx_xbar_2to2_mixed #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
        .BASE_ADDR({AW{1'b0}})
    ) dut (
        .pclk(clk), .presetn(rst_n),

        .m0_apb_PSEL(m0_apb_PSEL), .m0_apb_PENABLE(m0_apb_PENABLE),
        .m0_apb_PADDR(m0_apb_PADDR), .m0_apb_PWRITE(m0_apb_PWRITE),
        .m0_apb_PWDATA(m0_apb_PWDATA), .m0_apb_PSTRB(m0_apb_PSTRB),
        .m0_apb_PPROT(m0_apb_PPROT),
        .m0_apb_PRDATA(m0_apb_PRDATA), .m0_apb_PSLVERR(m0_apb_PSLVERR),
        .m0_apb_PREADY(m0_apb_PREADY),

        .m1_apb_PSEL(m1_apb_PSEL), .m1_apb_PENABLE(m1_apb_PENABLE),
        .m1_apb_PADDR(m1_apb_PADDR), .m1_apb_PWRITE(m1_apb_PWRITE),
        .m1_apb_PWDATA(m1_apb_PWDATA), .m1_apb_PSTRB(m1_apb_PSTRB),
        .m1_apb_PPROT(m1_apb_PPROT),
        .m1_apb_PRDATA(m1_apb_PRDATA), .m1_apb_PSLVERR(m1_apb_PSLVERR),
        .m1_apb_PREADY(m1_apb_PREADY),
        .m1_apb_PAUSER(m1_apb_PAUSER), .m1_apb_PWUSER(m1_apb_PWUSER),
        .m1_apb_PWAKEUP(m1_apb_PWAKEUP), .m1_apb_PRUSER(m1_apb_PRUSER),
        .m1_apb_PBUSER(m1_apb_PBUSER),

        .s0_apb_PSEL(s0_apb_PSEL), .s0_apb_PENABLE(s0_apb_PENABLE),
        .s0_apb_PADDR(s0_apb_PADDR), .s0_apb_PWRITE(s0_apb_PWRITE),
        .s0_apb_PWDATA(s0_apb_PWDATA), .s0_apb_PSTRB(s0_apb_PSTRB),
        .s0_apb_PPROT(s0_apb_PPROT),
        .s0_apb_PRDATA(s0_apb_PRDATA), .s0_apb_PSLVERR(s0_apb_PSLVERR),
        .s0_apb_PREADY(s0_apb_PREADY),
        .s0_apb_PAUSER(s0_apb_PAUSER), .s0_apb_PWUSER(s0_apb_PWUSER),
        .s0_apb_PWAKEUP(s0_apb_PWAKEUP), .s0_apb_PRUSER(s0_apb_PRUSER),
        .s0_apb_PBUSER(s0_apb_PBUSER),

        .s1_apb_PSEL(s1_apb_PSEL), .s1_apb_PENABLE(s1_apb_PENABLE),
        .s1_apb_PADDR(s1_apb_PADDR), .s1_apb_PWRITE(s1_apb_PWRITE),
        .s1_apb_PWDATA(s1_apb_PWDATA), .s1_apb_PSTRB(s1_apb_PSTRB),
        .s1_apb_PPROT(s1_apb_PPROT),
        .s1_apb_PRDATA(s1_apb_PRDATA), .s1_apb_PSLVERR(s1_apb_PSLVERR),
        .s1_apb_PREADY(s1_apb_PREADY)
    );

    integer f_past_valid = 0;
    always @(posedge clk) if (f_past_valid < 3) f_past_valid <= f_past_valid + 1;

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Masters obey APB: PENABLE never without PSEL, and nothing in flight
    // across reset.
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!m0_apb_PENABLE || m0_apb_PSEL);
            assume (!m1_apb_PENABLE || m1_apb_PSEL);
        end
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            assume (!m0_apb_PSEL);
            assume (!m1_apb_PSEL);
        end
    end

    // -------------------------------------------------------------------------
    // Property 1: Reset clears master-side outputs
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_rst_m0_pready:  assert (!m0_apb_PREADY);
            ap_rst_m0_pslverr: assert (!m0_apb_PSLVERR);
            ap_rst_m1_pready:  assert (!m1_apb_PREADY);
            ap_rst_m1_pslverr: assert (!m1_apb_PSLVERR);
        end
    end

    // -------------------------------------------------------------------------
    // Property 2: Reset clears slave-side outputs
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_rst_s0_psel: assert (!s0_apb_PSEL);
            ap_rst_s1_psel: assert (!s1_apb_PSEL);
            ap_rst_s0_pen:  assert (!s0_apb_PENABLE);
            ap_rst_s1_pen:  assert (!s1_apb_PENABLE);
        end
    end

    // -------------------------------------------------------------------------
    // Property 3: APB protocol on the slave side -- PENABLE requires PSEL
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_s0_pen_psel: assert (!s0_apb_PENABLE || s0_apb_PSEL);
            ap_s1_pen_psel: assert (!s1_apb_PENABLE || s1_apb_PSEL);
        end
    end

    // -------------------------------------------------------------------------
    // Property 4: Arbiter grant one-hot per slave
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_s0_grant_onehot: assert ($countones(dut.s0_arb_grant) <= 1);
            ap_s1_grant_onehot: assert ($countones(dut.s1_arb_grant) <= 1);
        end
    end

    // -------------------------------------------------------------------------
    // Property 5 (GATE, no injection): the APB4 master cannot cause sideband to
    // appear at the APB5 slave.
    //
    // m0 has no sideband pins, so the fabric has nothing legitimate to forward
    // and must not invent anything. This is the half of the gate the structure
    // does NOT give for free: s0_apb_PAUSER is a real wire fed by a mux, and
    // that mux has an m0 leg.
    //
    // A FIRST DRAFT ASSERTED THIS AGAINST THE INSTANTANEOUS GRANT --
    // "while s0_arb_grant[0], s0_apb_PAUSER == '0" -- and z3 refuted it in
    // seven steps. The trace was right and the property was wrong: m1 asserts
    // PSEL with PAUSER=1, then DROPS PSEL while its command is still in flight
    // through the cmd skid buffer, and the grant rotates to m0 while the
    // downstream apb5_master is still legitimately driving m1's sideband for
    // that earlier transaction. The instantaneous grant says nothing about
    // whose command the boundary IP is currently executing.
    //
    // Stated at the boundary with a sticky flag instead: if the APB5 master has
    // never selected, no sideband can ever have entered the fabric, so anything
    // at the APB5 slave would be fabricated on the APB4 master's behalf. That
    // holds without depending on any internal name or on grant timing.
    // (The thin core's harness reached the same formulation for the same
    // reason before it was deleted.)
    // -------------------------------------------------------------------------
    logic m1_ever_selected;
    always @(posedge clk) begin
        if (!rst_n) m1_ever_selected <= 1'b0;
        else if (m1_apb_PSEL) m1_ever_selected <= 1'b1;
    end

    always @(posedge clk) begin
        if (rst_n && !m1_ever_selected && !m1_apb_PSEL) begin
            ap_gate_no_inject_pauser: assert (s0_apb_PAUSER == 1'b0);
            ap_gate_no_inject_pwuser: assert (s0_apb_PWUSER == 1'b0);
        end
    end

    // -------------------------------------------------------------------------
    // Property 6 (GATE, no fabrication): completer sideband reaching the APB5
    // master can only have come from the APB5 slave.
    //
    // Stated at the boundary with a sticky flag rather than by reaching for the
    // response mux: if s0 has never driven PRUSER/PBUSER high, then nothing the
    // APB5 master sees on those pins can be real -- so anything nonzero would be
    // fabricated, and in particular would be the APB4 slave s1's response
    // leaking into pins s1 does not have.
    // -------------------------------------------------------------------------
    logic s0_ever_pruser, s0_ever_pbuser;
    always @(posedge clk) begin
        if (!rst_n) begin
            s0_ever_pruser <= 1'b0;
            s0_ever_pbuser <= 1'b0;
        end else begin
            if (s0_apb_PRUSER) s0_ever_pruser <= 1'b1;
            if (s0_apb_PBUSER) s0_ever_pbuser <= 1'b1;
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            if (!s0_ever_pruser && !s0_apb_PRUSER)
                ap_gate_no_fab_pruser: assert (m1_apb_PRUSER == 1'b0);
            if (!s0_ever_pbuser && !s0_apb_PBUSER)
                ap_gate_no_fab_pbuser: assert (m1_apb_PBUSER == 1'b0);
        end
    end

    // -------------------------------------------------------------------------
    // Property 7: PWAKEUP is dropped, unconditionally.
    //
    // This proves a documented LIMITATION rather than a guarantee. The mixed
    // variant's boundary IP leaves rsp_pwakeup unconnected and ties
    // wakeup_request to '0, so an APB5 slave asserting PWAKEUP is never seen at
    // the APB5 master. The books say so; this makes it checkable, and makes the
    // day someone wires it up a failing proof rather than a silent change.
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_pwakeup_dropped: assert (m1_apb_PWAKEUP == 1'b0);
        end
    end

    // -------------------------------------------------------------------------
    // Cover: these are what stop the gate properties above from passing
    // vacuously. If sideband never propagated at all, "it is '0 when granted to
    // m0" would be true and worthless.
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            cp_m0_pready:      cover (m0_apb_PREADY);
            cp_m1_pready:      cover (m1_apb_PREADY);
            cp_s0_psel:        cover (s0_apb_PSEL);
            cp_s1_psel:        cover (s1_apb_PSEL);
            // The APB5->APB5 path really carries request sideband...
            cp_sideband_fwd:   cover (s0_apb_PSEL && s0_apb_PAUSER);
            // ...and really returns completer sideband.
            cp_sideband_rtn:   cover (m1_apb_PRUSER);
            // The APB4 master really does reach the APB5 slave (property 5 is
            // about a state that occurs).
            cp_m0_to_s0:       cover (dut.s0_arb_grant[0]);
            // The APB5 master really does reach the APB4 slave.
            cp_m1_to_s1:       cover (dut.s1_arb_grant[1]);
        end
    end

endmodule
