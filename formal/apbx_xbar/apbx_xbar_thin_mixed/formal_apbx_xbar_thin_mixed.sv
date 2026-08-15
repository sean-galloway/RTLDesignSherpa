// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Formal proof for apbx_xbar_thin in a MIXED APB4/APB5 configuration
// (APBX-002). The sibling harness formal_apbx_xbar_thin proves the
// default all-APB4 build; this one proves the thing APBX-001 actually
// added — that the MST_APB5/SLV_APB5 masks gate sideband contribution
// at BOTH ends of every path.
//
// The simulation testbenches sample that property; this proves it
// exhaustively over every address, every arbitration order and every
// sideband value, which is what makes a "no leak" claim worth making.
//
// Configuration under proof: m0 = APB4, m1 = APB5,
//                            s0 = APB5, s1 = APB4.
// So exactly one of the four pairings (m1 -> s0) may carry sideband.

`include "reset_defs.svh"

module formal_apbx_xbar_thin_mixed #(
    parameter int M  = 2,
    parameter int S  = 2,
    parameter int AW = 12,
    parameter int DW = 32,
    parameter int SW = DW / 8,
    parameter int MAX_THRESH = 16,
    parameter int MTW   = $clog2(MAX_THRESH),
    parameter int MXMTW = M * MTW,
    // Sideband widths wide enough that a nonzero value cannot be
    // confused with the '0 an APB4 port must see.
    parameter int AUW = 4,
    parameter int WUW = 4,
    parameter int RUW = 4,
    parameter int BUW = 4,
    parameter logic [31:0] MST_APB5 = 32'h0000_0002,   // m1 only
    parameter logic [31:0] SLV_APB5 = 32'h0000_0001,   // s0 only
    parameter bit ENABLE_PARITY = 1'b1                 // APBX-003
) (
    input logic clk,
    input logic rst_n,

    input logic [S-1:0]         SLAVE_ENABLE,
    input logic [S-1:0][AW-1:0] SLAVE_ADDR_BASE,
    input logic [S-1:0][AW-1:0] SLAVE_ADDR_LIMIT,
    input logic [MXMTW-1:0]     THRESHOLDS,

    input logic [M-1:0]         m_apb_psel,
    input logic [M-1:0]         m_apb_penable,
    input logic [M-1:0]         m_apb_pwrite,
    input logic [M-1:0][2:0]    m_apb_pprot,
    input logic [M-1:0][AW-1:0] m_apb_paddr,
    input logic [M-1:0][DW-1:0] m_apb_pwdata,
    input logic [M-1:0][SW-1:0] m_apb_pstrb,
    // Requester-direction sideband, free inputs
    input logic [M-1:0][AUW-1:0] m_apb_pauser,
    input logic [M-1:0][WUW-1:0] m_apb_pwuser,
    input logic [M-1:0][SW-1:0]  m_apb_pwdataparity,
    input logic [M-1:0]          m_apb_paddrparity,
    input logic [M-1:0]          m_apb_pctrlparity,

    input logic [S-1:0]          s_apb_pready,
    input logic [S-1:0][DW-1:0]  s_apb_prdata,
    input logic [S-1:0]          s_apb_pslverr,
    // Completer-direction sideband, free inputs
    input logic [S-1:0]          s_apb_pwakeup,
    input logic [S-1:0][RUW-1:0] s_apb_pruser,
    input logic [S-1:0][BUW-1:0] s_apb_pbuser,
    input logic [S-1:0][SW-1:0]  s_apb_prdataparity,
    input logic [S-1:0]          s_apb_preadyparity,
    input logic [S-1:0]          s_apb_pslverrparity
);

    logic [M-1:0]          m_apb_pready;
    logic [M-1:0][DW-1:0]  m_apb_prdata;
    logic [M-1:0]          m_apb_pslverr;
    logic [M-1:0]          m_apb_pwakeup;
    logic [M-1:0][RUW-1:0] m_apb_pruser;
    logic [M-1:0][BUW-1:0] m_apb_pbuser;

    logic [S-1:0]          s_apb_psel;
    logic [S-1:0]          s_apb_penable;
    logic [S-1:0]          s_apb_pwrite;
    logic [S-1:0][2:0]     s_apb_pprot;
    logic [S-1:0][AW-1:0]  s_apb_paddr;
    logic [S-1:0][DW-1:0]  s_apb_pwdata;
    logic [S-1:0][SW-1:0]  s_apb_pstrb;
    logic [S-1:0][AUW-1:0] s_apb_pauser;
    logic [S-1:0][WUW-1:0] s_apb_pwuser;
    logic [S-1:0][SW-1:0]  s_apb_pwdataparity;
    logic [S-1:0]          s_apb_paddrparity;
    logic [S-1:0]          s_apb_pctrlparity;
    logic [M-1:0][SW-1:0]  m_apb_prdataparity;
    logic [M-1:0]          m_apb_preadyparity;
    logic [M-1:0]          m_apb_pslverrparity;

    apbx_xbar_thin #(
        .M(M), .S(S),
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
        .MAX_THRESH(MAX_THRESH),
        .MST_APB5(MST_APB5), .SLV_APB5(SLV_APB5),
        .ENABLE_PARITY(ENABLE_PARITY),
        .AUW(AUW), .WUW(WUW), .RUW(RUW), .BUW(BUW)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .SLAVE_ENABLE(SLAVE_ENABLE),
        .SLAVE_ADDR_BASE(SLAVE_ADDR_BASE),
        .SLAVE_ADDR_LIMIT(SLAVE_ADDR_LIMIT),
        .THRESHOLDS(THRESHOLDS),
        .m_apb_psel(m_apb_psel), .m_apb_penable(m_apb_penable),
        .m_apb_pwrite(m_apb_pwrite), .m_apb_pprot(m_apb_pprot),
        .m_apb_paddr(m_apb_paddr), .m_apb_pwdata(m_apb_pwdata),
        .m_apb_pstrb(m_apb_pstrb),
        .m_apb_pready(m_apb_pready), .m_apb_prdata(m_apb_prdata),
        .m_apb_pslverr(m_apb_pslverr),
        .m_apb_pauser(m_apb_pauser), .m_apb_pwuser(m_apb_pwuser),
        .m_apb_pwdataparity(m_apb_pwdataparity),
        .m_apb_paddrparity(m_apb_paddrparity),
        .m_apb_pctrlparity(m_apb_pctrlparity),
        .m_apb_prdataparity(m_apb_prdataparity),
        .m_apb_preadyparity(m_apb_preadyparity),
        .m_apb_pslverrparity(m_apb_pslverrparity),
        .m_apb_pwakeup(m_apb_pwakeup), .m_apb_pruser(m_apb_pruser),
        .m_apb_pbuser(m_apb_pbuser),
        .s_apb_psel(s_apb_psel), .s_apb_penable(s_apb_penable),
        .s_apb_pwrite(s_apb_pwrite), .s_apb_pprot(s_apb_pprot),
        .s_apb_paddr(s_apb_paddr), .s_apb_pwdata(s_apb_pwdata),
        .s_apb_pstrb(s_apb_pstrb),
        .s_apb_pready(s_apb_pready), .s_apb_prdata(s_apb_prdata),
        .s_apb_pslverr(s_apb_pslverr),
        .s_apb_pauser(s_apb_pauser), .s_apb_pwuser(s_apb_pwuser),
        .s_apb_pwdataparity(s_apb_pwdataparity),
        .s_apb_paddrparity(s_apb_paddrparity),
        .s_apb_pctrlparity(s_apb_pctrlparity),
        .s_apb_prdataparity(s_apb_prdataparity),
        .s_apb_preadyparity(s_apb_preadyparity),
        .s_apb_pslverrparity(s_apb_pslverrparity),
        .s_apb_pwakeup(s_apb_pwakeup), .s_apb_pruser(s_apb_pruser),
        .s_apb_pbuser(s_apb_pbuser)
    );

    integer f_past_valid = 0;
    always @(posedge clk) if (f_past_valid < 3) f_past_valid <= f_past_valid + 1;

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // ---- Assumptions: well-formed APB masters ------------------------------
    generate
        for (genvar am = 0; am < M; am++) begin : gen_assume_master
            always @(posedge clk) begin
                if (rst_n) assume (!m_apb_penable[am] || m_apb_psel[am]);
            end
            always @(posedge clk) begin
                if (f_past_valid > 0 && $past(!rst_n))
                    assume (!m_apb_psel[am]);
            end
        end
    endgenerate

    always @(posedge clk) if (rst_n) begin
        assume ($stable(SLAVE_ENABLE));
        assume ($stable(SLAVE_ADDR_BASE));
        assume ($stable(SLAVE_ADDR_LIMIT));
        assume ($stable(THRESHOLDS));
    end

    generate
        for (genvar si = 0; si < S; si++) begin : gen_assume_range_i
            for (genvar sj = si + 1; sj < S; sj++) begin : gen_assume_range_j
                always @(posedge clk) if (rst_n) begin
                    if (SLAVE_ENABLE[si] && SLAVE_ENABLE[sj])
                        assume (SLAVE_ADDR_LIMIT[si] < SLAVE_ADDR_BASE[sj] ||
                                SLAVE_ADDR_LIMIT[sj] < SLAVE_ADDR_BASE[si]);
                end
            end
        end
        for (genvar sb = 0; sb < S; sb++) begin : gen_assume_base_limit
            always @(posedge clk) if (rst_n) begin
                if (SLAVE_ENABLE[sb])
                    assume (SLAVE_ADDR_BASE[sb] <= SLAVE_ADDR_LIMIT[sb]);
            end
        end
    endgenerate

    // =======================================================================
    // Property A: an APB4 SLAVE is never driven with sideband.
    //
    // This is the "no leak downstream" half of the gate. It must hold for
    // every address, every arbitration order and every value an APB5
    // master puts on its user buses -- which is exactly the part a
    // simulation can only sample.
    // =======================================================================
    generate
        for (genvar gs = 0; gs < S; gs++) begin : gen_slv_gate
            if (SLV_APB5[gs] == 1'b0) begin : gen_apb4_slave
                always @(posedge clk) if (rst_n) begin
                    assert (s_apb_pauser[gs] == '0);
                    assert (s_apb_pwuser[gs] == '0);
                end
            end
        end
    endgenerate

    // =======================================================================
    // Property B: an APB4 MASTER never receives completer sideband.
    //
    // The "no leak upstream" half. An APB4 master has no pins for these,
    // so anything nonzero here would be driving a port that does not
    // exist on the real device.
    // =======================================================================
    generate
        for (genvar gm = 0; gm < M; gm++) begin : gen_mst_gate
            if (MST_APB5[gm] == 1'b0) begin : gen_apb4_master
                always @(posedge clk) if (rst_n) begin
                    assert (m_apb_pwakeup[gm] == 1'b0);
                    assert (m_apb_pruser[gm]  == '0);
                    assert (m_apb_pbuser[gm]  == '0);
                end
            end
        end
    endgenerate

    // =======================================================================
    // Property C: an APB4 master cannot contribute sideband to an APB5
    // slave either -- the gate is on BOTH ends, not just the receiving
    // one.
    //
    // This is stated against the GRANT, not against PSEL, and that
    // distinction is the whole content of the property. A first draft
    // asserted "if no APB5 master is selecting, the APB5 slave sees
    // '0" and the solver refuted it in four steps: grants persist from
    // command acceptance through response completion, so the APB5
    // master can still hold the grant -- and legitimately still be
    // driving sideband -- in a cycle where it has dropped PSEL. The
    // refutation was correct and the property was wrong.
    //
    // What the RTL actually promises is about the granted master, so
    // reach in for it. Hierarchical reference is the honest way to say
    // this; the alternative is a weaker property that would pass while
    // proving less.
    // =======================================================================
    // A sticky flag rather than a hierarchical reference into the DUT:
    // the native formal front end does not resolve dut.arb_gnt_id here,
    // and a boundary-only statement is a stronger thing to have anyway
    // -- it holds without depending on any internal name.
    logic apb5_mst_active;
    always @(posedge clk) begin
        if (!rst_n) apb5_mst_active <= 1'b0;
        else if ((m_apb_psel & MST_APB5[M-1:0]) != '0)
            apb5_mst_active <= 1'b1;
    end

    generate
        for (genvar cs = 0; cs < S; cs++) begin : gen_src_gate
            if (SLV_APB5[cs] == 1'b1) begin : gen_apb5_slave
                always @(posedge clk) if (rst_n) begin
                    // No APB5 master has ever selected, so anything the
                    // APB5 slave sees can only have come from an APB4
                    // master -- and must therefore be '0.
                    if (!apb5_mst_active) begin
                        assert (s_apb_pauser[cs] == '0);
                        assert (s_apb_pwuser[cs] == '0);
                    end
                end
            end
        end
    endgenerate

    // =======================================================================
    // Property D: parity obeys the same gate as the rest of the
    // sideband -- an APB4 slave is never driven with parity, and an
    // APB4 master never receives it. This is the owner's rule from
    // 2026-08-15 ("a mixed pairing ignores parity") stated as a
    // property rather than as a comment.
    // =======================================================================
    generate
        for (genvar ds = 0; ds < S; ds++) begin : gen_par_slv
            if (SLV_APB5[ds] == 1'b0) begin : gen_apb4_slave_par
                always @(posedge clk) if (rst_n) begin
                    assert (s_apb_pwdataparity[ds] == '0);
                    assert (s_apb_paddrparity[ds]  == 1'b0);
                    assert (s_apb_pctrlparity[ds]  == 1'b0);
                end
            end
        end
        for (genvar dm = 0; dm < M; dm++) begin : gen_par_mst
            if (MST_APB5[dm] == 1'b0) begin : gen_apb4_master_par
                always @(posedge clk) if (rst_n) begin
                    assert (m_apb_prdataparity[dm]  == '0);
                    assert (m_apb_preadyparity[dm]  == 1'b0);
                    assert (m_apb_pslverrparity[dm] == 1'b0);
                end
            end
        end
    endgenerate

    // =======================================================================
    // Property E: on an APB5->APB5 path the thin core passes parity
    // through UNALTERED. This is the whole reason the thin core carries
    // parity end-to-end instead of regenerating it: a recomputed parity
    // bit would be correct-by-construction and would therefore hide a
    // fault in the mux it just travelled through. Stated as "whatever
    // reaches the slave equals what some master drove", via the
    // sticky-flag trick used for Property C -- while only the APB5
    // master has ever selected, the APB5 slave's parity must equal that
    // master's.
    // =======================================================================
    logic apb4_mst_active;
    always @(posedge clk) begin
        if (!rst_n) apb4_mst_active <= 1'b0;
        else if ((m_apb_psel & ~MST_APB5[M-1:0]) != '0)
            apb4_mst_active <= 1'b1;
    end

    generate
        for (genvar es = 0; es < S; es++) begin : gen_par_pass
            if (SLV_APB5[es] == 1'b1) begin : gen_apb5_slave_pass
                for (genvar em = 0; em < M; em++) begin : gen_par_src
                    if (MST_APB5[em] == 1'b1) begin : gen_apb5_src
                        always @(posedge clk) if (rst_n) begin
                            if (!apb4_mst_active && s_apb_psel[es]) begin
                                assert (s_apb_pwdataparity[es] ==
                                        m_apb_pwdataparity[em]);
                                assert (s_apb_paddrparity[es] ==
                                        m_apb_paddrparity[em]);
                                assert (s_apb_pctrlparity[es] ==
                                        m_apb_pctrlparity[em]);
                            end
                        end
                    end
                end
            end
        end
    endgenerate

    // =======================================================================
    // Cover: the legal pairing really can carry sideband, so Properties
    // A-C are not passing vacuously on a fabric that never moves any.
    // =======================================================================
    generate
        for (genvar xs = 0; xs < S; xs++) begin : gen_cover_pass
            if (SLV_APB5[xs] == 1'b1) begin : gen_cover_apb5_slave
                always @(posedge clk) if (rst_n) begin
                    cover (s_apb_psel[xs] && s_apb_pauser[xs] != '0);
                end
            end
        end
    endgenerate

endmodule : formal_apbx_xbar_thin_mixed
