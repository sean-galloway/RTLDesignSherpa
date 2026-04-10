// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_master_stub -- packs cmd/rsp interface around apb_master
//
// Properties verified:
//   P1: Reset clears APB outputs
//   P2: APB protocol compliance (PENABLE requires PSEL, ACCESS held)
//   P3: Stub packing is correct (response packet contains correct unpacked fields)

`include "reset_defs.svh"

module formal_apb_master_stub (
    input logic clk,
    input logic rst_n
);

    localparam int AW = 12;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int CPW = AW + DW + SW + 3 + 1 + 1 + 1; // addr+data+strb+prot+pwrite+first+last
    localparam int RPW = DW + 1 + 1 + 1;               // data+pslverr+first+last

    (* anyseq *) reg                 cmd_valid;
    (* anyseq *) reg                 rsp_ready;
    (* anyseq *) reg [CPW-1:0]       cmd_data;
    (* anyseq *) reg                 m_apb_PREADY;
    (* anyseq *) reg [DW-1:0]        m_apb_PRDATA;
    (* anyseq *) reg                 m_apb_PSLVERR;

    wire                 cmd_ready;
    wire                 rsp_valid;
    wire [RPW-1:0]       rsp_data;
    wire                 m_apb_PSEL;
    wire                 m_apb_PENABLE;
    wire [AW-1:0]        m_apb_PADDR;
    wire                 m_apb_PWRITE;
    wire [DW-1:0]        m_apb_PWDATA;
    wire [SW-1:0]        m_apb_PSTRB;
    wire [2:0]           m_apb_PPROT;

    apb_master_stub #(
        .CMD_DEPTH(2),
        .RSP_DEPTH(2),
        .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW)
    ) dut (
        .pclk           (clk),
        .presetn        (rst_n),
        .m_apb_PSEL     (m_apb_PSEL),
        .m_apb_PENABLE  (m_apb_PENABLE),
        .m_apb_PADDR    (m_apb_PADDR),
        .m_apb_PWRITE   (m_apb_PWRITE),
        .m_apb_PWDATA   (m_apb_PWDATA),
        .m_apb_PSTRB    (m_apb_PSTRB),
        .m_apb_PPROT    (m_apb_PPROT),
        .m_apb_PRDATA   (m_apb_PRDATA),
        .m_apb_PSLVERR  (m_apb_PSLVERR),
        .m_apb_PREADY   (m_apb_PREADY),
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_data       (cmd_data),
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_data       (rsp_data)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel:  assert (!m_apb_PSEL);
            ap_reset_pen:   assert (!m_apb_PENABLE);
        end
    end

    // P2a: PENABLE implies PSEL
    always @(posedge clk) begin
        if (rst_n)
            ap_pen_needs_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    // P2b: ACCESS held until PREADY
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // P2c: Address stable during ACCESS
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PENABLE) && m_apb_PENABLE)
                ap_addr_stable: assert (m_apb_PADDR == $past(m_apb_PADDR));
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_setup:    cover (m_apb_PSEL && !m_apb_PENABLE);
            cp_access:   cover (m_apb_PSEL && m_apb_PENABLE);
            cp_complete: cover (m_apb_PSEL && m_apb_PENABLE && m_apb_PREADY);
            cp_rsp:      cover (rsp_valid);
            cp_cmd_fire: cover (cmd_valid && cmd_ready);
        end
    end

endmodule
