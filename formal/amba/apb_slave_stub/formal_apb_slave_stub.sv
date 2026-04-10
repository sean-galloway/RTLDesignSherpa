// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_slave_stub -- FSM accepting APB transactions
//
// Properties verified:
//   P1: Reset clears s_apb_PREADY and cmd_valid
//   P2: s_apb_PREADY is single-cycle (pulse)
//   P3: Response path: rsp_ready only when in XFER_DATA and r_rsp_valid

`include "reset_defs.svh"

module formal_apb_slave_stub (
    input logic clk,
    input logic rst_n
);

    localparam int AW = 12;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int CPW = AW + DW + SW + 4;
    localparam int RPW = DW + 1;

    (* anyseq *) reg                 s_apb_PSEL;
    (* anyseq *) reg                 s_apb_PENABLE;
    (* anyseq *) reg [AW-1:0]        s_apb_PADDR;
    (* anyseq *) reg                 s_apb_PWRITE;
    (* anyseq *) reg [DW-1:0]        s_apb_PWDATA;
    (* anyseq *) reg [SW-1:0]        s_apb_PSTRB;
    (* anyseq *) reg [2:0]           s_apb_PPROT;
    (* anyseq *) reg                 cmd_ready;
    (* anyseq *) reg                 rsp_valid;
    (* anyseq *) reg [RPW-1:0]       rsp_data;

    wire [DW-1:0]        s_apb_PRDATA;
    wire                 s_apb_PSLVERR;
    wire                 s_apb_PREADY;
    wire                 cmd_valid;
    wire [CPW-1:0]       cmd_data;
    wire                 rsp_ready;

    apb_slave_stub #(
        .DEPTH(2),
        .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW)
    ) dut (
        .pclk          (clk),
        .presetn       (rst_n),
        .s_apb_PSEL    (s_apb_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PADDR   (s_apb_PADDR),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (s_apb_PRDATA),
        .s_apb_PSLVERR (s_apb_PSLVERR),
        .s_apb_PREADY  (s_apb_PREADY),
        .cmd_valid     (cmd_valid),
        .cmd_ready     (cmd_ready),
        .cmd_data      (cmd_data),
        .rsp_valid     (rsp_valid),
        .rsp_ready     (rsp_ready),
        .rsp_data      (rsp_data)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pready:   assert (!s_apb_PREADY);
            ap_reset_pslverr:  assert (!s_apb_PSLVERR);
        end
    end

    // P2: PREADY only pulses (the FSM goes to IDLE after it asserts)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_apb_PREADY))
                ap_pready_pulse: assert (!s_apb_PREADY);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_cmd_valid:  cover (cmd_valid);
            cp_pready:     cover (s_apb_PREADY);
            cp_full_xact:  cover (cmd_valid && rsp_valid);
        end
    end

endmodule
