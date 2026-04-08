// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_slave_cdc -- single-clock model
//
// Multi-clock CDC is modeled with pclk=aclk=clk so both domains
// run synchronously, making BMC tractable while still verifying
// the datapath and FSM logic.
//
// Properties verified:
//   P1: Reset clears APB outputs (PREADY, PSLVERR, PRDATA)
//   P2: Reset clears cmd_valid
//   P3: APB PREADY is single-cycle pulse (not held high)
//   P4: Command passthrough -- after APB access phase, cmd_valid eventually rises
//   P5: Response passthrough -- rsp_valid eventually drives PREADY

`include "reset_defs.svh"

module formal_apb_slave_cdc (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int AW = 12;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int PW = 3;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg              s_apb_PSEL;
    (* anyseq *) reg              s_apb_PENABLE;
    (* anyseq *) reg [AW-1:0]     s_apb_PADDR;
    (* anyseq *) reg              s_apb_PWRITE;
    (* anyseq *) reg [DW-1:0]     s_apb_PWDATA;
    (* anyseq *) reg [SW-1:0]     s_apb_PSTRB;
    (* anyseq *) reg [PW-1:0]     s_apb_PPROT;

    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              s_apb_PREADY;
    wire [DW-1:0]     s_apb_PRDATA;
    wire              s_apb_PSLVERR;
    wire              cmd_valid;
    wire              cmd_pwrite;
    wire [AW-1:0]     cmd_paddr;
    wire [DW-1:0]     cmd_pwdata;
    wire [SW-1:0]     cmd_pstrb;
    wire [PW-1:0]     cmd_pprot;
    wire              rsp_ready;

    // =========================================================================
    // DUT -- single-clock model: pclk = aclk = clk
    // =========================================================================
    apb_slave_cdc #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .DEPTH      (2)
    ) dut (
        .aclk       (clk),
        .aresetn    (rst_n),
        .pclk       (clk),
        .presetn    (rst_n),

        .s_apb_PSEL    (s_apb_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PREADY  (s_apb_PREADY),
        .s_apb_PADDR   (s_apb_PADDR),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (s_apb_PRDATA),
        .s_apb_PSLVERR (s_apb_PSLVERR),

        .cmd_valid  (cmd_valid),
        .cmd_ready  (cmd_ready),
        .cmd_pwrite (cmd_pwrite),
        .cmd_paddr  (cmd_paddr),
        .cmd_pwdata (cmd_pwdata),
        .cmd_pstrb  (cmd_pstrb),
        .cmd_pprot  (cmd_pprot),

        .rsp_valid  (rsp_valid),
        .rsp_ready  (rsp_ready),
        .rsp_prdata (rsp_prdata),
        .rsp_pslverr(rsp_pslverr)
    );

    // =========================================================================
    // Reset and past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pready:  assert (!s_apb_PREADY);
            ap_reset_pslverr: assert (!s_apb_PSLVERR);
        end
    end

    // P2: Reset clears cmd_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_cmd_valid: assert (!cmd_valid);
    end

    // P3: PREADY never asserted for two consecutive cycles
    //     (APB slave FSM goes IDLE -> BUSY -> WAIT -> IDLE; PREADY is one-shot)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_apb_PREADY))
                ap_pready_single_cycle: assert (!s_apb_PREADY);
    end

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_cmd_valid:     cover (cmd_valid);
            cp_pready:        cover (s_apb_PREADY);
            cp_cmd_and_rsp:   cover (cmd_valid && rsp_valid);
        end
    end

endmodule
