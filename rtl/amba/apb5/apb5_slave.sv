// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave
// Purpose: APB5 Slave with AMBA5 extensions
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes (from master)
// - PWUSER: User-defined write data attributes (from master)
// - PRUSER: User-defined read data attributes (to master)
// - PBUSER: User-defined response attributes (to master)
// - PWAKEUP: Requester wake-up INPUT (IHI 0024E 3.7.2, Table 3-7)
// - Optional interface parity protection (IHI 0024E ch. 5: *CHK signals,
//   odd parity, one check bit per 8 payload bits)
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_slave #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int PROT_WIDTH      = 3,
    parameter int AUSER_WIDTH     = 4,
    parameter int WUSER_WIDTH     = 4,
    parameter int RUSER_WIDTH     = 4,
    parameter int BUSER_WIDTH     = 4,
    parameter int DEPTH           = 2,
    parameter bit ENABLE_PARITY   = 0,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    // Computed widths
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,  // Command packet width
    parameter int RPW = DW + RUW + BUW + 1,                  // Response packet width (data + user + error)
    // Parity check-signal widths (IHI 0024E Table 5-1): one bit per 8 bits
    parameter int ACW  = (AW + 7) / 8,                       // PADDRCHK
    parameter int DCW  = DW / 8,                             // PWDATACHK / PRDATACHK
    parameter int AUCW = (AUW + 7) / 8,                      // PAUSERCHK
    parameter int WUCW = (WUW + 7) / 8,                      // PWUSERCHK
    parameter int RUCW = (RUW + 7) / 8,                      // PRUSERCHK
    parameter int BUCW = (BUW + 7) / 8                       // PBUSERCHK
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // APB5 interface (slave side)
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    input  logic [AUW-1:0]    s_apb_PAUSER,
    input  logic [WUW-1:0]    s_apb_PWUSER,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,
    input  logic              s_apb_PWAKEUP,        // Requester-driven (Table 3-7)
    output logic [RUW-1:0]    s_apb_PRUSER,
    output logic [BUW-1:0]    s_apb_PBUSER,

    // Interface parity check signals, IHI 0024E ch. 5 (ENABLE_PARITY=1).
    // Odd parity; outputs tied LOW and inputs unchecked when ENABLE_PARITY=0.
    input  logic [ACW-1:0]    s_apb_PADDRCHK,
    input  logic              s_apb_PCTRLCHK,       // PPROT, PWRITE
    input  logic              s_apb_PSELCHK,        // PSELxCHK
    input  logic              s_apb_PENABLECHK,
    input  logic [DCW-1:0]    s_apb_PWDATACHK,
    input  logic              s_apb_PSTRBCHK,
    input  logic [AUCW-1:0]   s_apb_PAUSERCHK,
    input  logic [WUCW-1:0]   s_apb_PWUSERCHK,
    output logic [DCW-1:0]    s_apb_PRDATACHK,
    output logic              s_apb_PREADYCHK,
    output logic              s_apb_PSLVERRCHK,
    input  logic              s_apb_PWAKEUPCHK,
    output logic [RUCW-1:0]   s_apb_PRUSERCHK,
    output logic [BUCW-1:0]   s_apb_PBUSERCHK,

    // Command Interface
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,
    output logic [AUW-1:0]    cmd_pauser,
    output logic [WUW-1:0]    cmd_pwuser,

    // Response Interface
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
    input  logic [RUW-1:0]    rsp_pruser,
    input  logic [BUW-1:0]    rsp_pbuser,


    // Parity error flags (active when ENABLE_PARITY=1; combinational,
    // asserted while a check's Table 5-1 Check Enable term holds)
    //   parity_error_wdata: PWDATACHK, PSTRBCHK, PWUSERCHK
    //   parity_error_ctrl : PADDRCHK, PCTRLCHK, PSELCHK, PENABLECHK, PAUSERCHK,
    //                       PWAKEUPCHK
    output logic              parity_error_wdata,
    output logic              parity_error_ctrl
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          r_cmd_count;

    assign r_cmd_data_in = {s_apb_PWRITE, s_apb_PPROT, s_apb_PSTRB, s_apb_PADDR, s_apb_PWDATA,
                            s_apb_PAUSER, s_apb_PWUSER};
    assign {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
            cmd_pauser, cmd_pwuser} = r_cmd_data_out;

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (r_cmd_valid),
        .wr_ready     (r_cmd_ready),
        .wr_data      (r_cmd_data_in),
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        .rd_data      (r_cmd_data_out),
        .count        (r_cmd_count),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;
    logic [RPW-1:0]      r_rsp_data_out;
    logic [DW-1:0]       r_rsp_prdata;
    logic                r_rsp_pslverr;
    logic [RUW-1:0]      r_rsp_pruser;
    logic [BUW-1:0]      r_rsp_pbuser;
    logic [3:0]          r_rsp_count;

    assign {r_rsp_pslverr, r_rsp_prdata, r_rsp_pruser, r_rsp_pbuser} = r_rsp_data_out;
    assign r_rsp_data_in = {rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser};

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (r_rsp_data_in),
        .rd_valid     (r_rsp_valid),
        .rd_ready     (r_rsp_ready),
        .rd_data      (r_rsp_data_out),
        .count        (r_rsp_count),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // APB5 FSM
    typedef enum logic [2:0] {
        IDLE = 3'b001,
        BUSY = 3'b010,
        WAIT = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state;
    logic r_penable_prev;

    // PWAKEUP is a Requester output (IHI 0024E 3.7.2). This Completer does
    // not wait for it before PREADY; it is consumed by the parity check here
    // and as a clock-gate wake term in the _cg wrappers.

    // ------------------------------------------------------------------
    // Interface parity protection, AMBA APB IHI 0024E chapter 5.
    //   - ODD parity (5.3): payload plus check bit hold an odd number of 1s,
    //     so dataint_parity runs with parity_type = 0.
    //   - Multi-bit check signals carry one bit per 8 payload bits; bit [n]
    //     covers payload[8n+7:8n] and a short top byte is checked over the
    //     bits that exist. dataint_parity splits WIDTH/CHUNKS with the
    //     remainder in the LAST chunk, which is not that layout, so it is
    //     instantiated once per spec byte (CHUNKS = 1).
    //   - Single-bit critical controls (PSEL, PENABLE, PREADY, PSLVERR,
    //     PWAKEUP) check as the inversion of the signal (WIDTH = 1).
    //   - PCTRLCHK covers PPROT and PWRITE (PNSE is not carried, so LOW);
    //     PSTRBCHK is one bit over all of PSTRB (Table 5-1).
    //   - Error flags are combinational and only assert while the check's
    //     Check Enable term from Table 5-1 is true.
    // ------------------------------------------------------------------
    generate
        if (ENABLE_PARITY) begin : gen_parity
            // Requester-driven checks
            logic [ACW-1:0] w_paddrchk_err;
            for (genvar n = 0; n < ACW; n++) begin : gen_paddrchk
                localparam int LO = n * 8;
                localparam int PB = ((AW - LO) < 8) ? (AW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_paddrchk (
                    .data_in     (s_apb_PADDR[LO +: PB]),
                    .parity_in   (s_apb_PADDRCHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_paddrchk_err[n])
                );
            end
            logic [DCW-1:0] w_pwdatachk_err;
            for (genvar n = 0; n < DCW; n++) begin : gen_pwdatachk
                localparam int LO = n * 8;
                localparam int PB = ((DW - LO) < 8) ? (DW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pwdatachk (
                    .data_in     (s_apb_PWDATA[LO +: PB]),
                    .parity_in   (s_apb_PWDATACHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_pwdatachk_err[n])
                );
            end
            logic [AUCW-1:0] w_pauserchk_err;
            for (genvar n = 0; n < AUCW; n++) begin : gen_pauserchk
                localparam int LO = n * 8;
                localparam int PB = ((AUW - LO) < 8) ? (AUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pauserchk (
                    .data_in     (s_apb_PAUSER[LO +: PB]),
                    .parity_in   (s_apb_PAUSERCHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_pauserchk_err[n])
                );
            end
            logic [WUCW-1:0] w_pwuserchk_err;
            for (genvar n = 0; n < WUCW; n++) begin : gen_pwuserchk
                localparam int LO = n * 8;
                localparam int PB = ((WUW - LO) < 8) ? (WUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pwuserchk (
                    .data_in     (s_apb_PWUSER[LO +: PB]),
                    .parity_in   (s_apb_PWUSERCHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_pwuserchk_err[n])
                );
            end
            logic w_pctrlchk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(PW + 1)) u_pctrlchk (
                .data_in     ({s_apb_PWRITE, s_apb_PPROT}),
                .parity_in   (s_apb_PCTRLCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_pctrlchk_err)
            );
            logic w_pstrbchk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(SW)) u_pstrbchk (
                .data_in     (s_apb_PSTRB),
                .parity_in   (s_apb_PSTRBCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_pstrbchk_err)
            );
            logic w_pselchk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pselchk (
                .data_in     (s_apb_PSEL),
                .parity_in   (s_apb_PSELCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_pselchk_err)
            );
            logic w_penablechk_err;
            logic w_pwakeupchk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pwakeupchk (
                .data_in     (s_apb_PWAKEUP),
                .parity_in   (s_apb_PWAKEUPCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_pwakeupchk_err)
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_penablechk (
                .data_in     (s_apb_PENABLE),
                .parity_in   (s_apb_PENABLECHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_penablechk_err)
            );

            // Completer-driven checks
            for (genvar n = 0; n < DCW; n++) begin : gen_prdatachk
                localparam int LO = n * 8;
                localparam int PB = ((DW - LO) < 8) ? (DW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_prdatachk (
                    .data_in     (s_apb_PRDATA[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (s_apb_PRDATACHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            for (genvar n = 0; n < RUCW; n++) begin : gen_pruserchk
                localparam int LO = n * 8;
                localparam int PB = ((RUW - LO) < 8) ? (RUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pruserchk (
                    .data_in     (s_apb_PRUSER[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (s_apb_PRUSERCHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            for (genvar n = 0; n < BUCW; n++) begin : gen_pbuserchk
                localparam int LO = n * 8;
                localparam int PB = ((BUW - LO) < 8) ? (BUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pbuserchk (
                    .data_in     (s_apb_PBUSER[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (s_apb_PBUSERCHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_preadychk (
                .data_in     (s_apb_PREADY),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (s_apb_PREADYCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pslverrchk (
                .data_in     (s_apb_PSLVERR),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (s_apb_PSLVERRCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );

            // Check Enable terms (Table 5-1)
            logic w_en_sel;      // PSEL
            logic w_en_wr;       // PSEL & PWRITE
            logic w_en_reset;    // PRESETn
            assign w_en_sel   = s_apb_PSEL;
            assign w_en_wr    = s_apb_PSEL && s_apb_PWRITE;
            assign w_en_reset = !`RST_ASSERTED(presetn);

            // PWDATACHK, PSTRBCHK, PWUSERCHK
            assign parity_error_wdata = w_en_wr &&
                                        ((|w_pwdatachk_err) || w_pstrbchk_err || (|w_pwuserchk_err));
            // PADDRCHK, PCTRLCHK, PENABLECHK, PAUSERCHK; PSELCHK, PWAKEUPCHK
            assign parity_error_ctrl  = (w_en_sel && ((|w_paddrchk_err) || w_pctrlchk_err ||
                                                      w_penablechk_err || (|w_pauserchk_err))) ||
                                        (w_en_reset && (w_pselchk_err || w_pwakeupchk_err));
        end else begin : gen_no_parity
            assign s_apb_PRDATACHK    = '0;
            assign s_apb_PRUSERCHK    = '0;
            assign s_apb_PBUSERCHK    = '0;
            assign s_apb_PREADYCHK    = 1'b0;
            assign s_apb_PSLVERRCHK   = 1'b0;
            assign parity_error_wdata = 1'b0;
            assign parity_error_ctrl  = 1'b0;
        end
    endgenerate

    // Main APB5 state machine
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_apb_state    <= IDLE;
            s_apb_PREADY   <= 1'b0;
            s_apb_PSLVERR  <= 1'b0;
            s_apb_PRDATA   <= '0;
            s_apb_PRUSER   <= '0;
            s_apb_PBUSER   <= '0;
            r_cmd_valid    <= 1'b0;
            r_rsp_ready    <= 1'b0;
            r_penable_prev <= 1'b0;
        end else begin
            // Default states
            r_apb_state    <= r_apb_state;
            s_apb_PREADY   <= 1'b0;
            s_apb_PSLVERR  <= 1'b0;
            r_cmd_valid    <= 1'b0;
            r_rsp_ready    <= 1'b0;
            r_penable_prev <= s_apb_PENABLE;

            casez (r_apb_state)

                IDLE: begin
                    // Orphan-response guard, carried over from apb4_slave.
                    // A response sitting in the skid with no command
                    // outstanding is not ours to return: without this pop,
                    // the NEXT command consumes it instead of its own
                    // response, which permanently offsets every subsequent
                    // transaction. That misalignment was observed on the
                    // Nexys A7 DDR2 board and persisted until the device was
                    // reprogrammed. Causes are a duplicate backend response
                    // or a CDC reset independently of this side.
                    if (r_rsp_valid) begin
                        r_rsp_ready <= 1'b1;   // pop and drop
                        // synthesis translate_off
                        $display("%t %m WARNING: orphan APB response discarded (prdata=0x%0h pslverr=%0b) -- no command outstanding. Check for duplicate backend responses or an independently-reset CDC.",
                                 $time, r_rsp_prdata, r_rsp_pslverr);
                        // synthesis translate_on
                    end

                    // Only capture on rising edge of PENABLE (SETUP->ACCESS transition)
                    if (s_apb_PSEL && s_apb_PENABLE && !r_penable_prev && r_cmd_ready) begin
                        r_cmd_valid <= 1'b1;
                        r_apb_state <= BUSY;
                    end
                end

                BUSY: begin
                    if (r_rsp_valid) begin
                        s_apb_PREADY  <= 1'b1;
                        s_apb_PRDATA  <= r_rsp_prdata;
                        s_apb_PSLVERR <= r_rsp_pslverr;
                        s_apb_PRUSER  <= r_rsp_pruser;
                        s_apb_PBUSER  <= r_rsp_pbuser;
                        r_rsp_ready   <= 1'b1;
                        r_apb_state   <= WAIT;
                    end
                end

                WAIT: r_apb_state <= IDLE;

                // verilator coverage_off
                // DEFENSIVE: Illegal FSM state recovery
                default: r_apb_state <= IDLE;
                // verilator coverage_on

            endcase
        end
    )

endmodule : apb5_slave
