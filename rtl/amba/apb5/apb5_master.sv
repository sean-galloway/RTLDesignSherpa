// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_master
// Purpose: APB5 Master with AMBA5 extensions
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes
// - PWUSER: User-defined write data attributes
// - PWAKEUP: Requester wake-up OUTPUT (IHI 0024E 3.7.2, Table 3-7), registered
//   and asserted while a request is pending or a transfer is in flight
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

module apb5_master #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int AUSER_WIDTH     = 4,
    parameter int WUSER_WIDTH     = 4,
    parameter int RUSER_WIDTH     = 4,
    parameter int BUSER_WIDTH     = 4,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter bit ENABLE_PARITY   = 0,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
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

    // APB5 interface (master side)
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    output logic [AUW-1:0]    m_apb_PAUSER,
    output logic [WUW-1:0]    m_apb_PWUSER,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,
    output logic              m_apb_PWAKEUP,        // Requester-driven (Table 3-7)
    input  logic [RUW-1:0]    m_apb_PRUSER,
    input  logic [BUW-1:0]    m_apb_PBUSER,

    // Interface parity check signals, IHI 0024E ch. 5 (ENABLE_PARITY=1).
    // Odd parity; tied LOW and unchecked when ENABLE_PARITY=0.
    output logic [ACW-1:0]    m_apb_PADDRCHK,
    output logic              m_apb_PCTRLCHK,       // PPROT, PWRITE
    output logic              m_apb_PSELCHK,        // PSELxCHK
    output logic              m_apb_PENABLECHK,
    output logic [DCW-1:0]    m_apb_PWDATACHK,
    output logic              m_apb_PSTRBCHK,
    output logic [AUCW-1:0]   m_apb_PAUSERCHK,
    output logic [WUCW-1:0]   m_apb_PWUSERCHK,
    input  logic [DCW-1:0]    m_apb_PRDATACHK,
    input  logic              m_apb_PREADYCHK,
    input  logic              m_apb_PSLVERRCHK,
    output logic              m_apb_PWAKEUPCHK,
    input  logic [RUCW-1:0]   m_apb_PRUSERCHK,
    input  logic [BUCW-1:0]   m_apb_PBUSERCHK,

    // Command Packet interface
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_pwrite,
    input  logic [AW-1:0]     cmd_paddr,
    input  logic [DW-1:0]     cmd_pwdata,
    input  logic [SW-1:0]     cmd_pstrb,
    input  logic [PW-1:0]     cmd_pprot,
    input  logic [AUW-1:0]    cmd_pauser,
    input  logic [WUW-1:0]    cmd_pwuser,

    // Response interface
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [DW-1:0]     rsp_prdata,
    output logic              rsp_pslverr,
    output logic [RUW-1:0]    rsp_pruser,
    output logic [BUW-1:0]    rsp_pbuser,

    // Parity error flags (active when ENABLE_PARITY=1; combinational,
    // asserted while a check's Table 5-1 Check Enable term holds)
    //   parity_error_rdata: PRDATACHK, PRUSERCHK
    //   parity_error_ctrl : PREADYCHK, PSLVERRCHK, PBUSERCHK
    output logic              parity_error_rdata,
    output logic              parity_error_ctrl
);

    // Command FIFO signals
    logic                r_cmd_valid;
    logic                w_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          w_cmd_count;

    // Unpacked command signals
    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [PW-1:0]       r_cmd_pprot;
    logic [AUW-1:0]      r_cmd_pauser;
    logic [WUW-1:0]      r_cmd_pwuser;
    logic                r_cmd_pwrite;

    // Pack command inputs into a single data word
    assign r_cmd_data_in = {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
                            cmd_pauser, cmd_pwuser};

    // Unpack command data for use in the APB interface
    assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata,
            r_cmd_pauser, r_cmd_pwuser} = r_cmd_data_out;

    // Command FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CMD_DEPTH)
    ) cmd_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (cmd_valid),
        .wr_ready     (cmd_ready),
        .wr_data      (r_cmd_data_in),
        .count        (w_cmd_count),
        .rd_valid     (r_cmd_valid),
        .rd_ready     (w_cmd_ready),
        .rd_data      (r_cmd_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Response FIFO signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [3:0]          w_rsp_count;   // rsp skid occupancy (back-to-back gate)
    logic [RPW-1:0]      r_rsp_data_in;
    logic [RPW-1:0]      r_rsp_data_out;

    // Pack response data for the FIFO
    assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PRDATA, m_apb_PRUSER, m_apb_PBUSER};

    // Response FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (RSP_DEPTH)
    ) resp_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (w_rsp_valid),
        .wr_ready     (r_rsp_ready),
        .wr_data      (r_rsp_data_in),
        .count        (w_rsp_count),
        .rd_valid     (rsp_valid),
        .rd_ready     (rsp_ready),
        .rd_data      (r_rsp_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack response data
    assign {rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser} = r_rsp_data_out;

    // APB5 FSM
    typedef enum logic [2:0] {
        IDLE   = 3'b001,
        SETUP  = 3'b010,
        ACCESS = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_apb_state <= IDLE;
        end else begin
            r_apb_state <= w_apb_next_state;
        end
    )

    // PWAKEUP (IHI 0024E 3.7.2). The Requester drives it; the rules are:
    //   - glitch-free, so it comes straight from a flop;
    //   - recommended HIGH at least one cycle before PSEL: a command at the
    //     fub port (cmd_valid) raises it on the next edge, while the command
    //     is still passing through the command skid, so it leads PSEL by one
    //     cycle on a launch from IDLE;
    //   - must stay HIGH until PREADY once it and PSEL are high together: the
    //     FSM is out of IDLE for the whole transfer, including the PREADY
    //     cycle (the flop samples the previous cycle's state);
    //   - recommended LOW when no further transfers are required: every term
    //     is a pending request or an in-flight transfer, nothing else. A
    //     Completer may wait for PWAKEUP before PREADY, so a pending request
    //     must never leave it low.
    // The terms are Requester-side pending work only -- never the peer's
    // PREADY ([[clock-gating-activity-terms]]).
    logic r_pwakeup;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_pwakeup <= 1'b0;
        end else begin
            r_pwakeup <= cmd_valid || r_cmd_valid || (r_apb_state != IDLE);
        end
    )

    assign m_apb_PWAKEUP = r_pwakeup;

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
            for (genvar n = 0; n < ACW; n++) begin : gen_paddrchk
                localparam int LO = n * 8;
                localparam int PB = ((AW - LO) < 8) ? (AW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_paddrchk (
                    .data_in     (m_apb_PADDR[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (m_apb_PADDRCHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            for (genvar n = 0; n < DCW; n++) begin : gen_pwdatachk
                localparam int LO = n * 8;
                localparam int PB = ((DW - LO) < 8) ? (DW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pwdatachk (
                    .data_in     (m_apb_PWDATA[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (m_apb_PWDATACHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            for (genvar n = 0; n < AUCW; n++) begin : gen_pauserchk
                localparam int LO = n * 8;
                localparam int PB = ((AUW - LO) < 8) ? (AUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pauserchk (
                    .data_in     (m_apb_PAUSER[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (m_apb_PAUSERCHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            for (genvar n = 0; n < WUCW; n++) begin : gen_pwuserchk
                localparam int LO = n * 8;
                localparam int PB = ((WUW - LO) < 8) ? (WUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pwuserchk (
                    .data_in     (m_apb_PWUSER[LO +: PB]),
                    .parity_in   (1'b0),
                    .parity_type (1'b0),           // odd
                    .parity      (m_apb_PWUSERCHK[n]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity_err  ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end
            dataint_parity #(.CHUNKS(1), .WIDTH(PW + 1)) u_pctrlchk (
                .data_in     ({m_apb_PWRITE, m_apb_PPROT}),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (m_apb_PCTRLCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(SW)) u_pstrbchk (
                .data_in     (m_apb_PSTRB),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (m_apb_PSTRBCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pselchk (
                .data_in     (m_apb_PSEL),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (m_apb_PSELCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pwakeupchk (
                .data_in     (m_apb_PWAKEUP),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (m_apb_PWAKEUPCHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_penablechk (
                .data_in     (m_apb_PENABLE),
                .parity_in   (1'b0),
                .parity_type (1'b0),               // odd
                .parity      (m_apb_PENABLECHK),
                /* verilator lint_off PINCONNECTEMPTY */
                .parity_err  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );

            // Completer-driven checks
            logic [DCW-1:0] w_prdatachk_err;
            for (genvar n = 0; n < DCW; n++) begin : gen_prdatachk
                localparam int LO = n * 8;
                localparam int PB = ((DW - LO) < 8) ? (DW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_prdatachk (
                    .data_in     (m_apb_PRDATA[LO +: PB]),
                    .parity_in   (m_apb_PRDATACHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_prdatachk_err[n])
                );
            end
            logic [RUCW-1:0] w_pruserchk_err;
            for (genvar n = 0; n < RUCW; n++) begin : gen_pruserchk
                localparam int LO = n * 8;
                localparam int PB = ((RUW - LO) < 8) ? (RUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pruserchk (
                    .data_in     (m_apb_PRUSER[LO +: PB]),
                    .parity_in   (m_apb_PRUSERCHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_pruserchk_err[n])
                );
            end
            logic [BUCW-1:0] w_pbuserchk_err;
            for (genvar n = 0; n < BUCW; n++) begin : gen_pbuserchk
                localparam int LO = n * 8;
                localparam int PB = ((BUW - LO) < 8) ? (BUW - LO) : 8;
                dataint_parity #(.CHUNKS(1), .WIDTH(PB)) u_pbuserchk (
                    .data_in     (m_apb_PBUSER[LO +: PB]),
                    .parity_in   (m_apb_PBUSERCHK[n]),
                    .parity_type (1'b0),           // odd
                    /* verilator lint_off PINCONNECTEMPTY */
                    .parity      (),
                    /* verilator lint_on PINCONNECTEMPTY */
                    .parity_err  (w_pbuserchk_err[n])
                );
            end
            logic w_preadychk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_preadychk (
                .data_in     (m_apb_PREADY),
                .parity_in   (m_apb_PREADYCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_preadychk_err)
            );
            logic w_pslverrchk_err;
            dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_pslverrchk (
                .data_in     (m_apb_PSLVERR),
                .parity_in   (m_apb_PSLVERRCHK),
                .parity_type (1'b0),               // odd
                /* verilator lint_off PINCONNECTEMPTY */
                .parity      (),
                /* verilator lint_on PINCONNECTEMPTY */
                .parity_err  (w_pslverrchk_err)
            );

            // Check Enable terms (Table 5-1)
            logic w_en_ready;    // PSEL & PENABLE
            logic w_en_rsp;      // PSEL & PENABLE & PREADY
            logic w_en_rdata;    // PSEL & PENABLE & PREADY & !PWRITE
            assign w_en_ready = m_apb_PSEL && m_apb_PENABLE;
            assign w_en_rsp   = w_en_ready && m_apb_PREADY;
            assign w_en_rdata = w_en_rsp && !m_apb_PWRITE;

            // PRDATACHK, PRUSERCHK
            assign parity_error_rdata = w_en_rdata &&
                                        ((|w_prdatachk_err) || (|w_pruserchk_err));
            // PREADYCHK, PSLVERRCHK, PBUSERCHK
            assign parity_error_ctrl  = (w_en_ready && w_preadychk_err) ||
                                        (w_en_rsp   && (w_pslverrchk_err || (|w_pbuserchk_err)));
        end else begin : gen_no_parity
            assign m_apb_PADDRCHK     = '0;
            assign m_apb_PWDATACHK    = '0;
            assign m_apb_PAUSERCHK    = '0;
            assign m_apb_PWUSERCHK    = '0;
            assign m_apb_PCTRLCHK     = 1'b0;
            assign m_apb_PSTRBCHK     = 1'b0;
            assign m_apb_PSELCHK      = 1'b0;
            assign m_apb_PENABLECHK   = 1'b0;
            assign m_apb_PWAKEUPCHK   = 1'b0;
            assign parity_error_rdata = 1'b0;
            assign parity_error_ctrl  = 1'b0;
        end
    endgenerate

    // Main APB5 state machine
    always_comb begin
        // Default assignments
        w_apb_next_state = r_apb_state;
        m_apb_PSEL = 1'b0;
        m_apb_PENABLE = 1'b0;
        m_apb_PADDR = r_cmd_paddr;
        m_apb_PWRITE = r_cmd_pwrite;
        m_apb_PWDATA = r_cmd_pwdata;
        m_apb_PSTRB = r_cmd_pstrb;
        m_apb_PPROT = r_cmd_pprot;
        m_apb_PAUSER = r_cmd_pauser;
        m_apb_PWUSER = r_cmd_pwuser;
        w_cmd_ready = 1'b0;
        w_rsp_valid = 1'b0;

        casez (r_apb_state)
            IDLE: begin
                // Start transaction if there's a valid command.
                //
                // PSEL stays LOW here: this cycle is still IDLE, and SETUP
                // is the setup phase. Asserting it here too gave every
                // launch-from-idle transfer a TWO-cycle setup phase where
                // APB defines exactly one (TASK-071). The state sequence is
                // unchanged, so this costs no latency.
                // Start a transaction only when a command is pending AND
                // the response skid has space. Launch-gating is the deadlock
                // fix carried over from apb4_master (TASK-068): the completed
                // transfer's response must be enqueueable, or ACCESS would
                // have to hold PENABLE past PREADY -- a protocol violation --
                // against a one-shot-PREADY slave that never re-fires, which
                // wedges the bus permanently. This FSM is the skid's only
                // writer, so space at launch holds through completion.
                if (r_cmd_valid && r_rsp_ready) begin
                    w_apb_next_state = SETUP;
                end
            end

            SETUP: begin
                // Setup phase - assert PSEL without PENABLE. Exactly one
                // cycle, reached from IDLE on launch or from ACCESS on the
                // back-to-back shortcut.
                m_apb_PSEL = 1'b1;

                // Always move to ACCESS phase
                w_apb_next_state = ACCESS;
            end

            ACCESS: begin
                // Access phase - assert both PSEL and PENABLE
                m_apb_PSEL = 1'b1;
                m_apb_PENABLE = 1'b1;

                // Wait for slave to respond with PREADY. Response space was
                // guaranteed at launch (IDLE and the back-to-back shortcut
                // both gate on r_rsp_ready), so completion always enqueues and
                // this state never has to hold PENABLE past PREADY.
                if (m_apb_PREADY) begin
                    w_rsp_valid = 1'b1;
                    w_cmd_ready = 1'b1;

                    // Back-to-back only when the NEXT response also has space
                    // AFTER this cycle's enqueue -- r_rsp_ready alone is stale
                    // by one entry here (it predates the enqueue), and
                    // launching on the last slot would lose the next response.
                    // Otherwise drain through IDLE, which re-applies the
                    // launch gate on fresh state.
                    if (w_cmd_count > 1 && (32'(w_rsp_count) <= RSP_DEPTH - 2))
                        w_apb_next_state = SETUP;
                    else
                        w_apb_next_state = IDLE;
                end
            end

            // verilator coverage_off
            // DEFENSIVE: Illegal FSM state recovery
            default: w_apb_next_state = IDLE;
            // verilator coverage_on
        endcase
    end

endmodule : apb5_master
