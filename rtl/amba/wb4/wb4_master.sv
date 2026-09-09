// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_master
// Purpose: Wishbone B4 pipelined master behind a valid/ready command queue
//          and a valid/ready response queue (the same FUB-side contract as
//          apb4_master).
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Converts a command stream {we, adr, dat, sel} into Wishbone B4 PIPELINED
//   bus cycles and returns every termination as a response {status, dat}.
//   There is no state machine: STB follows the head of the command queue, a
//   command is accepted by the slave on STB && !STALL, and every ACK/ERR/RTY
//   is enqueued as it arrives. Terminations arrive in issue order (B4 rule),
//   so no tags are needed.
//
// Features:
//   - One command per clock while the slave does not STALL
//   - Up to RSP_DEPTH transfers in flight; issue is credit-gated so a
//     termination can ALWAYS be enqueued (the bus cannot stall a response)
//   - RTY is reported in the status, never retried here -- retry policy
//     belongs to the FUB
//   - CYC is held for the whole cycle: from the first STB until the last
//     outstanding transfer terminates
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH:  Wishbone address width (default 32)
//   DATA_WIDTH:  Wishbone data width, port size (default 32)
//   SEL_WIDTH:   byte-select width, DATA_WIDTH/8 (derived)
//   CMD_DEPTH:   command queue depth in ENTRIES, 2..8 (gaxi_skid_buffer)
//   RSP_DEPTH:   response queue depth in ENTRIES, 2..8; also the maximum
//                number of transfers in flight on the bus
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   clk / aresetn      : clock, active-low async reset (repo convention; the
//                        Wishbone RST_I polarity is the integrator's inverter)
//   m_wb_CYC/STB/WE/ADR/DAT_W/SEL : Wishbone master outputs
//   m_wb_STALL/ACK/ERR/RTY/DAT_R  : Wishbone master inputs
//   cmd_*              : command queue in  (valid/ready, we, adr, dat, sel)
//   rsp_*              : response queue out (valid/ready, status, dat)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   cmd accepted -> STB          : 1 clock (through the command skid)
//   ACK/ERR/RTY  -> rsp_valid    : 1 clock (through the response skid)
//   Throughput                   : one transfer per clock in both directions
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   issue    = r_cmd_valid && (r_reserved < RSP_DEPTH)
//   STB      = issue;  CYC = STB || r_inflight != 0
//   accept   = STB && !STALL           -> pop command, r_inflight++, r_reserved++
//   term     = CYC && (ACK|ERR|RTY)    -> push {status, DAT_R}, r_inflight--
//   rsp pop  = rsp_valid && rsp_ready  -> r_reserved--
//   r_reserved counts transfers issued and not yet CONSUMED downstream
//   (in flight + queued), so it is the only gate a termination needs.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - wb4_slave.sv   - the mirror image (Wishbone in, command/response out)
//   - apb4_master.sv - the same FUB-side contract over APB
//   - gaxi_skid_buffer.sv - both queues
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_wb4_master_slave.py (master <-> slave loop)
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_master
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int CMD_DEPTH  = 4,
    parameter int RSP_DEPTH  = 4,
    parameter int SEL_WIDTH  = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CPW = 1 + AW + DW + SW,   // command packet: {we, adr, dat, sel}
    parameter int RPW = STW + DW            // response packet: {status, dat}
) (
    // Clock and Reset
    input  logic              clk,
    input  logic              aresetn,

    // Wishbone B4 pipelined master
    output logic              m_wb_CYC,
    output logic              m_wb_STB,
    output logic              m_wb_WE,
    output logic [AW-1:0]     m_wb_ADR,
    output logic [DW-1:0]     m_wb_DAT_W,
    output logic [SW-1:0]     m_wb_SEL,
    input  logic              m_wb_STALL,
    input  logic              m_wb_ACK,
    input  logic              m_wb_ERR,
    input  logic              m_wb_RTY,
    input  logic [DW-1:0]     m_wb_DAT_R,

    // Command queue (FUB -> bus)
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,

    // Response queue (bus -> FUB)
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat
);

    // ------------------------------------------------------------------------
    // Command queue
    // ------------------------------------------------------------------------
    logic                r_cmd_valid;     // head of the command queue is valid
    logic                w_cmd_pop;       // the slave accepted the head this clock
    logic [CPW-1:0]      w_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;

    assign w_cmd_data_in = {cmd_we, cmd_adr, cmd_dat, cmd_sel};
    assign {m_wb_WE, m_wb_ADR, m_wb_DAT_W, m_wb_SEL} = r_cmd_data_out;

    gaxi_skid_buffer #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CMD_DEPTH)
    ) u_cmd_skid (
        .axi_aclk     (clk),
        .axi_aresetn  (aresetn),
        .wr_valid     (cmd_valid),
        .wr_ready     (cmd_ready),
        .wr_data      (w_cmd_data_in),
        .rd_valid     (r_cmd_valid),
        .rd_ready     (w_cmd_pop),
        .rd_data      (r_cmd_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------------
    // Response queue
    // ------------------------------------------------------------------------
    logic                w_rsp_push;      // a termination arrived this clock
    logic                w_rsp_space;     // skid can take it (always true by construction)
    logic [STW-1:0]      w_status;
    logic [RPW-1:0]      w_rsp_data_in;

    // ERR and RTY are mutually exclusive by the spec; ERR wins if a slave
    // breaks that, so a broken slave reads as an error rather than a retry.
    assign w_status      = m_wb_ERR ? WB4_RSP_ERR :
                           m_wb_RTY ? WB4_RSP_RTY : WB4_RSP_ACK;
    assign w_rsp_data_in = {w_status, m_wb_DAT_R};

    gaxi_skid_buffer #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (RSP_DEPTH)
    ) u_rsp_skid (
        .axi_aclk     (clk),
        .axi_aresetn  (aresetn),
        .wr_valid     (w_rsp_push),
        .wr_ready     (w_rsp_space),
        .wr_data      (w_rsp_data_in),
        .rd_valid     (rsp_valid),
        .rd_ready     (rsp_ready),
        .rd_data      ({rsp_status, rsp_dat}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------------
    // Credit and cycle tracking. No FSM: two counters and three wires.
    // ------------------------------------------------------------------------
    localparam int CW = $clog2(RSP_DEPTH + 1);

    logic [CW-1:0]  r_inflight;   // accepted by the slave, not yet terminated
    logic [CW-1:0]  r_reserved;   // issued, not yet consumed from rsp_*: in flight + queued
    logic           w_issue;      // head may be presented on the bus
    logic           w_term;       // a termination is on the bus this clock
    logic           w_rsp_pop;

    // A termination can never be stalled (Wishbone gives the master no way to
    // refuse an ACK), so a transfer is only put on the bus when its response
    // slot is already reserved. r_reserved counts everything issued that the
    // FUB has not yet taken off rsp_*, which is exactly what occupies the
    // response skid in the worst case; r_reserved <= RSP_DEPTH therefore
    // guarantees w_rsp_space at every termination. This replaces the "count is
    // stale by one" hazard the apb4_master back-to-back path had to reason
    // about: the reservation is taken at issue, not read back from the skid.
    assign w_issue   = r_cmd_valid && (32'(r_reserved) < RSP_DEPTH);
    assign m_wb_STB  = w_issue;
    assign m_wb_CYC  = w_issue || (r_inflight != '0);
    assign w_cmd_pop = m_wb_STB && !m_wb_STALL;
    assign w_term    = m_wb_CYC && (m_wb_ACK || m_wb_ERR || m_wb_RTY);
    assign w_rsp_push = w_term;
    assign w_rsp_pop  = rsp_valid && rsp_ready;

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_inflight <= '0;
            r_reserved <= '0;
        end else begin
            r_inflight <= r_inflight + CW'(w_cmd_pop) - CW'(w_term);
            r_reserved <= r_reserved + CW'(w_cmd_pop) - CW'(w_rsp_pop);
        end
    )

`ifndef FORMAL
    // synthesis translate_off
    // Simulation-only reports. A termination with nothing in flight is a
    // slave protocol violation (ACK outside a cycle, or more terminations
    // than accepted STBs); it is still enqueued, so the FUB sees it. A push
    // with no space cannot happen while the credit invariant holds -- if it
    // ever prints, the invariant is broken, not the skid.
    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
        end else begin
            if (w_term && r_inflight == '0 && !w_cmd_pop)
                $display("%t %m WARNING: Wishbone termination with no transfer in flight (status=%0d)",
                         $time, w_status);
            if (w_rsp_push && !w_rsp_space)
                $display("%t %m ERROR: response lost -- termination with the response queue full",
                         $time);
        end
    )
    // synthesis translate_on
`endif

`ifdef FORMAL
    // Wishbone B4 rules this block is responsible for, plus the sizing
    // invariant the credit scheme rests on.
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge clk) f_past_valid <= 1'b1;

    always_ff @(posedge clk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // CYC covers every in-flight transfer.
        assert (!(r_inflight != '0) || m_wb_CYC);
        // STB implies CYC (B4 rule 3.25).
        assert (!m_wb_STB || m_wb_CYC);
        // A stalled STB holds its request stable (B4 rule 3.60-ish for
        // pipelined: the master may not change ADR/DAT/SEL/WE while stalled).
        if ($past(m_wb_STB) && $past(m_wb_STALL) && $past(m_wb_CYC)) begin
            assert (m_wb_STB);
            assert ($stable(m_wb_ADR) && $stable(m_wb_DAT_W) && $stable(m_wb_SEL) && $stable(m_wb_WE));
        end
        // The credit invariant: never more reserved than the response skid holds.
        assert (32'(r_reserved) <= RSP_DEPTH);
        assert (r_inflight <= r_reserved);
        // A termination always found space (the whole point of the credit).
        assert (!w_rsp_push || w_rsp_space);
    end
`endif

endmodule : wb4_master
