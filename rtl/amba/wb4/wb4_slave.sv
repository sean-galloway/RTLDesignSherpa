// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave
// Purpose: Wishbone B4 slave (pipelined, or classic with CLASSIC=1) that
//          presents each accepted transfer on a valid/ready command queue
//          and terminates it from a valid/ready response queue (the same
//          FUB-side contract as apb4_slave).
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_slave.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Accepts Wishbone B4 PIPELINED transfers one per clock while the command
//   queue has room and fewer than MAX_OUTSTANDING transfers await termination,
//   and terminates them IN ORDER from the response queue with a registered
//   ACK, ERR or RTY plus read data. No state machine: STALL is the inverse of
//   "can accept", and the response side is a counter and a register.
//
// Features:
//   - One accept and one termination per clock (full pipelined throughput)
//   - Backpressure by STALL only; STB is never dropped
//   - RTY comes from the FUB's response status, so a FUB can ask the master
//     to retry without the slave knowing why
//   - Orphan-response guard: a response with nothing outstanding is dropped
//     (and reported in simulation) rather than left to mis-pair the next
//     transfer
//   - A master that drops CYC with transfers outstanding aborts them: the
//     outstanding count moves to an "abandoned" count and that many later
//     responses are discarded, even if a new cycle has begun by then
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH:       Wishbone address width (default 32)
//   DATA_WIDTH:       Wishbone data width, port size (default 32)
//   SEL_WIDTH:        byte-select width, DATA_WIDTH/8 (derived)
//   CMD_DEPTH:        command queue depth in ENTRIES, 2..8
//   RSP_DEPTH:        response queue depth in ENTRIES, 2..8
//   MAX_OUTSTANDING:  transfers accepted but not yet terminated before STALL
//                     (default 16). Bounds the FUB's in-order pipeline; a
//                     master's own limit is its RSP_DEPTH.
//   CLASSIC:          0 = B4 pipelined (default). 1 = B4 standard ("classic")
//                     mode for classic masters, which hold STB until the
//                     termination and never sample STALL: a request is
//                     accepted once per presentation (not again on every
//                     clock it is held) and STALL is driven low. Match the
//                     mode to the peer; cross-mode pairs are not legal
//                     (B4 chapter 5).
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   clk / aresetn      : clock, active-low async reset (repo convention)
//   s_wb_CYC/STB/WE/ADR/DAT_W/SEL : Wishbone slave inputs
//   s_wb_STALL/ACK/ERR/RTY/DAT_R  : Wishbone slave outputs (all registered
//                                   except STALL)
//   cmd_*              : command queue out (valid/ready, we, adr, dat, sel)
//   rsp_*              : response queue in  (valid/ready, status, dat)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   STB accepted -> cmd_valid    : 1 clock (through the command skid)
//   rsp_valid    -> ACK/ERR/RTY  : 2 clocks (response skid + output register)
//   STALL                        : combinational from queue room and the
//                                  outstanding count (no path from STB)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   accept = CYC && STB && !STALL   -> push {we, adr, dat, sel}, r_outstanding++
//   STALL  = !cmd skid room || r_outstanding == MAX_OUTSTANDING
//   term   = rsp head valid && r_outstanding != 0 && CYC
//            -> register ACK|ERR|RTY from status, DAT_R, pop, r_outstanding--
//   orphan = rsp head valid && (r_outstanding == 0 || r_abandoned != 0)
//            -> pop and drop (r_abandoned-- when it was owed)
//   abort  = !CYC && r_outstanding != 0 -> r_abandoned += r_outstanding,
//            r_outstanding <= 0. The FUB still answers those commands
//            later, possibly after the master has started a NEW cycle; the
//            next r_abandoned responses are dropped so they are never
//            paired with the new cycle's transfers.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - wb4_master.sv  - the mirror image (command/response in, Wishbone out)
//   - apb4_slave.sv  - the same FUB-side contract over APB
//   - gaxi_skid_buffer.sv - both queues
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_wb4_master_slave.py (master <-> slave loop)
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_slave
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int SEL_WIDTH       = DATA_WIDTH / 8,
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

    // Wishbone B4 pipelined slave
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // Command queue (bus -> FUB)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_we,
    output logic [AW-1:0]     cmd_adr,
    output logic [DW-1:0]     cmd_dat,
    output logic [SW-1:0]     cmd_sel,

    // Response queue (FUB -> bus)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat
);

    // ------------------------------------------------------------------------
    // Outstanding transfers: accepted on the bus, not yet terminated.
    // ------------------------------------------------------------------------
    localparam int OW  = $clog2(MAX_OUTSTANDING + 1);
    // Responses still owed for aborted transfers. Sized for two back-to-back
    // aborts' worth; saturates beyond that (a FUB that never answers an
    // accepted command has already broken its contract).
    localparam int ABW = OW + 1;
    localparam int AB_MAX = (1 << ABW) - 1;

    logic [OW-1:0]  r_outstanding;
    logic [ABW-1:0] r_abandoned;
    logic           w_drop_abandoned;
    logic           w_accept;
    logic           w_term;
    logic           w_orphan;
    logic           w_cmd_room;      // command skid can take one

    // ------------------------------------------------------------------------
    // Command queue
    // ------------------------------------------------------------------------
    logic [CPW-1:0]  w_cmd_data_in;
    logic [CPW-1:0]  r_cmd_data_out;

    assign w_cmd_data_in = {s_wb_WE, s_wb_ADR, s_wb_DAT_W, s_wb_SEL};
    assign {cmd_we, cmd_adr, cmd_dat, cmd_sel} = r_cmd_data_out;

    generate
        if (CLASSIC != 0) begin : g_classic
            // B4 standard mode: the master holds STB until it sees the
            // termination and never looks at STALL. A request is accepted
            // ONCE, when nothing is outstanding; the held STB on later clocks
            // is the same request waiting for its termination. Backpressure
            // is simply not accepting: the master waits.
            // The held STB is still on the wire in the clock the termination
            // is driven (the master sees the termination at the NEXT edge),
            // so an accept is also refused while ACK/ERR/RTY is high --
            // otherwise the same presentation is accepted twice.
            assign s_wb_STALL = 1'b0;
            assign w_accept   = s_wb_CYC && s_wb_STB && w_cmd_room && (r_outstanding == '0)
                                && !(s_wb_ACK || s_wb_ERR || s_wb_RTY);
        end else begin : g_pipelined
            // STALL is the ONLY backpressure a pipelined slave has, and it must
            // not depend on STB (B4 permits STALL to be asserted with no
            // request). Both terms here are state: skid room and the
            // outstanding count.
            assign s_wb_STALL = !w_cmd_room || (32'(r_outstanding) >= MAX_OUTSTANDING);
            assign w_accept   = s_wb_CYC && s_wb_STB && !s_wb_STALL;
        end
    endgenerate

    gaxi_skid_buffer #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CMD_DEPTH)
    ) u_cmd_skid (
        .axi_aclk     (clk),
        .axi_aresetn  (aresetn),
        .wr_valid     (w_accept),
        .wr_ready     (w_cmd_room),
        .wr_data      (w_cmd_data_in),
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        .rd_data      (r_cmd_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------------
    // Response queue
    // ------------------------------------------------------------------------
    logic            r_rsp_valid;     // head of the response queue is valid
    logic            w_rsp_pop;
    logic [RPW-1:0]  w_rsp_data_in;
    logic [RPW-1:0]  r_rsp_data_out;
    logic [STW-1:0]  r_rsp_status;
    logic [DW-1:0]   r_rsp_dat;

    assign w_rsp_data_in = {rsp_status, rsp_dat};
    assign {r_rsp_status, r_rsp_dat} = r_rsp_data_out;

    gaxi_skid_buffer #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (RSP_DEPTH)
    ) u_rsp_skid (
        .axi_aclk     (clk),
        .axi_aresetn  (aresetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (w_rsp_data_in),
        .rd_valid     (r_rsp_valid),
        .rd_ready     (w_rsp_pop),
        .rd_data      (r_rsp_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------------
    // Termination: registered, in order, only inside a cycle.
    // ------------------------------------------------------------------------
    // A response with nothing outstanding cannot belong to any transfer
    // (duplicate from the FUB, or a response to a transfer the master
    // aborted). Drop it; otherwise it would terminate the NEXT transfer and
    // every later response would be off by one -- the positional mis-pairing
    // apb4_slave's orphan guard exists for.
    // A response owed to an abandoned transfer is dropped FIRST, whatever the
    // new cycle has outstanding: the FUB answers in order, so the oldest
    // response belongs to the oldest command, which was the abandoned one.
    assign w_drop_abandoned = r_rsp_valid && (r_abandoned != '0);
    assign w_term    = r_rsp_valid && (r_outstanding != '0) && s_wb_CYC && (r_abandoned == '0);
    assign w_orphan  = r_rsp_valid && ((r_outstanding == '0) || w_drop_abandoned);
    assign w_rsp_pop = w_term || w_orphan;

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_outstanding <= '0;
            r_abandoned   <= '0;
            s_wb_ACK      <= 1'b0;
            s_wb_ERR      <= 1'b0;
            s_wb_RTY      <= 1'b0;
            s_wb_DAT_R    <= '0;
        end else begin
            // Exactly one of ACK/ERR/RTY, for exactly one clock per response.
            s_wb_ACK <= w_term && (r_rsp_status == WB4_RSP_ACK);
            s_wb_ERR <= w_term && (r_rsp_status == WB4_RSP_ERR);
            s_wb_RTY <= w_term && (r_rsp_status == WB4_RSP_RTY);
            if (w_term)
                s_wb_DAT_R <= r_rsp_dat;   // holds between terminations

            if (!s_wb_CYC) begin
                // The master ended the cycle. Anything still outstanding was
                // abandoned; remember how many responses are still owed for
                // it so they are dropped when they come -- even after a new
                // cycle has started.
                r_outstanding <= '0;
                if (32'(r_abandoned) + 32'(r_outstanding) - 32'(w_drop_abandoned) > AB_MAX)
                    r_abandoned <= ABW'(AB_MAX);
                else
                    r_abandoned <= r_abandoned + ABW'(r_outstanding) - ABW'(w_drop_abandoned);
            end else begin
                r_outstanding <= r_outstanding + OW'(w_accept) - OW'(w_term);
                r_abandoned   <= r_abandoned - ABW'(w_drop_abandoned);
            end
        end
    )

`ifndef FORMAL
    // synthesis translate_off
    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
        end else begin
            if (w_drop_abandoned)
                $display("%t %m INFO: response for an aborted transfer discarded (status=%0d dat=0x%0h), %0d more owed",
                         $time, r_rsp_status, r_rsp_dat, r_abandoned - 1);
            else if (w_orphan)
                $display("%t %m WARNING: orphan Wishbone response discarded (status=%0d dat=0x%0h) -- nothing outstanding. Check for duplicate FUB responses.",
                         $time, r_rsp_status, r_rsp_dat);
            if (!s_wb_CYC && r_outstanding != '0)
                $display("%t %m WARNING: master dropped CYC with %0d transfer(s) outstanding -- aborted",
                         $time, r_outstanding);
        end
    )
    // synthesis translate_on
`endif

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge clk) f_past_valid <= 1'b1;

    always_ff @(posedge clk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // At most one termination signal per clock.
        assert ($onehot0({s_wb_ACK, s_wb_ERR, s_wb_RTY}));
        // A termination is only ever driven for a transfer the master had
        // outstanding inside a cycle.
        if (s_wb_ACK || s_wb_ERR || s_wb_RTY)
            assert ($past(s_wb_CYC) && $past(r_outstanding) != 0);
        // The outstanding count never exceeds its bound.
        assert (32'(r_outstanding) <= MAX_OUTSTANDING);
        // An accept always found queue room (STALL covers the skid).
        assert (!w_accept || w_cmd_room);
        // No termination is driven while responses for abandoned transfers
        // are still owed: the oldest response cannot belong to the new cycle.
        assert (!w_term || r_abandoned == 0);
        if ($past(!s_wb_CYC) && $past(r_outstanding) != 0)
            assert (r_abandoned != 0);
        if (CLASSIC != 0) begin
            // One at a time, and STALL never rises.
            assert (r_outstanding <= 1);
            assert (!s_wb_STALL);
        end
    end
`endif

endmodule : wb4_slave
