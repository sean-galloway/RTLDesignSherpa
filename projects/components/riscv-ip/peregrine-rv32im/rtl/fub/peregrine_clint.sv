// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_clint
// Purpose: peregrine's core-local interruptor (PRD P7), one hart, the
//          SiFive layout at offsets from the CLINT base (0x0200_0000):
//
//            +0x0000  msip      bit 0 drives irq_software (MSIP)
//            +0x4000  mtimecmp  low word
//            +0x4004  mtimecmp  high word
//            +0xBFF8  mtime     low word
//            +0xBFFC  mtime     high word
//
//          mtime counts up once every MTIME_DIV clocks.  irq_timer is
//          registered: (mtime >= mtimecmp), one cycle behind both.
//          Writes take their byte strobes.  Any other offset reads 0 and
//          ignores writes.
//
//          Port: one request per cycle, always ready; the response
//          (rsp_valid, rsp_rdata) is the next cycle, for reads and writes
//          alike, so the core's D-side sees the same 1-cycle shape as a D$
//          hit.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - MTIME_DIV: clocks per mtime increment, >= 1 (default 1).
//
// Notes:
//   - mtimecmp resets to all ones, so no timer interrupt is pending out of
//     reset; mtime resets to 0; msip to 0.
//   - A write to one half of mtime or mtimecmp is not atomic with the
//     other half (the privileged spec's RV32 sequence handles that).
//
// Related Modules:
//   - peregrine_top (D-side decode, interrupt pins)
//
// Test:
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_clint.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_clint #(
    parameter int MTIME_DIV = 1
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        req_valid,
    input  logic [15:0] req_addr,     // offset within the CLINT window
    input  logic        req_we,
    input  logic [3:0]  req_wstrb,
    input  logic [31:0] req_wdata,
    output logic        rsp_valid,
    output logic [31:0] rsp_rdata,
    output logic        irq_software,
    output logic        irq_timer
);

    localparam logic [15:0] OFF_MSIP    = 16'h0000;
    localparam logic [15:0] OFF_CMP_LO  = 16'h4000;
    localparam logic [15:0] OFF_CMP_HI  = 16'h4004;
    localparam logic [15:0] OFF_TIME_LO = 16'hBFF8;
    localparam logic [15:0] OFF_TIME_HI = 16'hBFFC;
    localparam int DIV_W = (MTIME_DIV > 1) ? $clog2(MTIME_DIV) : 1;

    initial begin
        if (MTIME_DIV < 1) $error("peregrine_clint: MTIME_DIV must be >= 1");
    end

    logic        r_msip;
    logic [63:0] r_mtimecmp;
    logic [63:0] r_mtime;
    logic [DIV_W-1:0] r_div;
    logic        w_tick;

    logic [15:0] w_off;
    logic        w_wr;

    assign w_off = {req_addr[15:2], 2'b00};
    assign w_wr  = req_valid & req_we;

    if (MTIME_DIV > 1) begin : g_div
        assign w_tick = (r_div == DIV_W'(MTIME_DIV - 1));
    end else begin : g_nodiv
        assign w_tick = 1'b1;
    end

    function automatic logic [31:0] merge(input logic [31:0] old_w,
                                          input logic [31:0] new_w,
                                          input logic [3:0]  strb);
        logic [31:0] m;
        for (int b = 0; b < 4; b++) begin
            m[b*8 +: 8] = strb[b] ? new_w[b*8 +: 8] : old_w[b*8 +: 8];
        end
        return m;
    endfunction

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_msip     <= 1'b0;
            r_mtimecmp <= '1;
            r_mtime    <= '0;
            r_div      <= '0;
            irq_timer  <= 1'b0;
            rsp_valid  <= 1'b0;
            rsp_rdata  <= '0;
        end else begin
            r_div <= w_tick ? '0 : r_div + 1'b1;

            // mtime: a write wins over the tick for the half it writes
            if (w_wr && w_off == OFF_TIME_LO) begin
                r_mtime[31:0] <= merge(r_mtime[31:0], req_wdata, req_wstrb);
            end else if (w_wr && w_off == OFF_TIME_HI) begin
                r_mtime[63:32] <= merge(r_mtime[63:32], req_wdata, req_wstrb);
            end else if (w_tick) begin
                r_mtime <= r_mtime + 64'd1;
            end

            if (w_wr && w_off == OFF_MSIP && req_wstrb[0]) r_msip <= req_wdata[0];
            if (w_wr && w_off == OFF_CMP_LO)
                r_mtimecmp[31:0] <= merge(r_mtimecmp[31:0], req_wdata, req_wstrb);
            if (w_wr && w_off == OFF_CMP_HI)
                r_mtimecmp[63:32] <= merge(r_mtimecmp[63:32], req_wdata, req_wstrb);

            irq_timer <= (r_mtime >= r_mtimecmp);

            rsp_valid <= req_valid;
            if (req_valid && !req_we) begin
                unique case (w_off)
                    OFF_MSIP:    rsp_rdata <= {31'd0, r_msip};
                    OFF_CMP_LO:  rsp_rdata <= r_mtimecmp[31:0];
                    OFF_CMP_HI:  rsp_rdata <= r_mtimecmp[63:32];
                    OFF_TIME_LO: rsp_rdata <= r_mtime[31:0];
                    OFF_TIME_HI: rsp_rdata <= r_mtime[63:32];
                    default:     rsp_rdata <= 32'd0;
                endcase
            end else begin
                rsp_rdata <= 32'd0;
            end
        end
    )

    assign irq_software = r_msip;

endmodule : peregrine_clint
