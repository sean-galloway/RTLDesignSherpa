// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_cdc_fifo
// Purpose: Compact dual-clock FIFO for the HIVE control network, written
//          against the textbook binary-pointer + Gray-crossing scheme:
//            * write-domain binary pointer, Gray-encoded across, 2-flop
//              synchronized into the read domain (and vice versa)
//            * full  = wrap-bit differ && lower bits equal (fifo_control eq.)
//            * empty = pointers equal, COMBINATIONAL rd_valid (mux-mode read,
//              no registered-empty lag — the one-cycle lag of a registered
//              empty flag re-granted just-emptied slaves in the arbiter)
//
//          WORKAROUND COMPONENT: this exists because gaxi_fifo_async
//          (rtl/cdc) showed stuck-flag behaviour at small depths during
//          hive Phase-1 bring-up (vault bug filed with VCD evidence: full
//          flags stuck with wr==rd at DEPTH=2, read-valid stuck after early
//          pops).  Revert hive_ctrl_network to gaxi_fifo_async once the
//          shared library is fixed.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/04_control_network.md
// Subsystem: hive-serv
//
// Author: seang
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hive_cdc_fifo #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH      = 4,
    parameter int N_FLOP_CROSS = 2        // synchronizer stages (>=2)
) (
    input  logic                  axi_wr_aclk,
    input  logic                  axi_wr_aresetn,
    input  logic                  axi_rd_aclk,
    input  logic                  axi_rd_aresetn,

    input  logic                  wr_valid,
    output logic                  wr_ready,
    input  logic [DATA_WIDTH-1:0] wr_data,

    input  logic                  rd_ready,
    output logic                  rd_valid,
    output logic [DATA_WIDTH-1:0] rd_data
);

    localparam int D  = DEPTH;
    localparam int AW = (DEPTH <= 2) ? 1 : $clog2(DEPTH);
    localparam int PW = AW + 1;

    // -----------------------------------------------------------------------
    // Pointers (per domain).  Same MSB-inversion discipline as counter_bin /
    // fifo_sync: the lower AW bits count 0..DEPTH-1, then the wrap bit
    // (bit AW) toggles and the lower bits clear, giving a 2*DEPTH pointer
    // space.  Slot address is the lower AW bits.
    // -----------------------------------------------------------------------
    logic [PW-1:0] r_wr_ptr, r_rd_ptr;

    function automatic [PW-1:0] ptr_next(input [PW-1:0] p);
        ptr_next = (p[AW-1:0] == AW'(DEPTH-1))
                 ? {~p[PW-1], {AW{1'b0}}}
                 : p + PW'(1);
    endfunction

    wire [PW-1:0] w_wr_ptr_next = ptr_next(r_wr_ptr);
    wire [PW-1:0] w_rd_ptr_next = ptr_next(r_rd_ptr);

    `ALWAYS_FF_RST(axi_wr_aclk, axi_wr_aresetn,
        if (`RST_ASSERTED(axi_wr_aresetn)) r_wr_ptr <= '0;
        else if (wr_valid && wr_ready)    r_wr_ptr <= w_wr_ptr_next;
    )

    `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
        if (`RST_ASSERTED(axi_rd_aresetn)) r_rd_ptr <= '0;
        else if (rd_valid && rd_ready)    r_rd_ptr <= w_rd_ptr_next;
    )

    // -----------------------------------------------------------------------
    // Gray crossing
    // -----------------------------------------------------------------------
    function automatic [PW-1:0] bin2gray(input [PW-1:0] b);
        bin2gray = b ^ (b >> 1);
    endfunction

    function automatic [PW-1:0] gray2bin(input [PW-1:0] g);
        logic [PW-1:0] b;
        b[PW-1] = g[PW-1];
        for (int i = PW-2; i >= 0; i--) b[i] = b[i+1] ^ g[i];
        return b;
    endfunction

    logic [PW-1:0] r_wr_gray, r_rd_gray;
    assign r_wr_gray = bin2gray(r_wr_ptr);
    assign r_rd_gray = bin2gray(r_rd_ptr);

    logic [PW-1:0] r_rdom_wr_gray [N_FLOP_CROSS];
    logic [PW-1:0] r_wdom_rd_gray [N_FLOP_CROSS];

    `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
        if (`RST_ASSERTED(axi_rd_aresetn)) begin
            for (int i = 0; i < N_FLOP_CROSS; i++) r_rdom_wr_gray[i] <= '0;
        end else begin
            r_rdom_wr_gray[0] <= r_wr_gray;
            for (int i = 1; i < N_FLOP_CROSS; i++) r_rdom_wr_gray[i] <= r_rdom_wr_gray[i-1];
        end
    )

    `ALWAYS_FF_RST(axi_wr_aclk, axi_wr_aresetn,
        if (`RST_ASSERTED(axi_wr_aresetn)) begin
            for (int i = 0; i < N_FLOP_CROSS; i++) r_wdom_rd_gray[i] <= '0;
        end else begin
            r_wdom_rd_gray[0] <= r_rd_gray;
            for (int i = 1; i < N_FLOP_CROSS; i++) r_wdom_rd_gray[i] <= r_wdom_rd_gray[i-1];
        end
    )

    wire [PW-1:0] w_rdom_wr_bin = gray2bin(r_rdom_wr_gray[N_FLOP_CROSS-1]);
    wire [PW-1:0] w_wdom_rd_bin = gray2bin(r_wdom_rd_gray[N_FLOP_CROSS-1]);

    // -----------------------------------------------------------------------
    // Flags.  full: registered in the write domain.  counter_bin semantics:
    // the "next" pointer only advances when a write is actually accepted, so
    // the fullness lookahead is transactional — base the equation on the
    // post-accept pointer when a write is in flight, else on the current
    // pointer (matches fifo_sync/fifo_control exactly).  empty: combinational
    // from CURRENT pointers so rd_valid never lags a pop.
    // -----------------------------------------------------------------------
    logic r_wr_full;

    wire [PW-1:0] w_wr_base = (wr_valid && wr_ready) ? w_wr_ptr_next : r_wr_ptr;

    wire w_wr_full_d = (w_wr_base[PW-1] != w_wdom_rd_bin[PW-1])
                     && (w_wr_base[AW-1:0] == w_wdom_rd_bin[AW-1:0]);

    `ALWAYS_FF_RST(axi_wr_aclk, axi_wr_aresetn,
        if (`RST_ASSERTED(axi_wr_aresetn)) r_wr_full <= 1'b0;
        else                              r_wr_full <= w_wr_full_d;
    )

    assign wr_ready = !r_wr_full;
    assign rd_valid = (r_rd_ptr != w_rdom_wr_bin);

    // -----------------------------------------------------------------------
    // Memory: write on wr clock, combinational (mux) read at the rd pointer.
    // -----------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] mem [D];

    always_ff @(posedge axi_wr_aclk) begin
        if (wr_valid && wr_ready) begin
            mem[r_wr_ptr[AW-1:0]] <= wr_data;
        end
    end

    assign rd_data = mem[r_rd_ptr[AW-1:0]];

endmodule : hive_cdc_fifo
