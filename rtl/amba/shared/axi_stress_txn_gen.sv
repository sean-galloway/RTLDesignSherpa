// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_txn_gen
// Purpose: Random, always-legal AXI burst descriptors for one direction of a
//          bus-stress master, drawn from a table of target windows.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Two registered stages behind a valid/ready output:
//
//   draw      three xorshift32 streams pick the window (uniformly among the
//             enabled ones), the size, burst type, length,
//             window offset, ID, QoS and the idle gap before the burst
//   legalize  clamp to what the window allows and to what AXI allows:
//               size     into [size_min, size_max], and to the bus width and
//                        the window
//               burst    the drawn type if the window's burst_mask allows it,
//                        else INCR, else the lowest allowed type
//               WRAP     length 2/4/8/16, the largest one len_mask reaches; a
//                        WRAP that cannot fit the window or the 4 KB page, or
//                        a window with len_mask 0, becomes INCR
//               FIXED    at most 16 beats
//               address  window base | random offset; on the size grid unless
//                        the window allows unaligned INCR/FIXED starts
//               INCR     shortened so it neither crosses 4 KB nor leaves the
//                        window
//             The window's len_mask is ANDed with LEN_MASK first, so an
//             AXI3 shell never sees a burst longer than 16 beats.
//             One draw in eight is forced to a single beat, so single-beat
//             traffic is always present whatever len_mask says.
//
// The streams step once per descriptor taken, never per cycle, so the
// descriptor sequence is a function of the seed alone: a run on the board and
// the same seed in simulation issue identical bursts whatever the back
// pressure was.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_txn_gen
    import axi_stress_pkg::*;
#(
    parameter int NWIN    = 8,                 // power of two, 2..8
    parameter int IW      = 8,                 // 1..16
    parameter int BUS_LG2 = 3,                 // log2(bus bytes)
    parameter logic [7:0]  LEN_MASK = 8'hFF,   // protocol AxLEN limit (AXI3: 8'h0F)
    parameter logic [31:0] SALT = 32'h0        // decorrelates rd from wr
) (
    input  logic                aclk,
    input  logic                aresetn,

    input  logic                restart,       // reseed and flush (GO)
    input  logic                run,           // draw while high
    input  logic [31:0]         cfg_seed,
    input  logic [15:0]         cfg_id_base,
    input  logic [15:0]         cfg_id_mask,
    input  logic [7:0]          cfg_gap_mask,
    input  logic                cfg_qos_rand,
    input  stress_win_t         cfg_win  [NWIN],
    input  logic [NWIN-1:0]     cfg_win_en,    // this direction's enables

    output logic                txn_valid,
    input  logic                txn_ready,
    output logic [31:0]         txn_addr,
    output logic [7:0]          txn_len,
    output logic [2:0]          txn_size,
    output logic [1:0]          txn_burst,
    output logic [IW-1:0]       txn_id,
    output logic [3:0]          txn_qos,
    output logic [7:0]          txn_gap,
    output logic [7:0]          txn_tag,
    output logic [1:0]          txn_resp,      // the window's expected response
    output logic                txn_strb_rand,
    output logic                txn_sb,        // AXI5: the window expects responses to echo
    output logic [3:0]          txn_plg2       // AXI5: the window's poison rate
);

    localparam int WSW = (NWIN > 1) ? $clog2(NWIN) : 1;

    // ---- PRNG ----------------------------------------------------------------
    logic [31:0] r_ra, r_rb, r_rc;
    logic [31:0] w_seed;
    assign w_seed = ((cfg_seed == '0) ? 32'hC0FF_EE11 : cfg_seed) ^ SALT;

    // ---- stage 1: draw -------------------------------------------------------
    logic            r_d_valid;
    logic [WSW-1:0]  r_d_win;
    logic [2:0]      r_d_size;
    logic [1:0]      r_d_burst;
    logic [7:0]      r_d_len;
    logic [1:0]      r_d_wrapk;
    logic            r_d_single;
    logic [31:0]     r_d_off;
    logic [IW-1:0]   r_d_id;
    logic [3:0]      r_d_qos;
    logic [7:0]      r_d_gap;

    logic            w_d_take;     // stage 2 accepts stage 1
    logic            w_d_load;     // stage 1 draws

    // The window: uniform over the enabled ones -- the k-th enabled window,
    // k = random mod (number enabled).
    logic [WSW-1:0]  w_pick;
    logic            w_pick_ok;
    always_comb begin
        logic [3:0] n, k, seen;
        n = '0;
        for (int i = 0; i < NWIN; i++) n = n + 4'(cfg_win_en[i]);
        k    = (n == '0) ? 4'd0 : 4'(r_ra[7:0] % 8'(n));
        seen = '0;
        w_pick    = '0;
        w_pick_ok = (n != '0);
        for (int i = 0; i < NWIN; i++) begin
            if (cfg_win_en[i]) begin
                if (seen == k) w_pick = WSW'(i);
                seen = seen + 4'd1;
            end
        end
    end

    assign w_d_load = run && w_pick_ok && (!r_d_valid || w_d_take);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ra      <= 32'h1;
            r_rb      <= 32'h1;
            r_rc      <= 32'h1;
            r_d_valid <= 1'b0;
        end else if (restart) begin
            r_ra      <= f_xs32(w_seed);
            r_rb      <= f_xs32(f_xs32(w_seed ^ 32'h9E37_79B9));
            r_rc      <= f_xs32(f_xs32(f_xs32(w_seed ^ 32'h7F4A_7C15)));
            r_d_valid <= 1'b0;
        end else begin
            if (w_d_load) begin
                r_ra <= f_xs32(r_ra);
                r_rb <= f_xs32(r_rb);
                r_rc <= f_xs32(r_rc);
            end
            if (w_d_load)       r_d_valid <= 1'b1;
            else if (w_d_take)  r_d_valid <= 1'b0;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_d_load) begin
            r_d_win    <= w_pick;
            r_d_size   <= r_ra[10:8];
            r_d_burst  <= r_ra[12:11];
            r_d_len    <= r_ra[20:13];
            r_d_wrapk  <= r_ra[22:21];
            r_d_single <= (r_ra[25:23] == 3'd0);
            r_d_qos    <= r_ra[29:26];
            r_d_off    <= r_rb;
            r_d_id     <= IW'(cfg_id_base) ^ (IW'(r_rc) & IW'(cfg_id_mask));
            r_d_gap    <= r_rc[31:24] & cfg_gap_mask;
        end
    end

    // ---- stage 2: legalize ---------------------------------------------------
    stress_win_t w_w;
    assign w_w = cfg_win[r_d_win];

    logic [5:0]  w_pg_lg2;       // min(12, window): the span no burst may cross
    logic [2:0]  w_size;
    logic [1:0]  w_burst;
    logic [7:0]  w_len;
    logic [31:0] w_addr;
    logic [7:0]  w_lmask;        // the window's len_mask, cut to the protocol's
    assign w_lmask = w_w.len_mask & LEN_MASK;

    always_comb begin
        logic [2:0]  smax, wrapcap_lg2, wl_lg2;
        logic [31:0] bytes, off, aligned_off;
        logic [13:0] room_beats;

        w_pg_lg2 = (w_w.size_lg2 < 6'd12) ? w_w.size_lg2 : 6'd12;

        // size
        smax = w_w.size_max;
        if (smax > 3'(BUS_LG2))         smax = 3'(BUS_LG2);
        if ({3'd0, smax} > w_pg_lg2)    smax = w_pg_lg2[2:0];
        w_size = r_d_size;
        if (w_size > smax)              w_size = smax;
        if (w_size < w_w.size_min)      w_size = w_w.size_min;
        if (w_size > smax)              w_size = smax;  // size_min > size_max
        bytes = 32'd1 << w_size;

        // burst type
        unique case (r_d_burst)
            2'd0:    w_burst = BURST_FIXED;
            2'd2:    w_burst = BURST_WRAP;
            default: w_burst = BURST_INCR;
        endcase
        if (!w_w.burst_mask[w_burst]) begin
            if (w_w.burst_mask[1])      w_burst = BURST_INCR;
            else if (w_w.burst_mask[0]) w_burst = BURST_FIXED;
            else if (w_w.burst_mask[2]) w_burst = BURST_WRAP;
            else                        w_burst = BURST_INCR;
        end

        // length
        w_len = r_d_single ? 8'd0 : (r_d_len & w_lmask);
        wrapcap_lg2 = (w_lmask >= 8'd15) ? 3'd4 :
                      (w_lmask >=  8'd7) ? 3'd3 :
                      (w_lmask >=  8'd3) ? 3'd2 : 3'd1;
        wl_lg2 = 3'(r_d_wrapk) + 3'd1;
        if (wl_lg2 > wrapcap_lg2) wl_lg2 = wrapcap_lg2;
        if (w_burst == BURST_WRAP) begin
            if (w_lmask == 8'd0 || r_d_single ||
                (6'(wl_lg2) + 6'(w_size)) > w_pg_lg2) begin
                w_burst = BURST_INCR;
            end else begin
                w_len = 8'((9'd1 << wl_lg2) - 9'd1);
            end
        end
        if (w_burst == BURST_FIXED && w_len > 8'd15) w_len = w_len & 8'd15;

        // address
        off = r_d_off;
        if (w_w.size_lg2 < 6'd32) off = off & ((32'd1 << w_w.size_lg2) - 32'd1);
        if (w_burst == BURST_WRAP || !w_w.unaligned) off = off & ~(bytes - 32'd1);
        w_addr = (w_w.size_lg2 < 6'd32)
               ? ((w_w.base & ~((32'd1 << w_w.size_lg2) - 32'd1)) | off)
               : off;

        // INCR: stop at the page (or the window, if smaller)
        aligned_off = (w_addr & ~(bytes - 32'd1)) & ((32'd1 << w_pg_lg2) - 32'd1);
        room_beats  = 14'(((32'd1 << w_pg_lg2) - aligned_off) >> w_size);
        if (w_burst == BURST_INCR && ({6'd0, w_len} + 14'd1) > room_beats)
            w_len = 8'(room_beats - 14'd1);
    end

    logic r_o_valid;
    assign w_d_take = r_d_valid && (!r_o_valid || txn_ready);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_o_valid <= 1'b0;
        end else if (restart) begin
            r_o_valid <= 1'b0;
        end else begin
            if (w_d_take)       r_o_valid <= 1'b1;
            else if (txn_ready) r_o_valid <= 1'b0;
        end
    )

    always_ff @(posedge aclk) begin
        if (w_d_take) begin
            txn_addr      <= w_addr;
            txn_len       <= w_len;
            txn_size      <= w_size;
            txn_burst     <= w_burst;
            txn_id        <= r_d_id;
            txn_qos       <= cfg_qos_rand ? r_d_qos : 4'd0;
            txn_gap       <= r_d_gap;
            txn_tag       <= w_w.tag;
            txn_resp      <= w_w.resp;
            txn_strb_rand <= w_w.strb_rand;
            txn_sb        <= w_w.sb;
            txn_plg2      <= w_w.poison_lg2;
        end
    end

    assign txn_valid = r_o_valid;

endmodule : axi_stress_txn_gen
