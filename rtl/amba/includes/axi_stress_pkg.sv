// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Package: axi_stress_pkg
// Purpose: Shared definitions of the bus-stress traffic blocks
//          (axi_stress_mst_{rd,wr}, axi_stress_slv_{rd,wr}): the data
//          function, the AXI beat-address step, the burst legality rules, the
//          error codes, and the cfg / status structures.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// The data contract
//
// Every byte the stress blocks move is a pure function of its FABRIC byte
// address, the tag of the slave that owns the address, and the direction:
//
//     word(A, tag, dir) = f_word({A[31:2], 2'b00}, seed, tag, dir)
//     byte(A)           = word(A)[8*A[1:0] +: 8]
//
// A master writes word(A, tag, WR) and a slave checks it; a slave returns
// word(A, tag, RD) and a master checks it. Nothing is stored, so:
//   - any number of masters can share any slave without a memory model;
//   - responses may come back in any order or interleaved, because each beat
//     is checked against its own address, never against a running stream;
//   - width conversion, burst splitting and protocol conversion in between
//     cannot hide an error: a byte lands on the lane its address names, at
//     every width, so a converter that moves a byte to the wrong lane or the
//     wrong beat changes the data the far end computes for it.
//
// f_word is xorshift32 applied twice around a key XOR. xorshift32 is a
// bijection on 32 bits, so two different word addresses never produce the
// same word under one key: an address error is always a data error. The tag
// is folded into the key, so a request the fabric delivers to the wrong slave
// returns data that differs by a key-dependent constant and fails at the
// master even if the wrong slave's own window check were missing. Every
// output bit is an XOR of address and key bits only, which synthesizes to two
// LUT6 levels -- no multiplier, so the check is free at bus rate.
//==============================================================================

`timescale 1ns / 1ps

package axi_stress_pkg;

    // ---- AXI encodings ------------------------------------------------------
    localparam logic [1:0] BURST_FIXED = 2'b00;
    localparam logic [1:0] BURST_INCR  = 2'b01;
    localparam logic [1:0] BURST_WRAP  = 2'b10;

    localparam logic [1:0] RESP_OKAY   = 2'b00;
    localparam logic [1:0] RESP_EXOKAY = 2'b01;
    localparam logic [1:0] RESP_SLVERR = 2'b10;
    localparam logic [1:0] RESP_DECERR = 2'b11;

    // ---- Error codes: one bit each in a block's 16-bit err_mask (all 16 used) 
    // Master side
    localparam int ERR_RD_STRAY = 0;   // R beat on an ID with nothing outstanding
    localparam int ERR_RD_LAST  = 1;   // RLAST on the wrong beat
    localparam int ERR_RD_RESP  = 2;   // RRESP differs from the window's
    localparam int ERR_RD_DATA  = 3;   // an active byte lane is wrong
    localparam int ERR_WR_STRAY = 4;   // B on an ID with nothing outstanding
    localparam int ERR_WR_RESP  = 5;   // BRESP differs from the window's
    localparam int ERR_WR_EARLY = 6;   // B before the burst's last W left
    localparam int ERR_HANG     = 7;   // outstanding work, no response for 2^n cycles
    // Slave side
    localparam int ERR_S_ADDR   = 8;   // request outside this slave's window
    localparam int ERR_S_PROTO  = 9;   // illegal burst (size, WRAP shape, 4 KB)
    localparam int ERR_S_WDATA  = 10;  // a strobed byte is wrong
    localparam int ERR_S_WSTRB  = 11;  // a strobe outside the beat's byte lanes
    localparam int ERR_S_WLAST  = 12;  // WLAST on the wrong beat
    localparam int ERR_S_WID    = 13;  // AXI3: WID is not its burst's AWID
    localparam int ERR_S_SB     = 14;  // AXI5: request sideband or WPOISON wrong
    // Master side, either direction
    localparam int ERR_M_SB     = 15;  // AXI5: response sideband or RPOISON wrong

    // ---- Configuration and status -------------------------------------------
    // One target window of a master. Windows are size-aligned power-of-two
    // ranges; the host builds them from the fabric's address map. resp is what
    // every access to the window must answer (OKAY on a slave, SLVERR on a
    // slave's error range, DECERR on a hole), and the burst-shape fields say
    // what the path to that slave can legally carry (AXI3: len_mask 15;
    // AXI4-Lite / APB: len_mask 0 and one size).
    typedef struct packed {
        logic [31:0] base;
        logic [5:0]  size_lg2;     // window = 2^size_lg2 bytes, >= the bus width
        logic [7:0]  tag;          // the owning slave's tag
        logic [1:0]  resp;         // expected response
        logic [7:0]  len_mask;     // AxLEN = random & len_mask
        logic [2:0]  size_min;
        logic [2:0]  size_max;     // clamped to the bus width
        logic [2:0]  burst_mask;   // [0] FIXED  [1] INCR  [2] WRAP
        logic        unaligned;    // INCR/FIXED may start off the size grid
        logic        strb_rand;    // writes clear random strobes
        logic        rd_en;
        logic        wr_en;
        logic        sb;           // AXI5: responses echo the request sideband
        logic [3:0]  poison_lg2;   // AXI5: beats poisoned 1 in 2^n; 0 = never
    } stress_win_t;

    // One direction of a master.
    typedef struct packed {
        logic        enable;       // this direction runs on GO
        logic [31:0] txn_count;    // bursts per run; 0 = until STOP
        logic [31:0] seed;         // transaction PRNG; 0 = built-in seed
        logic [15:0] id_base;      // AxID = id_base ^ (random & id_mask)
        logic [15:0] id_mask;
        logic [7:0]  gap_mask;     // idle cycles after a burst = random & gap_mask
        logic [3:0]  resp_throttle;// RREADY/BREADY low with probability n/16
        logic [3:0]  data_throttle;// writes: a WVALID bubble with probability n/16
        logic [7:0]  max_out;      // bursts in flight; 0 = as built
        logic [4:0]  timeout_lg2;  // HANG after 2^n silent cycles; 0 = off
        logic        qos_rand;     // AxQOS random (else 0)
    } stress_mdir_cfg_t;

    typedef struct packed {
        logic        busy;
        logic        done;         // run complete: budget issued, all retired
        logic [7:0]  runs;         // GOs taken (wraps): proves this block saw the run
        logic [31:0] issued;       // bursts issued this run
        logic [31:0] completed;    // bursts retired (last R / B checked)
        logic [31:0] beats;        // R or W beats moved
        logic [15:0] err_mask;     // sticky, one bit per ERR_* code
        logic [15:0] err_cnt;      // saturating
        logic        fe_valid;     // first error, frozen until the next GO
        logic [3:0]  fe_kind;
        logic [15:0] fe_id;
        logic [31:0] fe_addr;
        logic [31:0] fe_exp;
        logic [31:0] fe_act;
        logic [15:0] lat_max;      // cycles, issue to retire
        logic [31:0] lat_sum;      // saturating; / completed = mean
        logic [7:0]  out_now;
        logic [7:0]  out_max;
    } stress_mdir_sts_t;

    // One direction of a slave.
    typedef struct packed {
        logic [31:0] base;         // the slave's fabric window
        logic [5:0]  size_lg2;
        logic        offset_mode;  // the port carries a window offset (APB)
        logic [7:0]  tag;
        logic        err_en;       // (A & err_mask) == err_base answers SLVERR
        logic [31:0] err_base;
        logic [31:0] err_mask;
        logic        inorder;      // complete in request order across IDs
        logic        interleave;   // R: switch bursts between beats (rd only)
        logic [7:0]  lat_min;      // cycles before a request may answer
        logic [7:0]  lat_mask;     //   + random & lat_mask
        logic [3:0]  req_throttle; // AxREADY low with probability n/16
        logic [3:0]  data_throttle;// WREADY low / an R bubble, n/16
        logic [7:0]  max_out;      // requests held; 0 = as built
        logic [31:0] seed;
        logic [7:0]  sb_src;       // AXI5: masters (by ID prefix) whose requests carry sideband
        logic [3:0]  poison_lg2;   // AXI5: as stress_win_t.poison_lg2, for this slave
    } stress_sdir_cfg_t;

    typedef struct packed {
        logic [7:0]  runs;         // clears taken (wraps)
        logic [31:0] bursts;
        logic [31:0] beats;
        logic [15:0] err_mask;
        logic [15:0] err_cnt;
        logic        fe_valid;
        logic [3:0]  fe_kind;
        logic [15:0] fe_id;
        logic [31:0] fe_addr;
        logic [31:0] fe_exp;
        logic [31:0] fe_act;
        logic [7:0]  out_now;
        logic [7:0]  out_max;
    } stress_sdir_sts_t;

    // ---- Functions ----------------------------------------------------------

    // xorshift32 (13, 17, 5): full period over the nonzero states, and the
    // mixing step of f_word.
    function automatic logic [31:0] f_xs32(input logic [31:0] v);
        logic [31:0] x;
        x = v ^ (v << 13);
        x = x ^ (x >> 17);
        x = x ^ (x << 5);
        return x;
    endfunction

    // The data word at a 4-byte-aligned fabric address. dir: 0 write, 1 read.
    function automatic logic [31:0] f_word(input logic [31:0] waddr,
                                           input logic [31:0] seed,
                                           input logic [7:0]  tag,
                                           input logic        dir);
        logic [31:0] k;
        k = seed ^ {tag, ~tag, tag, ~tag} ^ (dir ? 32'h5A5A_A5A5 : 32'h0);
        return f_xs32(f_xs32({waddr[31:2], 2'b00} ^ k) ^ {k[15:0], k[31:16]});
    endfunction

    // AXI5 sideband layout. A shell packs the request fields its port carries
    // into one 32-bit word, and its responses into one 8-bit word, at these
    // fixed positions; SB_MASK / RSB_MASK say which bits it carries.
    localparam logic [31:0] SB_M_NSAID  = 32'h0000_000F;  // AxNSAID [3:0]
    localparam logic [31:0] SB_M_TRACE  = 32'h0000_0010;  // AxTRACE [4]
    localparam logic [31:0] SB_M_MPAM   = 32'h0000_FFE0;  // AxMPAM  [15:5]
    localparam logic [31:0] SB_M_MECID  = 32'hFFFF_0000;  // AxMECID [31:16]
    localparam logic [7:0]  RSB_M_TRACE = 8'h01;          // BTRACE / RTRACE [0]

    // AXI5 sideband: every sideband field a request carries (NSAID, TRACE,
    // MPAM, MECID, packed by the shell) is f_sb(start address) & SB_MASK.
    // Both ends compute it, so like the data it needs no state, and a field
    // the fabric drops, swaps or routes to the wrong burst fails the check.
    // The response sideband is the slave's echo of what it received (f_rsb):
    // BTRACE / RTRACE repeat the request's TRACE, as AXI asks of a
    // trace-capable slave (and as the bridge asserts in simulation).
    function automatic logic [31:0] f_sb(input logic [31:0] a,
                                         input logic [31:0] seed);
        return f_xs32(f_xs32(a ^ seed ^ 32'hC6A4_A793) ^ 32'h5851_F42D);
    endfunction

    // The response sideband word that echoes a request sideband word.
    function automatic logic [7:0] f_rsb(input logic [31:0] sb);
        return {7'd0, sb[4]};             // RTRACE / BTRACE = AxTRACE
    endfunction

    // A beat at address `a` is poisoned with probability 1 in 2^lg2 (never
    // when lg2 is 0): a hash of the beat address both ends agree on.
    function automatic logic f_poison(input logic [31:0] a,
                                      input logic [31:0] seed,
                                      input logic [3:0]  lg2);
        logic [31:0] h;
        h = f_sb(a ^ 32'h9E37_79B9, seed);
        return (lg2 != 4'd0) && ((h & ((32'd1 << lg2) - 32'd1)) == 32'd0);
    endfunction

    // The address of the beat after `a` in a burst (AXI4 A3.4.1). WRAP needs
    // len in {1, 3, 7, 15}, so (len+1) << size is (len << size) | (bytes-1).
    function automatic logic [31:0] f_next_addr(input logic [31:0] a,
                                                input logic [2:0]  size,
                                                input logic [7:0]  len,
                                                input logic [1:0]  burst);
        logic [31:0] bytes, aligned, wmask;
        bytes   = 32'd1 << size;
        aligned = a & ~(bytes - 32'd1);
        wmask   = ({24'd0, len} << size) | (bytes - 32'd1);
        unique case (burst)
            BURST_FIXED: return a;
            BURST_WRAP:  return (a & ~wmask) | ((aligned + bytes) & wmask);
            default:     return aligned + bytes;
        endcase
    endfunction

    // A burst the AXI4 spec does not allow: a beat wider than the bus, a FIXED
    // or WRAP longer than 16, a WRAP of the wrong length or off the size grid,
    // an INCR across a 4 KB boundary, or the reserved burst type.
    function automatic logic f_burst_illegal(input logic [31:0] a,
                                             input logic [7:0]  len,
                                             input logic [2:0]  size,
                                             input logic [1:0]  burst,
                                             input logic [2:0]  bus_lg2);
        logic [12:0] start, span;
        start = {1'b0, a[11:0] & ~((12'd1 << size) - 12'd1)};
        span  = (13'({5'd0, len}) + 13'd1) << size;
        if (size > bus_lg2)                                        return 1'b1;
        if (burst == 2'b11)                                        return 1'b1;
        if (burst != BURST_INCR && len > 8'd15)                    return 1'b1;
        if (burst == BURST_WRAP &&
            !(len == 8'd1 || len == 8'd3 || len == 8'd7 || len == 8'd15)) return 1'b1;
        if (burst == BURST_WRAP && (a & ((32'd1 << size) - 32'd1)) != '0) return 1'b1;
        if (burst == BURST_INCR && (start + span) > 13'h1000)      return 1'b1;
        return 1'b0;
    endfunction

    // A READY (or a beat) held low with probability n/16: passes when the
    // random nibble r is at or above n, so n = 0 never throttles.
    function automatic logic f_pass(input logic [3:0] r, input logic [3:0] n);
        return r >= n;
    endfunction

endpackage : axi_stress_pkg
