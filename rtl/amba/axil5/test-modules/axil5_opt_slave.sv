// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_opt_slave
// Purpose: AXI5-Lite slave carrying every optional signal group, for DV
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-08-28
//
// ---------------------------------------------------------------------------
// TEST COLLATERAL, NOT A LIBRARY BLOCK.
//
// This exists so the AXI5-Lite BFMs have something to drive. Their optional
// signal groups (USER, TRACE, LOOP, MPAM, MECID, NSAID, POISON, exclusive)
// were declaration-only: the framework unit tests compare field configs, and
// no DUT in the repo carried the ports, so nothing ever proved a BFM puts
// those values on a wire. A BFM-only test would only assert the BFM against
// its own beliefs.
//
// It is deliberately NOT in rtl/amba/axil5/ proper. It is not a reusable
// AXI5-Lite slave: the memory is a plain array, there is no error decoding,
// and the exclusive-access support is a response code rather than a monitor.
// Do not instantiate it in a design.
//
// What it implements, and why each part is checkable:
//
//   LOOP   AWLOOP -> BLOOP and ARLOOP -> RLOOP, returned unmodified. This is
//          the spec behaviour (a completer echoes loopback IDs on the matching
//          response), so a test can write a known value and require it back.
//   TRACE  AWTRACE -> BTRACE, ARTRACE -> RTRACE, propagated with the
//          transaction. Same shape of check.
//   USER   AWUSER -> BUSER and ARUSER -> RUSER. User signals are by definition
//          implementation-defined; echoing is this DUT's contract, chosen
//          because it makes the value observable.
//   POISON WPOISON is stored alongside the data and returned as RPOISON on a
//          read of the same address, so poison survives a round trip.
//   LOCK   An exclusive access (AxLOCK=1) answers EXOKAY instead of OKAY.
//          That is the one qualifier whose effect is visible in a field the
//          BFM already checks, which is why it is worth carrying.
//
// The remaining address qualifiers -- PROT, MPAM, MECID, NSAID -- have no
// architectural side effect a Lite slave can express, so they are captured
// into `o_last_*` observation ports instead. A testbench samples those to
// prove the BFM actually drove the value, which is the whole question. They
// are outputs rather than readable registers so the check needs no second
// transaction to interfere with the one under test.
//
// Parameters:
//   AXIL_ADDR_WIDTH  Address width. Range 12..64, default 32.
//   AXIL_DATA_WIDTH  Data width, power of 2. Range 32..512, default 32.
//   MEM_DEPTH        Words of storage, power of 2. Default 256.
//   USER_WIDTH       AxUSER/xUSER width. >=1.
//   LOOP_WIDTH       AxLOOP/xLOOP width. >=1.
//   MPAM_WIDTH       AxMPAM width. >=1.
//   MECID_WIDTH      AxMECID width. >=1.
//   NSAID_WIDTH      AxNSAID width. >=1.
//
// Notes:
//   - POISON_WIDTH is derived, not a parameter: AXI defines one poison bit per
//     64 data bits, and a narrow bus still carries one. Deriving it keeps the
//     RTL and the BFM (which applies the same rule) from disagreeing.
//   - No FSM. AW/W/AR are captured into single-entry holding registers and the
//     responses are produced combinationally from them, so the data path has
//     no state machine to get out of step with the handshakes.
// ---------------------------------------------------------------------------

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil5_opt_slave
#(
    parameter int AXIL_ADDR_WIDTH = 32,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int MEM_DEPTH       = 256,
    parameter int USER_WIDTH      = 4,
    parameter int LOOP_WIDTH      = 3,
    parameter int MPAM_WIDTH      = 11,
    parameter int MECID_WIDTH     = 16,
    parameter int NSAID_WIDTH     = 4,

    // Optional-group enables, same names and defaults as the production
    // AXI5-Lite modules. A disabled group is not carried in the payload
    // there, so its field reads zero; this model does the same, which is
    // what lets one testbench sweep configurations instead of only ever
    // exercising all-groups-on.
    parameter bit ENABLE_USER     = 1,
    parameter bit ENABLE_TRACE    = 1,
    parameter bit ENABLE_LOOP     = 1,
    parameter bit ENABLE_MPAM     = 1,
    parameter bit ENABLE_MECID    = 1,
    parameter bit ENABLE_NSAID    = 1,
    parameter bit ENABLE_POISON   = 1,
    parameter bit ENABLE_LOCK     = 1,

    // Derived. Do not override.
    parameter int AW           = AXIL_ADDR_WIDTH,
    parameter int DW           = AXIL_DATA_WIDTH,
    parameter int SW           = DW/8,
    parameter int POISON_WIDTH = (DW/64) > 0 ? (DW/64) : 1,
    parameter int IDX_W        = $clog2(MEM_DEPTH),
    parameter int ADDR_LSB     = $clog2(SW)
)
(
    // Global clock and reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // ---- Write address channel (AW) ------------------------------------
    input  logic [AW-1:0]            s_axil_awaddr,
    input  logic [2:0]               s_axil_awprot,
    input  logic                     s_axil_awlock,
    input  logic [USER_WIDTH-1:0]    s_axil_awuser,
    input  logic                     s_axil_awtrace,
    input  logic [LOOP_WIDTH-1:0]    s_axil_awloop,
    input  logic [MPAM_WIDTH-1:0]    s_axil_awmpam,
    input  logic [MECID_WIDTH-1:0]   s_axil_awmecid,
    input  logic [NSAID_WIDTH-1:0]   s_axil_awnsaid,
    input  logic                     s_axil_awvalid,
    output logic                     s_axil_awready,

    // ---- Write data channel (W) ----------------------------------------
    input  logic [DW-1:0]            s_axil_wdata,
    input  logic [SW-1:0]            s_axil_wstrb,
    input  logic [USER_WIDTH-1:0]    s_axil_wuser,
    input  logic [POISON_WIDTH-1:0]  s_axil_wpoison,
    input  logic                     s_axil_wvalid,
    output logic                     s_axil_wready,

    // ---- Write response channel (B) ------------------------------------
    output logic [1:0]               s_axil_bresp,
    output logic [USER_WIDTH-1:0]    s_axil_buser,
    output logic                     s_axil_btrace,
    output logic [LOOP_WIDTH-1:0]    s_axil_bloop,
    output logic                     s_axil_bvalid,
    input  logic                     s_axil_bready,

    // ---- Read address channel (AR) -------------------------------------
    input  logic [AW-1:0]            s_axil_araddr,
    input  logic [2:0]               s_axil_arprot,
    input  logic                     s_axil_arlock,
    input  logic [USER_WIDTH-1:0]    s_axil_aruser,
    input  logic                     s_axil_artrace,
    input  logic [LOOP_WIDTH-1:0]    s_axil_arloop,
    input  logic [MPAM_WIDTH-1:0]    s_axil_armpam,
    input  logic [MECID_WIDTH-1:0]   s_axil_armecid,
    input  logic [NSAID_WIDTH-1:0]   s_axil_arnsaid,
    input  logic                     s_axil_arvalid,
    output logic                     s_axil_arready,

    // ---- Read data channel (R) -----------------------------------------
    output logic [DW-1:0]            s_axil_rdata,
    output logic [1:0]               s_axil_rresp,
    output logic [USER_WIDTH-1:0]    s_axil_ruser,
    output logic                     s_axil_rtrace,
    output logic [LOOP_WIDTH-1:0]    s_axil_rloop,
    output logic [POISON_WIDTH-1:0]  s_axil_rpoison,
    output logic                     s_axil_rvalid,
    input  logic                     s_axil_rready,

    // ---- Observation of qualifiers with no architectural effect --------
    // Last accepted AW / AR qualifiers. A testbench samples these to prove the
    // BFM drove the value; there is nothing in a Lite response for them to
    // come back in.
    output logic [2:0]               o_last_aw_prot,
    output logic [MPAM_WIDTH-1:0]    o_last_aw_mpam,
    output logic [MECID_WIDTH-1:0]   o_last_aw_mecid,
    output logic [NSAID_WIDTH-1:0]   o_last_aw_nsaid,
    output logic [USER_WIDTH-1:0]    o_last_w_user,
    output logic [2:0]               o_last_ar_prot,
    output logic [MPAM_WIDTH-1:0]    o_last_ar_mpam,
    output logic [MECID_WIDTH-1:0]   o_last_ar_mecid,
    output logic [NSAID_WIDTH-1:0]   o_last_ar_nsaid
);

    localparam logic [1:0] RESP_OKAY   = 2'b00;
    localparam logic [1:0] RESP_EXOKAY = 2'b01;

    // ---- Storage --------------------------------------------------------
    // Plain arrays: this is test collateral, so a behavioural memory is the
    // point. A library block would use the SRAM wrappers.
    logic [DW-1:0]           r_mem    [0:MEM_DEPTH-1];
    logic [POISON_WIDTH-1:0] r_poison [0:MEM_DEPTH-1];

    // ---- AW holding register -------------------------------------------
    logic                    r_aw_full;
    logic [IDX_W-1:0]        r_aw_idx;
    logic                    r_aw_lock;
    logic [USER_WIDTH-1:0]   r_aw_user;
    logic                    r_aw_trace;
    logic [LOOP_WIDTH-1:0]   r_aw_loop;

    // ---- W holding register ---------------------------------------------
    logic                    r_w_full;
    logic [DW-1:0]           r_w_data;
    logic [SW-1:0]           r_w_strb;
    logic [POISON_WIDTH-1:0] r_w_poison;

    // ---- B / R response registers ---------------------------------------
    logic                    r_b_valid;
    logic [1:0]              r_b_resp;
    logic [USER_WIDTH-1:0]   r_b_user;
    logic                    r_b_trace;
    logic [LOOP_WIDTH-1:0]   r_b_loop;

    logic                    r_r_valid;
    logic [DW-1:0]           r_r_data;
    logic [1:0]              r_r_resp;
    logic [USER_WIDTH-1:0]   r_r_user;
    logic                    r_r_trace;
    logic [LOOP_WIDTH-1:0]   r_r_loop;
    logic [POISON_WIDTH-1:0] r_r_poison;

    // ---- Handshakes ------------------------------------------------------
    // ready is driven from register occupancy only, never from the matching
    // valid, so there is no combinational path from a master's valid back to
    // its ready.
    assign s_axil_awready = !r_aw_full;
    assign s_axil_wready  = !r_w_full;
    assign s_axil_arready = !r_r_valid;

    logic w_aw_fire, w_w_fire, w_ar_fire, w_wr_commit, w_b_fire, w_r_fire;
    assign w_aw_fire   = s_axil_awvalid && s_axil_awready;
    assign w_w_fire    = s_axil_wvalid  && s_axil_wready;
    assign w_ar_fire   = s_axil_arvalid && s_axil_arready;
    assign w_b_fire    = r_b_valid      && s_axil_bready;
    assign w_r_fire    = r_r_valid      && s_axil_rready;
    // A write commits once both halves are held and the B slot is free.
    assign w_wr_commit = r_aw_full && r_w_full && (!r_b_valid || w_b_fire);

    // Word index of the address presented this cycle / held.
    logic [IDX_W-1:0] w_ar_idx;
    assign w_ar_idx = s_axil_araddr[ADDR_LSB +: IDX_W];

    // Byte-enable merge for the committing write.
    logic [DW-1:0] w_wr_data;
    always_comb begin
        w_wr_data = r_mem[r_aw_idx];
        for (int b = 0; b < SW; b++) begin
            if (r_w_strb[b]) w_wr_data[b*8 +: 8] = r_w_data[b*8 +: 8];
        end
    end

    // ---- AW capture ------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_aw_full  <= 1'b0;
            r_aw_idx   <= '0;
            r_aw_lock  <= 1'b0;
            r_aw_user  <= '0;
            r_aw_trace <= 1'b0;
            r_aw_loop  <= '0;
        end else begin
            if (w_aw_fire) begin
                r_aw_full  <= 1'b1;
                r_aw_idx   <= s_axil_awaddr[ADDR_LSB +: IDX_W];
                r_aw_lock  <= s_axil_awlock;
                r_aw_user  <= s_axil_awuser;
                r_aw_trace <= s_axil_awtrace;
                r_aw_loop  <= s_axil_awloop;
            end else if (w_wr_commit) begin
                r_aw_full  <= 1'b0;
            end
        end
    )

    // ---- W capture -------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_w_full   <= 1'b0;
            r_w_data   <= '0;
            r_w_strb   <= '0;
            r_w_poison <= '0;
        end else begin
            if (w_w_fire) begin
                r_w_full   <= 1'b1;
                r_w_data   <= s_axil_wdata;
                r_w_strb   <= s_axil_wstrb;
                r_w_poison <= s_axil_wpoison;
            end else if (w_wr_commit) begin
                r_w_full   <= 1'b0;
            end
        end
    )

    // ---- Memory update + B response --------------------------------------
    // POISON is stored with the word, so a later read of the same address
    // returns it: the round trip is the property under test.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_b_valid <= 1'b0;
            r_b_resp  <= RESP_OKAY;
            r_b_user  <= '0;
            r_b_trace <= 1'b0;
            r_b_loop  <= '0;
        end else begin
            if (w_wr_commit) begin
                r_mem[r_aw_idx]    <= w_wr_data;
                r_poison[r_aw_idx] <= r_w_poison;

                r_b_valid <= 1'b1;
                // Exclusive access answers EXOKAY; a normal write answers OKAY.
                r_b_resp  <= (ENABLE_LOCK && r_aw_lock) ? RESP_EXOKAY : RESP_OKAY;
                // Echo the transaction's sideband back on its response.
                r_b_user  <= r_aw_user;
                r_b_trace <= r_aw_trace;
                r_b_loop  <= r_aw_loop;
            end else if (w_b_fire) begin
                r_b_valid <= 1'b0;
            end
        end
    )

    // ---- AR accept + R response ------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            r_r_valid  <= 1'b0;
            r_r_data   <= '0;
            r_r_resp   <= RESP_OKAY;
            r_r_user   <= '0;
            r_r_trace  <= 1'b0;
            r_r_loop   <= '0;
            r_r_poison <= '0;
        end else begin
            if (w_ar_fire) begin
                r_r_valid  <= 1'b1;
                r_r_data   <= r_mem[w_ar_idx];
                r_r_poison <= r_poison[w_ar_idx];
                r_r_resp   <= (ENABLE_LOCK && s_axil_arlock)
                              ? RESP_EXOKAY : RESP_OKAY;
                r_r_user   <= s_axil_aruser;
                r_r_trace  <= s_axil_artrace;
                r_r_loop   <= s_axil_arloop;
            end else if (w_r_fire) begin
                r_r_valid  <= 1'b0;
            end
        end
    )

    assign s_axil_bresp   = r_b_resp;
    assign s_axil_buser = ENABLE_USER ? r_b_user : '0;
    assign s_axil_btrace = ENABLE_TRACE ? r_b_trace : 1'b0;
    assign s_axil_bloop = ENABLE_LOOP ? r_b_loop : '0;
    assign s_axil_bvalid  = r_b_valid;

    assign s_axil_rdata   = r_r_data;
    assign s_axil_rresp   = r_r_resp;
    assign s_axil_ruser = ENABLE_USER ? r_r_user : '0;
    assign s_axil_rtrace = ENABLE_TRACE ? r_r_trace : 1'b0;
    assign s_axil_rloop = ENABLE_LOOP ? r_r_loop : '0;
    assign s_axil_rpoison = ENABLE_POISON ? r_r_poison : '0;
    assign s_axil_rvalid  = r_r_valid;

    // ---- Qualifier observation -------------------------------------------
    // Captured on acceptance, held until the next transaction of that
    // direction, so a testbench can sample after the response completes.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn) begin
            o_last_aw_prot  <= '0;
            o_last_aw_mpam  <= '0;
            o_last_aw_mecid <= '0;
            o_last_aw_nsaid <= '0;
            o_last_w_user   <= '0;
            o_last_ar_prot  <= '0;
            o_last_ar_mpam  <= '0;
            o_last_ar_mecid <= '0;
            o_last_ar_nsaid <= '0;
        end else begin
            // A disabled group is not carried, so its tap stays at zero --
            // the same thing a caller sees from the production modules, whose
            // payload simply has no field for it.
            if (w_aw_fire) begin
                o_last_aw_prot  <= s_axil_awprot;
                o_last_aw_mpam  <= ENABLE_MPAM  ? s_axil_awmpam  : '0;
                o_last_aw_mecid <= ENABLE_MECID ? s_axil_awmecid : '0;
                o_last_aw_nsaid <= ENABLE_NSAID ? s_axil_awnsaid : '0;
            end
            if (w_w_fire) begin
                o_last_w_user   <= ENABLE_USER ? s_axil_wuser : '0;
            end
            if (w_ar_fire) begin
                o_last_ar_prot  <= s_axil_arprot;
                o_last_ar_mpam  <= ENABLE_MPAM  ? s_axil_armpam  : '0;
                o_last_ar_mecid <= ENABLE_MECID ? s_axil_armecid : '0;
                o_last_ar_nsaid <= ENABLE_NSAID ? s_axil_arnsaid : '0;
            end
        end
    )

endmodule : axil5_opt_slave
