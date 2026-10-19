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
// This exists so the AXI5-Lite BFMs have something to drive. Their transaction
// ID and optional signal groups (ID, USER, TRACE, POISON) were
// declaration-only: the framework unit tests compare field configs, and
// no DUT in the repo carried the ports, so nothing ever proved a BFM puts
// those values on a wire. A BFM-only test would only assert the BFM against
// its own beliefs.
//
// It is deliberately NOT in rtl/amba/axil5/ proper. It is not a reusable
// AXI5-Lite slave: the memory is a plain array and there is no error
// decoding. Do not instantiate it in a design.
//
// Signal set per IHI 0022 Issue L Table B2.2 (AXI5-Lite column): AWID/BID and
// ARID/RID are present (YS: mandatory on a Subordinate, which this is); USER,
// TRACE and POISON are optional (O). AxLOCK, AxMPAM, AxMECID, AxNSAID and
// xLOOP are NOT present (N) on AXI5-Lite, and exclusive accesses are not
// supported (B2.1.5), so this model has none of them and never answers EXOKAY.
//
// What it implements, and why each part is checkable:
//
//   ID     AWID -> BID and ARID -> RID, returned unmodified. This is the spec
//          behaviour (A5.1.1: the Manager requires BID and RID to be reflected
//          from AWID and ARID), so a test can send a known ID and require it
//          back.
//   TRACE  AWTRACE -> BTRACE, ARTRACE -> RTRACE, propagated with the
//          transaction. Same shape of check.
//   USER   AWUSER -> BUSER and ARUSER -> RUSER. User signals are by definition
//          implementation-defined; echoing is this DUT's contract, chosen
//          because it makes the value observable.
//   POISON WPOISON is stored alongside the data and returned as RPOISON on a
//          read of the same address, so poison survives a round trip.
//
// PROT (and WUSER, which has no response to ride back on) have no
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
//   ID_WIDTH         AWID/BID and ARID/RID width, 1..32 (a Subordinate must
//                    carry the ID, so 0 is not offered). Default 4.
//   USER_WIDTH       AxUSER/xUSER width. >=1.
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
    parameter int ID_WIDTH        = 4,
    parameter int USER_WIDTH      = 4,

    // Optional-group enables, same names and defaults as the production
    // AXI5-Lite modules. A disabled group is not carried in the payload
    // there, so its field reads zero; this model does the same, which is
    // what lets one testbench sweep configurations instead of only ever
    // exercising all-groups-on.
    parameter bit ENABLE_USER     = 1,
    parameter bit ENABLE_TRACE    = 1,
    parameter bit ENABLE_POISON   = 1,

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
    input  logic [ID_WIDTH-1:0]      s_axil_awid,
    input  logic [AW-1:0]            s_axil_awaddr,
    input  logic [2:0]               s_axil_awprot,
    input  logic [USER_WIDTH-1:0]    s_axil_awuser,
    input  logic                     s_axil_awtrace,
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
    output logic [ID_WIDTH-1:0]      s_axil_bid,
    output logic [1:0]               s_axil_bresp,
    output logic [USER_WIDTH-1:0]    s_axil_buser,
    output logic                     s_axil_btrace,
    output logic                     s_axil_bvalid,
    input  logic                     s_axil_bready,

    // ---- Read address channel (AR) -------------------------------------
    input  logic [ID_WIDTH-1:0]      s_axil_arid,
    input  logic [AW-1:0]            s_axil_araddr,
    input  logic [2:0]               s_axil_arprot,
    input  logic [USER_WIDTH-1:0]    s_axil_aruser,
    input  logic                     s_axil_artrace,
    input  logic                     s_axil_arvalid,
    output logic                     s_axil_arready,

    // ---- Read data channel (R) -----------------------------------------
    output logic [ID_WIDTH-1:0]      s_axil_rid,
    output logic [DW-1:0]            s_axil_rdata,
    output logic [1:0]               s_axil_rresp,
    output logic [USER_WIDTH-1:0]    s_axil_ruser,
    output logic                     s_axil_rtrace,
    output logic [POISON_WIDTH-1:0]  s_axil_rpoison,
    output logic                     s_axil_rvalid,
    input  logic                     s_axil_rready,

    // ---- Observation of qualifiers with no architectural effect --------
    // Last accepted AW / AR qualifiers. A testbench samples these to prove the
    // BFM drove the value; there is nothing in a Lite response for them to
    // come back in.
    output logic [2:0]               o_last_aw_prot,
    output logic [USER_WIDTH-1:0]    o_last_w_user,
    output logic [2:0]               o_last_ar_prot
);

    localparam logic [1:0] RESP_OKAY   = 2'b00;

    // ---- Storage --------------------------------------------------------
    // Plain arrays: this is test collateral, so a behavioural memory is the
    // point. A library block would use the SRAM wrappers.
    logic [DW-1:0]           r_mem    [MEM_DEPTH];
    logic [POISON_WIDTH-1:0] r_poison [MEM_DEPTH];

    // ---- AW holding register -------------------------------------------
    logic                    r_aw_full;
    logic [IDX_W-1:0]        r_aw_idx;
    logic [ID_WIDTH-1:0]     r_aw_id;
    logic [USER_WIDTH-1:0]   r_aw_user;
    logic                    r_aw_trace;

    // ---- W holding register ---------------------------------------------
    logic                    r_w_full;
    logic [DW-1:0]           r_w_data;
    logic [SW-1:0]           r_w_strb;
    logic [POISON_WIDTH-1:0] r_w_poison;

    // ---- B / R response registers ---------------------------------------
    logic                    r_b_valid;
    logic [ID_WIDTH-1:0]     r_b_id;
    logic [1:0]              r_b_resp;
    logic [USER_WIDTH-1:0]   r_b_user;
    logic                    r_b_trace;

    logic                    r_r_valid;
    logic [DW-1:0]           r_r_data;
    logic [ID_WIDTH-1:0]     r_r_id;
    logic [1:0]              r_r_resp;
    logic [USER_WIDTH-1:0]   r_r_user;
    logic                    r_r_trace;
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
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_full  <= 1'b0;
            r_aw_idx   <= '0;
            r_aw_id    <= '0;
            r_aw_user  <= '0;
            r_aw_trace <= 1'b0;
        end else begin
            if (w_aw_fire) begin
                r_aw_full  <= 1'b1;
                r_aw_idx   <= s_axil_awaddr[ADDR_LSB +: IDX_W];
                r_aw_id    <= s_axil_awid;
                r_aw_user  <= s_axil_awuser;
                r_aw_trace <= s_axil_awtrace;
            end else if (w_wr_commit) begin
                r_aw_full  <= 1'b0;
            end
        end
    )

    // ---- W capture -------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
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
        if (`RST_ASSERTED(aresetn)) begin
            r_b_valid <= 1'b0;
            r_b_id    <= '0;
            r_b_resp  <= RESP_OKAY;
            r_b_user  <= '0;
            r_b_trace <= 1'b0;
        end else begin
            if (w_wr_commit) begin
                r_mem[r_aw_idx]    <= w_wr_data;
                r_poison[r_aw_idx] <= r_w_poison;

                r_b_valid <= 1'b1;
                // No exclusive access on AXI5-Lite: every write answers OKAY.
                r_b_resp  <= RESP_OKAY;
                // Reflect the ID; echo the transaction's sideband.
                r_b_id    <= r_aw_id;
                r_b_user  <= r_aw_user;
                r_b_trace <= r_aw_trace;
            end else if (w_b_fire) begin
                r_b_valid <= 1'b0;
            end
        end
    )

    // ---- AR accept + R response ------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_r_valid  <= 1'b0;
            r_r_data   <= '0;
            r_r_id     <= '0;
            r_r_resp   <= RESP_OKAY;
            r_r_user   <= '0;
            r_r_trace  <= 1'b0;
            r_r_poison <= '0;
        end else begin
            if (w_ar_fire) begin
                r_r_valid  <= 1'b1;
                r_r_data   <= r_mem[w_ar_idx];
                r_r_poison <= r_poison[w_ar_idx];
                r_r_resp   <= RESP_OKAY;
                r_r_id     <= s_axil_arid;
                r_r_user   <= s_axil_aruser;
                r_r_trace  <= s_axil_artrace;
            end else if (w_r_fire) begin
                r_r_valid  <= 1'b0;
            end
        end
    )

    assign s_axil_bid     = r_b_id;
    assign s_axil_bresp   = r_b_resp;
    assign s_axil_buser = ENABLE_USER ? r_b_user : '0;
    assign s_axil_btrace = ENABLE_TRACE ? r_b_trace : 1'b0;
    assign s_axil_bvalid  = r_b_valid;

    assign s_axil_rid     = r_r_id;
    assign s_axil_rdata   = r_r_data;
    assign s_axil_rresp   = r_r_resp;
    assign s_axil_ruser = ENABLE_USER ? r_r_user : '0;
    assign s_axil_rtrace = ENABLE_TRACE ? r_r_trace : 1'b0;
    assign s_axil_rpoison = ENABLE_POISON ? r_r_poison : '0;
    assign s_axil_rvalid  = r_r_valid;

    // ---- Qualifier observation -------------------------------------------
    // Captured on acceptance, held until the next transaction of that
    // direction, so a testbench can sample after the response completes.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_last_aw_prot  <= '0;
            o_last_w_user   <= '0;
            o_last_ar_prot  <= '0;
        end else begin
            // A disabled group is not carried, so its tap stays at zero --
            // the same thing a caller sees from the production modules, whose
            // payload simply has no field for it.
            if (w_aw_fire) begin
                o_last_aw_prot  <= s_axil_awprot;
            end
            if (w_w_fire) begin
                o_last_w_user   <= ENABLE_USER ? s_axil_wuser : '0;
            end
            if (w_ar_fire) begin
                o_last_ar_prot  <= s_axil_arprot;
            end
        end
    )

endmodule : axil5_opt_slave
