// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_axi_burst_chopper
// Purpose: FSM-free AXI address-channel burst chopper. Takes one host AXI
//          address-channel command (AW or AR - the field set is identical) and
//          emits it as N sub-commands, each spanning at most AXI_BEATS_PER_BURST AXI
//          beats (= one DFI/DRAM burst). Sub-command addresses step by
//          AXI_BURST_BYTES so each lands on its own DRAM-burst boundary. The pumice
//          intakes require "one AXI sub-burst == one DFI burst"; this chopper is
//          what guarantees that framing on the request side.
//
//          FSM-free: there is no state enum. A single "active" bit plus a
//          remaining-beats counter and a running address drive everything. The
//          first sub-command of a new host command is presented combinationally
//          straight from the fub inputs (and the host command is accepted the
//          cycle that first sub launches, its fields latched); subsequent
//          sub-commands are presented from the latched copy while `fub_axready`
//          holds low to backpressure the next host command until the current one
//          fully drains.
//
//          Regular split: for the pumice-aligned case (host burst is a whole
//          multiple of AXI_BEATS_PER_BURST and CHUNK-aligned) every sub-command is
//          exactly AXI_BEATS_PER_BURST beats. A ragged final chunk is handled too (its
//          length is min(remaining, AXI_BEATS_PER_BURST)) so the module is robust to any
//          burst shape, though pumice never issues one.
//
//          Aggregation sideband: each sub-command carries m_ax_agg (=1 when its
//          host command splits into >1 sub) and m_ax_last (=1 on the final sub
//          of the host command). These ride with the command through the intake
//          into the CAM / AR-order FIFO so the return path can collapse the
//          per-sub B/RLAST into one host response using stored bits - no
//          separate snoop-and-count aggregator. A single-sub command has
//          agg=0, last=1.
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_axi_burst_chopper #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int STRB_BYTES     = 8,   // bytes per AXI beat (AXI_DATA_WIDTH/8)
    parameter int AXI_BEATS_PER_BURST    = 1,   // AXI beats per DFI burst (power of 2)
    // 1 = always DECLARE a full AXI_BEATS_PER_BURST sub-command, even when the host
    // burst leaves a short tail. The write path sets this: the splitter pads
    // the W stream out to the chunk with zero-strobe filler beats, so the
    // sub-command really is AXI_BEATS_PER_BURST long on the wire and the intake's
    // "one AXI burst == one DFI burst" contract holds for ANY host AxLEN.
    // Internal remaining-beat accounting still uses the REAL beat count, so
    // the address stepping and last-sub detection are unchanged.
    // Reads leave this 0: a short read needs no padding (the R framing
    // follows the AR), so the read side stays bit-identical.
    parameter int PAD_TO_CHUNK   = 0,
    // Derived
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int AXI_BURST_BYTES = AXI_BEATS_PER_BURST * STRB_BYTES
) (
    input  logic              aclk,
    input  logic              aresetn,

    // ---- host address channel in (AW or AR) -------------------------------
    input  logic [IW-1:0]     fub_axid,
    input  logic [AW-1:0]     fub_axaddr,
    input  logic [7:0]        fub_axlen,
    input  logic [2:0]        fub_axsize,
    input  logic [1:0]        fub_axburst,
    input  logic              fub_axlock,
    input  logic [3:0]        fub_axcache,
    input  logic [2:0]        fub_axprot,
    input  logic [3:0]        fub_axqos,
    input  logic [3:0]        fub_axregion,
    input  logic [UW-1:0]     fub_axuser,
    input  logic              fub_axvalid,
    output logic              fub_axready,

    // ---- sub-command address channel out (to intake) ----------------------
    output logic [IW-1:0]     m_axid,
    output logic [AW-1:0]     m_axaddr,
    output logic [7:0]        m_axlen,
    output logic [2:0]        m_axsize,
    output logic [1:0]        m_axburst,
    output logic              m_axlock,
    output logic [3:0]        m_axcache,
    output logic [2:0]        m_axprot,
    output logic [3:0]        m_axqos,
    output logic [3:0]        m_axregion,
    output logic [UW-1:0]     m_axuser,
    output logic              m_axvalid,
    input  logic              m_axready,

    // ---- aggregation sideband (aligned with m_ax*) ------------------------
    output logic              m_ax_agg,   // this sub is part of a split (>1 sub)
    output logic              m_ax_last   // this sub is the final one of the cmd
);

    initial begin
        assert (AXI_BEATS_PER_BURST >= 1 && (AXI_BEATS_PER_BURST == (1 << $clog2(AXI_BEATS_PER_BURST)))) else
            $fatal(1, "pumice_axi_burst_chopper: AXI_BEATS_PER_BURST must be a power of 2");
    end

    // ---- latched host command (valid only while r_active) ------------------
    logic           r_active;      // emitting sub-commands of a latched command
    logic [8:0]     r_rem;         // beats remaining to emit (incl. current sub)
    logic [AW-1:0]  r_addr;        // address of the current sub-command
    logic [IW-1:0]  r_id;
    logic [2:0]     r_size;
    logic [1:0]     r_burst;
    logic           r_lock;
    logic [3:0]     r_cache;
    logic [2:0]     r_prot;
    logic [3:0]     r_qos;
    logic [3:0]     r_region;
    logic [UW-1:0]  r_user;

    // ---- present the current sub-command (first from fub, rest from latch) --
    logic           w_first;
    logic [8:0]     w_total;       // host burst beat count (axlen+1)
    logic [8:0]     w_rem;         // beats remaining incl. current sub
    logic [8:0]     w_this;        // beats in the current sub-command
    logic [AW-1:0]  w_addr;
    logic           w_last_sub;    // current sub is the final one of the command
    logic           w_sub_acc;

    assign w_first = !r_active;
    assign w_total = {1'b0, fub_axlen} + 9'd1;
    assign w_rem   = w_first ? w_total : r_rem;
    assign w_this  = (w_rem > 9'(AXI_BEATS_PER_BURST)) ? 9'(AXI_BEATS_PER_BURST) : w_rem;
    assign w_addr  = w_first ? fub_axaddr : r_addr;
    assign w_last_sub = (w_rem <= 9'(AXI_BEATS_PER_BURST));

    assign m_axaddr   = w_addr;
    assign m_axlen    = (PAD_TO_CHUNK != 0) ? 8'(AXI_BEATS_PER_BURST - 1)
                                            : 8'(w_this - 9'd1);
    assign m_axid     = w_first ? fub_axid     : r_id;
    assign m_axsize   = w_first ? fub_axsize   : r_size;
    assign m_axburst  = w_first ? fub_axburst  : r_burst;
    assign m_axlock   = w_first ? fub_axlock   : r_lock;
    assign m_axcache  = w_first ? fub_axcache  : r_cache;
    assign m_axprot   = w_first ? fub_axprot   : r_prot;
    assign m_axqos    = w_first ? fub_axqos    : r_qos;
    assign m_axregion = w_first ? fub_axregion : r_region;
    assign m_axuser   = w_first ? fub_axuser   : r_user;

    // A new command's first sub tracks fub_axvalid; continuation subs are always
    // valid (work is latched).
    assign m_axvalid   = w_first ? fub_axvalid : 1'b1;

    // Aggregation sideband: agg=1 when the host command has >1 sub (on the first
    // sub that's total>CHUNK; on continuation subs it is by definition a split).
    // last=1 on the final sub. Single-sub command => agg=0, last=1.
    assign m_ax_agg    = w_first ? (w_total > 9'(AXI_BEATS_PER_BURST)) : 1'b1;
    assign m_ax_last   = w_last_sub;
    // Accept the host command as its first sub launches; hold ready low while a
    // command is still draining so the next one waits.
    assign fub_axready = w_first && m_axready;

    assign w_sub_acc = m_axvalid && m_axready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_active <= 1'b0;
            r_rem    <= 9'd0;
            r_addr   <= '0;
            r_id     <= '0; r_size <= '0; r_burst <= '0; r_lock <= '0;
            r_cache  <= '0; r_prot <= '0; r_qos <= '0; r_region <= '0; r_user <= '0;
        end else if (w_sub_acc) begin
            if (w_last_sub) begin
                // Final sub of this command accepted -> ready for the next.
                r_active <= 1'b0;
            end else begin
                // More subs to come: advance address / remaining, latch fields
                // (latch matters only on the transition out of the first sub).
                r_active <= 1'b1;
                r_rem    <= w_rem - w_this;
                r_addr   <= w_addr + AW'(AXI_BURST_BYTES);
                if (w_first) begin
                    r_id     <= fub_axid;
                    r_size   <= fub_axsize;
                    r_burst  <= fub_axburst;
                    r_lock   <= fub_axlock;
                    r_cache  <= fub_axcache;
                    r_prot   <= fub_axprot;
                    r_qos    <= fub_axqos;
                    r_region <= fub_axregion;
                    r_user   <= fub_axuser;
                end
            end
        end
    )

endmodule : pumice_axi_burst_chopper
