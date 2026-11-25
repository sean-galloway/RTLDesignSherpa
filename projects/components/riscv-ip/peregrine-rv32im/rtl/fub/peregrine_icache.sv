// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_icache
// Purpose: peregrine's instruction cache (PRD §4.5, P9): direct-mapped,
//          read-only, blocking, one AXI4 read master.  This is the slot a
//          cache-ip I$ would replace; it carries no dirty state, no
//          coherence and no snoop port.
//
//          Fetch contract (the core's registered-read imem contract):
//          - fetch_addr_next is the PC after this edge; the data RAM is read
//            there, so fetch_rdata is the word at fetch_addr (the PC) in the
//            next cycle.
//          - stall is high whenever fetch_rdata is not the word at
//            fetch_addr: a miss, a refill, the replay cycle after a refill,
//            and an invalidate.  The core holds (its mem_wait), so
//            fetch_addr_next equals fetch_addr while stalled and the RAM
//            re-reads the same word.
//          - Hit test on the registered PC: valid bit (flops) and the tag
//            (distributed RAM, read asynchronously) of the PC's set.
//
//          Miss: one INCR burst of the whole line from its first beat
//          (LINE_BYTES / (AXI_DW/8) beats, no critical-word-first), each
//          beat written to the data RAM; the last beat writes the tag and
//          sets valid; one replay cycle re-reads the PC's word; then the
//          hit test passes.
//
//          Invalidate (fence.i, PRD P10): inv_req is a level; it is taken
//          when no refill is in flight.  That cycle clears every valid bit
//          and pulses inv_ack.  It wins over a miss starting the same cycle.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - SIZE_BYTES: capacity, a power of two (PRD P9: 4096).
//   - LINE_BYTES: line size, a power of two, >= AXI_DW/8 (PRD P9: 64).
//   - AXI_DW: fabric data width, 32 or 64.
//   - AXI_IW: AXI id width; the I$ always uses id 0.
//
// Notes:
//   - The data and tag RAMs have no reset; the valid bits do, and a hit
//     reads a tag only under its valid bit.
//   - An R beat with an error response is installed like any other; the
//     fabric's memory never returns one.  Fetch faults are out of scope
//     (peregrine has no instruction access fault, PRD P6).
//
// Related Modules:
//   - peregrine_top (fetch side, fence.i sequence)
//   - peregrine_axi4_arb (the refill master is its port 0)
//
// Test:
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_icache.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_icache #(
    parameter int SIZE_BYTES = 4096,
    parameter int LINE_BYTES = 64,
    parameter int AXI_DW     = 64,
    parameter int AXI_IW     = 4
) (
    input  logic                clk,
    input  logic                rst_n,
    // Fetch side
    input  logic [31:0]         fetch_addr,       // the PC (registered in the core)
    input  logic [31:0]         fetch_addr_next,  // the PC after this edge
    output logic [31:0]         fetch_rdata,
    output logic                stall,
    // Invalidate (fence.i)
    input  logic                inv_req,
    output logic                inv_ack,
    // AXI4 read master (refill)
    output logic [AXI_IW-1:0]   m_axi_arid,
    output logic [31:0]         m_axi_araddr,
    output logic [7:0]          m_axi_arlen,
    output logic [2:0]          m_axi_arsize,
    output logic [1:0]          m_axi_arburst,
    output logic                m_axi_arvalid,
    input  logic                m_axi_arready,
    input  logic [AXI_IW-1:0]   m_axi_rid,
    input  logic [AXI_DW-1:0]   m_axi_rdata,
    input  logic [1:0]          m_axi_rresp,
    input  logic                m_axi_rlast,
    input  logic                m_axi_rvalid,
    output logic                m_axi_rready
);

    localparam int BEAT_BYTES  = AXI_DW / 8;
    localparam int SETS        = SIZE_BYTES / LINE_BYTES;
    localparam int BEATS       = LINE_BYTES / BEAT_BYTES;
    localparam int OFF_W       = $clog2(LINE_BYTES);
    localparam int IDX_W       = $clog2(SETS);
    localparam int BEAT_W      = (BEATS > 1) ? $clog2(BEATS) : 1;
    localparam int BOFF_W      = $clog2(BEAT_BYTES);
    localparam int TAG_W       = 32 - OFF_W - IDX_W;
    localparam int RAM_AW      = IDX_W + BEAT_W;
    localparam int WORDS_BEAT  = BEAT_BYTES / 4;
    localparam int WSEL_W      = (WORDS_BEAT > 1) ? $clog2(WORDS_BEAT) : 1;
    localparam logic [1:0] BURST_INCR = 2'b01;

    initial begin
        if ((SIZE_BYTES & (SIZE_BYTES - 1)) != 0)
            $error("peregrine_icache: SIZE_BYTES must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0 || LINE_BYTES < BEAT_BYTES)
            $error("peregrine_icache: LINE_BYTES must be a power of two >= AXI_DW/8");
        if (AXI_DW != 32 && AXI_DW != 64)
            $error("peregrine_icache: AXI_DW must be 32 or 64");
    end

    typedef enum logic [2:0] {
        S_IDLE   = 3'd0,
        S_AR     = 3'd1,
        S_FILL   = 3'd2,
        S_REPLAY = 3'd3
    } state_e;

    state_e r_state, w_state_d;

    // -----------------------------------------------------------------
    // Storage
    // -----------------------------------------------------------------
    (* ram_style = "block" *)
    logic [AXI_DW-1:0] r_data [1 << RAM_AW];
    (* ram_style = "distributed" *)
    /* synthesis ramstyle = "MLAB" */
    logic [TAG_W-1:0]  r_tag  [SETS];
    logic [SETS-1:0]   r_valid;

    // -----------------------------------------------------------------
    // Hit test on the registered PC
    // -----------------------------------------------------------------
    logic [IDX_W-1:0] w_idx;
    logic [TAG_W-1:0] w_tag;
    logic             w_hit;

    assign w_idx = fetch_addr[OFF_W +: IDX_W];
    assign w_tag = fetch_addr[31 -: TAG_W];
    assign w_hit = (r_state == S_IDLE) & r_valid[w_idx] & (r_tag[w_idx] == w_tag);

    logic w_inv_take;
    logic w_miss_start;

    assign w_inv_take   = (r_state == S_IDLE) & inv_req;
    assign w_miss_start = (r_state == S_IDLE) & ~inv_req & ~w_hit;

    assign stall   = ~w_hit | w_inv_take;
    assign inv_ack = w_inv_take;

    // -----------------------------------------------------------------
    // Refill sequencer
    // -----------------------------------------------------------------
    logic [IDX_W-1:0]  r_fill_idx;
    logic [TAG_W-1:0]  r_fill_tag;
    logic [BEAT_W-1:0] r_fill_beat;
    logic              w_beat;

    assign w_beat = (r_state == S_FILL) & m_axi_rvalid;

    always_comb begin
        w_state_d = r_state;
        unique case (r_state)
            S_IDLE:   if (w_miss_start)                 w_state_d = S_AR;
            S_AR:     if (m_axi_arready)                w_state_d = S_FILL;
            S_FILL:   if (w_beat && m_axi_rlast)        w_state_d = S_REPLAY;
            S_REPLAY:                                   w_state_d = S_IDLE;
            default:                                    w_state_d = S_IDLE;
        endcase
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state     <= S_IDLE;
            r_valid     <= '0;
            r_fill_idx  <= '0;
            r_fill_tag  <= '0;
            r_fill_beat <= '0;
        end else begin
            r_state <= w_state_d;
            if (w_inv_take) begin
                r_valid <= '0;
            end else if (w_beat && m_axi_rlast) begin
                r_valid[r_fill_idx] <= 1'b1;
            end
            if (w_miss_start) begin
                r_fill_idx  <= w_idx;
                r_fill_tag  <= w_tag;
                r_fill_beat <= '0;
            end else if (w_beat) begin
                r_fill_beat <= r_fill_beat + 1'b1;
            end
        end
    )

    // The tag is written with the last beat, together with its valid bit.
    always_ff @(posedge clk) begin
        if (w_beat && m_axi_rlast) begin
            r_tag[r_fill_idx] <= r_fill_tag;
        end
    end

    // -----------------------------------------------------------------
    // Data RAM: one write port (refill), one sync read port (fetch)
    // -----------------------------------------------------------------
    logic [RAM_AW-1:0] w_wr_addr;
    logic [RAM_AW-1:0] w_rd_addr;
    logic [AXI_DW-1:0] r_rd_beat;
    logic [WSEL_W-1:0] r_rd_wsel;

    assign w_wr_addr = {r_fill_idx, r_fill_beat};
    if (BEATS > 1) begin : g_rd_beats
        assign w_rd_addr = {fetch_addr_next[OFF_W +: IDX_W],
                            fetch_addr_next[BOFF_W +: BEAT_W]};
    end else begin : g_rd_one
        assign w_rd_addr = {fetch_addr_next[OFF_W +: IDX_W], 1'b0};
    end

    always_ff @(posedge clk) begin
        if (w_beat) begin
            r_data[w_wr_addr] <= m_axi_rdata;
        end
        r_rd_beat <= r_data[w_rd_addr];
    end

    if (WORDS_BEAT > 1) begin : g_wsel
        always_ff @(posedge clk) begin
            r_rd_wsel <= fetch_addr_next[2 +: WSEL_W];
        end
        assign fetch_rdata = r_rd_beat[r_rd_wsel * 32 +: 32];
    end else begin : g_nowsel
        assign r_rd_wsel   = '0;
        assign fetch_rdata = r_rd_beat[31:0];
    end

    // -----------------------------------------------------------------
    // AXI4 read master
    // -----------------------------------------------------------------
    assign m_axi_arid    = '0;
    assign m_axi_araddr  = {r_fill_tag, r_fill_idx, {OFF_W{1'b0}}};
    assign m_axi_arlen   = 8'(BEATS - 1);
    assign m_axi_arsize  = 3'($clog2(BEAT_BYTES));
    assign m_axi_arburst = BURST_INCR;
    assign m_axi_arvalid = (r_state == S_AR);
    assign m_axi_rready  = (r_state == S_FILL);

    // Unused: the id (one outstanding burst), the response code (see the
    // header), the PC's low bits.
    logic w_unused;
    assign w_unused = &{1'b0, m_axi_rid, m_axi_rresp, fetch_addr[1:0], r_rd_wsel};

endmodule : peregrine_icache
