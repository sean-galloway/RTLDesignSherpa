// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axil_sdpram_slave
// Purpose: Pipelined AXI4-Lite slave backed by a Simple Dual-Port BRAM.
//
// Architecture (see /home/seang/Downloads/AXIL_PIPELINED_SLAVE_SDPRAM.md):
//
//   s_axil_aw/w/b ──→ [ axil4_slave_wr ] ──→ fub_aw/w/b ──→ BRAM port A
//                       (skid buffers)
//
//   s_axil_ar/r   ──→ [ axil4_slave_rd ] ──→ fub_ar/r   ──→ BRAM port B
//                       (skid buffers)
//
// The protocol-side skid buffers live inside axil4_slave_wr / axil4_slave_rd
// — this module owns only the BRAM glue. That means:
//   - dropping in *_cg or *_mon variants is a one-line swap, with no
//     re-verification of the protocol wrapper required;
//   - we benefit from any future fixes to those wrappers automatically;
//   - this file's job collapses to BRAM port A/B handshakes + a single
//     in-flight read latency flop. No FSMs, no shift registers.
//
// Symmetric port: only one AXIL slave interface at parameterized DATA_WIDTH.
// Width conversion (32b host writes vs 256b STREAM desc fetches) is the
// upstream bridge's problem, not this module's.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil_sdpram_slave #(
    parameter int ADDR_WIDTH     = 32,
    parameter int DATA_WIDTH     = 64,        // 32 / 64 typical
    parameter int MEM_DEPTH      = 2048,      // BRAM depth in DATA_WIDTH words

    parameter int SKID_DEPTH_AW  = 2,
    parameter int SKID_DEPTH_W   = 2,
    parameter int SKID_DEPTH_B   = 2,
    parameter int SKID_DEPTH_AR  = 2,
    parameter int SKID_DEPTH_R   = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // ---------------------------------------------------------------
    // AXI4-Lite slave interface
    // ---------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]       s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,

    input  logic [DATA_WIDTH-1:0]       s_axil_wdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,

    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,

    input  logic [ADDR_WIDTH-1:0]       s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,

    output logic [DATA_WIDTH-1:0]       s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

    // ---------------------------------------------------------------
    // Bulk-clear control
    //
    // i_cfg_start_clear  1-cycle pulse: kick the clear FSM. While clearing,
    //                    the AXIL write/read handshakes stall (fub_* readys
    //                    held low) and port A of the BRAM is owned by the
    //                    clear walker, which writes 0 to every word.
    // o_cfg_done_clear   sticky 1 once the walker has retired the last
    //                    word. Cleared by the next i_cfg_start_clear pulse.
    //
    // Restoring the old per-SRAM self-clear capability: the previous
    // bespoke desc_ram / debug_sram modules each carried this; the
    // unified slave dropped it. Bringing it back here means both SRAM
    // instances regain the host-pokeable wipe without reintroducing
    // bespoke RTL.
    // ---------------------------------------------------------------
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,

    // ---------------------------------------------------------------
    // Observation port (non-functional; for harness/CSR counters)
    //
    // o_dbg_vr      [9:0] raw external valid/ready pairs (AW, W, B, AR, R)
    //                       [0] awvalid  [1] awready
    //                       [2] wvalid   [3] wready
    //                       [4] bvalid   [5] bready
    //                       [6] arvalid  [7] arready
    //                       [8] rvalid   [9] rready
    // o_dbg_fub_vr  [9:0] same shape but on the fub-side (between the
    //                       axil4_slave_* wrappers and the BRAM glue)
    // o_dbg_bram_wr  1-cycle pulse on BRAM port-A write fire
    // o_dbg_bram_rd  1-cycle pulse on BRAM port-B read fire
    // o_dbg_busy_wr  axil4_slave_wr busy (skid activity)
    // o_dbg_busy_rd  axil4_slave_rd busy (skid activity)
    // ---------------------------------------------------------------
    output logic [9:0]                  o_dbg_vr,
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd,
    output logic                        o_dbg_busy_wr,
    output logic                        o_dbg_busy_rd
);

    // ---------------------------------------------------------------
    // Derived constants
    // ---------------------------------------------------------------
    localparam int STRB_W   = DATA_WIDTH / 8;
    localparam int ADDR_LSB = $clog2(STRB_W);
    localparam int MEM_AW   = $clog2(MEM_DEPTH);
    localparam int WORD_AW  = ADDR_WIDTH - ADDR_LSB;

    // ---------------------------------------------------------------
    // Fub-side write nets (between axil4_slave_wr skid and BRAM glue)
    // ---------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]   fub_awaddr;
    /* verilator lint_off UNUSED */
    logic [2:0]              fub_awprot;
    /* verilator lint_on UNUSED */
    logic                    fub_awvalid, fub_awready;
    logic [DATA_WIDTH-1:0]   fub_wdata;
    logic [STRB_W-1:0]       fub_wstrb;
    logic                    fub_wvalid,  fub_wready;
    logic [1:0]              fub_bresp;
    logic                    fub_bvalid,  fub_bready;

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH(ADDR_WIDTH),
        .AXIL_DATA_WIDTH(DATA_WIDTH),
        .SKID_DEPTH_AW  (SKID_DEPTH_AW),
        .SKID_DEPTH_W   (SKID_DEPTH_W),
        .SKID_DEPTH_B   (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),

        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),

        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),

        .fub_awaddr     (fub_awaddr),
        .fub_awprot     (fub_awprot),
        .fub_awvalid    (fub_awvalid),
        .fub_awready    (fub_awready),

        .fub_wdata      (fub_wdata),
        .fub_wstrb      (fub_wstrb),
        .fub_wvalid     (fub_wvalid),
        .fub_wready     (fub_wready),

        .fub_bresp      (fub_bresp),
        .fub_bvalid     (fub_bvalid),
        .fub_bready     (fub_bready),

        .busy           (o_dbg_busy_wr)
    );

    // ---------------------------------------------------------------
    // Fub-side read nets (between axil4_slave_rd skid and BRAM glue)
    // ---------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]   fub_araddr;
    /* verilator lint_off UNUSED */
    logic [2:0]              fub_arprot;
    /* verilator lint_on UNUSED */
    logic                    fub_arvalid, fub_arready;
    logic [DATA_WIDTH-1:0]   fub_rdata;
    logic [1:0]              fub_rresp;
    logic                    fub_rvalid,  fub_rready;

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH(ADDR_WIDTH),
        .AXIL_DATA_WIDTH(DATA_WIDTH),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_R   (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),

        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),

        .fub_araddr     (fub_araddr),
        .fub_arprot     (fub_arprot),
        .fub_arvalid    (fub_arvalid),
        .fub_arready    (fub_arready),

        .fub_rdata      (fub_rdata),
        .fub_rresp      (fub_rresp),
        .fub_rvalid     (fub_rvalid),
        .fub_rready     (fub_rready),

        .busy           (o_dbg_busy_rd)
    );

    // ---------------------------------------------------------------
    // Clear FSM — owns BRAM port A while w_clearing is asserted.
    // Walks r_clear_addr 0..MEM_DEPTH-1 writing all-zeros on every
    // cycle, then drops back to IDLE and asserts the sticky done flag.
    //
    // The cfg_start_clear pulse is sampled in IDLE only; arrivals
    // during a clear are ignored (host should observe done first).
    // r_done_clear is held high until the next start kicks the FSM
    // back into BUSY, so a polling host can race-free detect
    // completion.
    // ---------------------------------------------------------------
    typedef enum logic { CLR_IDLE = 1'b0, CLR_BUSY = 1'b1 } clr_state_e;
    clr_state_e        r_clr_state;
    logic [MEM_AW-1:0] r_clear_addr;
    logic              r_done_clear;
    wire               clr_last   = (r_clear_addr == MEM_AW'(MEM_DEPTH - 1));
    wire               w_clearing = (r_clr_state == CLR_BUSY);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_clr_state  <= CLR_IDLE;
            r_clear_addr <= '0;
            r_done_clear <= 1'b0;
        end else begin
            unique case (r_clr_state)
                CLR_IDLE: begin
                    if (i_cfg_start_clear) begin
                        r_clr_state  <= CLR_BUSY;
                        r_clear_addr <= '0;
                        r_done_clear <= 1'b0;
                    end
                end
                CLR_BUSY: begin
                    if (clr_last) begin
                        r_clr_state  <= CLR_IDLE;
                        r_done_clear <= 1'b1;
                    end else begin
                        r_clear_addr <= r_clear_addr + 1'b1;
                    end
                end
            endcase
        end
    )

    assign o_cfg_done_clear = r_done_clear;

    // ---------------------------------------------------------------
    // Write fire — combinational handshake against BRAM port A.
    // Fire when both AW and W heads valid AND downstream B skid can
    // absorb the response (its fub_bready is the wrapper's ready into
    // the B skid). All three handshakes complete the same cycle.
    //
    // The clear FSM owns port A while w_clearing is high, so AW/W/B
    // are stalled (readys low, bvalid low) for the duration of a wipe.
    // ---------------------------------------------------------------
    // Use only the MEM_AW low bits of the word-address as the BRAM
    // index. High address bits are ignored (the address space aliases
    // around the memory's natural size). The previous range check
    // compared the FULL WORD_AW-bit slice against MEM_DEPTH, which
    // marked every absolute address (e.g. 0x00020020 — bits [31:5]
    // are 0x1001) out-of-range even though the row index (bits
    // [11:5]) was valid. That caused silent SLVERR on every write
    // while the uart_axil_bridge cheerfully returned "OK" upstream.
    wire [MEM_AW-1:0]  write_bram_addr     = fub_awaddr[ADDR_LSB +: MEM_AW];
    wire               write_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_aw_word_addr    = fub_awaddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    wire write_fire = fub_awvalid && fub_wvalid && fub_bready && !w_clearing;
    assign fub_awready = fub_wvalid  && fub_bready && !w_clearing;
    assign fub_wready  = fub_awvalid && fub_bready && !w_clearing;
    assign fub_bvalid  = write_fire;
    assign fub_bresp   = write_addr_in_range ? 2'b00 : 2'b10;  // OKAY / SLVERR

    // ---------------------------------------------------------------
    // Read path — BRAM_READ_LAT = 1. Single flop pair carries the
    // in-flight rresp; r_bram_rdata + r_inflight_rresp pair to drive
    // fub_rvalid/data/resp the cycle after AR pop.
    //
    //   read_issue fires when fub_arvalid && we can absorb the next
    //   BRAM data into the R skid. Concretely:
    //     - no read in flight → safe to fire (skid is at-most-1
    //       behind)
    //     - read in flight && downstream R skid will take the data
    //       this cycle → safe to fire (pipeline continues 1/cycle)
    //
    // arready is also gated by !w_clearing so the AR skid stalls
    // for the duration of a wipe (port B's BRAM read is harmless
    // mid-wipe, but issuing it would race the clear walker's port A
    // writes from the same address and could surface stale data on
    // the AXIL R channel).
    // ---------------------------------------------------------------
    // Mirror the write-side fix: row index aliases by MEM_AW bits;
    // high bits are ignored. The previous range check rejected every
    // absolute address that had any bit above MEM_AW set, including
    // STREAM's 0x00020020 descriptor fetches.
    wire [MEM_AW-1:0]  read_bram_addr     = fub_araddr[ADDR_LSB +: MEM_AW];
    wire               read_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_ar_word_addr   = fub_araddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    logic r_inflight;
    logic [1:0] r_inflight_rresp;

    wire read_issue = fub_arvalid && fub_arready;
    assign fub_arready = !w_clearing && (!r_inflight || fub_rready);

    // ---------------------------------------------------------------
    // BRAM — inferred dual-port; one always_ff per port keeps Vivado
    // happy. ram_style left to "auto" so small builds drop into
    // LUTRAM and big builds map to block RAM.
    // ---------------------------------------------------------------
    (* ram_style = "auto" *)
    logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH];

    // Port A: clear FSM owns the port while w_clearing; otherwise
    // byte-enabled AXIL write. No reset (BRAM contents persist
    // across aresetn — bulk wipe is opt-in via cfg_start_clear).
    always_ff @(posedge aclk) begin
        if (w_clearing) begin
            r_mem[r_clear_addr] <= '0;
        end else if (write_fire && write_addr_in_range) begin
            for (int b = 0; b < STRB_W; b++) begin
                if (fub_wstrb[b]) begin
                    r_mem[write_bram_addr][8*b +: 8] <= fub_wdata[8*b +: 8];
                end
            end
        end
    end

    // Port B: read with 1-cycle latency (no output register).
    logic [DATA_WIDTH-1:0] r_bram_rdata;
    always_ff @(posedge aclk) begin
        if (read_issue) begin
            r_bram_rdata <= r_mem[read_bram_addr];
        end
    end

    // In-flight tracking (single flop pair, BRAM_READ_LAT=1).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_inflight       <= 1'b0;
            r_inflight_rresp <= 2'b00;
        end else begin
            // Default: if data was just consumed, drop r_inflight unless
            // we issued a new read this cycle.
            if (r_inflight && fub_rready && !read_issue) begin
                r_inflight <= 1'b0;
            end else if (read_issue) begin
                r_inflight       <= 1'b1;
                r_inflight_rresp <= read_addr_in_range ? 2'b00 : 2'b10;
            end
        end
    )

    assign fub_rvalid = r_inflight;
    assign fub_rdata  = r_bram_rdata;
    assign fub_rresp  = r_inflight_rresp;

    // ---------------------------------------------------------------
    // Observation wiring
    // ---------------------------------------------------------------
    assign o_dbg_vr = {
        s_axil_rready,  s_axil_rvalid,
        s_axil_arready, s_axil_arvalid,
        s_axil_bready,  s_axil_bvalid,
        s_axil_wready,  s_axil_wvalid,
        s_axil_awready, s_axil_awvalid
    };

    assign o_dbg_fub_vr = {
        fub_rready,  fub_rvalid,
        fub_arready, fub_arvalid,
        fub_bready,  fub_bvalid,
        fub_wready,  fub_wvalid,
        fub_awready, fub_awvalid
    };

    assign o_dbg_bram_wr = write_fire && write_addr_in_range;
    assign o_dbg_bram_rd = read_issue;

endmodule : axil_sdpram_slave
