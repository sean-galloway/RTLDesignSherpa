// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axil_sdpram_slave
// Purpose: Pipelined AXI4-Lite slave backed by a Simple Dual-Port BRAM.
//
// Architecture (see /home/seang/Downloads/AXIL_PIPELINED_SLAVE_SDPRAM.md):
//
//   AW ─→ AW_queue ─┐
//                   ├──→ port A (BRAM write)  ──→ B_queue → B
//   W  ─→ W_queue  ─┘
//
//   AR ─→ AR_queue ─→ port B (BRAM read, lat=1) ─┐
//                                                ├─→ R_out_queue → R
//                  rresp pre-computed at AR pop ─┘
//
//   No FSMs. Every sequencer is a gaxi_fifo_sync, no shift registers.
//   Read latency is BRAM_READ_LAT=1 (no output register) so the "slot
//   tracker" between AR pop and BRAM data return collapses to a single
//   one-cycle pipeline flop pair.
//
// Symmetric port: only one AXIL slave interface. Width conversion (32-bit
// host writes vs wider STREAM reads) is the upstream bridge's problem.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil_sdpram_slave #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,           // power of two; 32 or 64 typical
    parameter int MEM_DEPTH  = 2048,         // BRAM depth in DATA_WIDTH words

    parameter int AW_DEPTH   = 4,            // queue depths (all gaxi_fifo_sync)
    parameter int W_DEPTH    = 4,
    parameter int AR_DEPTH   = 4,
    parameter int B_DEPTH    = 4,
    parameter int R_DEPTH    = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // ---------------------------------------------------------------
    // AXI4-Lite slave interface
    // ---------------------------------------------------------------
    // Write address channel
    input  logic [ADDR_WIDTH-1:0]       s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,

    // Write data channel
    input  logic [DATA_WIDTH-1:0]       s_axil_wdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,

    // Write response channel
    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,

    // Read address channel
    input  logic [ADDR_WIDTH-1:0]       s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,

    // Read data channel
    output logic [DATA_WIDTH-1:0]       s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

    // ---------------------------------------------------------------
    // Observation bus — non-functional; for harness/CSR counters.
    //
    // Layout (packed, all combinational unless noted):
    //   o_dbg_vr    [9:0]  raw valid/ready bits for AW, W, B, AR, R
    //                       [0] awvalid  [1] awready
    //                       [2] wvalid   [3] wready
    //                       [4] bvalid   [5] bready
    //                       [6] arvalid  [7] arready
    //                       [8] rvalid   [9] rready
    //   o_dbg_q_full[4:0]  one-bit per queue (AW, W, AR, B, R) — currently full
    //   o_dbg_q_count_*    queue occupancy (0..DEPTH) for each queue
    //   o_dbg_bram_wr      1 cycle pulse: BRAM port A wrote
    //   o_dbg_bram_rd      1 cycle pulse: BRAM port B issued a read
    // ---------------------------------------------------------------
    output logic [9:0]                  o_dbg_vr,
    output logic [4:0]                  o_dbg_q_full,
    output logic [$clog2(AW_DEPTH+1)-1:0] o_dbg_q_count_aw,
    output logic [$clog2(W_DEPTH +1)-1:0] o_dbg_q_count_w,
    output logic [$clog2(AR_DEPTH+1)-1:0] o_dbg_q_count_ar,
    output logic [$clog2(B_DEPTH +1)-1:0] o_dbg_q_count_b,
    output logic [$clog2(R_DEPTH +1)-1:0] o_dbg_q_count_r,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd
);

    // ---------------------------------------------------------------
    // Derived constants
    // ---------------------------------------------------------------
    localparam int STRB_W       = DATA_WIDTH / 8;
    localparam int ADDR_LSB     = $clog2(STRB_W);    // byte-offset bits
    localparam int MEM_AW       = $clog2(MEM_DEPTH); // BRAM addr width
    localparam int AW_PKT_W     = ADDR_WIDTH + 3;            // addr + awprot
    localparam int W_PKT_W      = DATA_WIDTH + STRB_W;       // data + wstrb
    localparam int AR_PKT_W     = ADDR_WIDTH + 3;            // addr + arprot

    // ---------------------------------------------------------------
    // AW_queue : holds {addr, prot} until matched with a W_queue head.
    // ---------------------------------------------------------------
    logic                aw_q_wr_valid, aw_q_wr_ready;
    logic                aw_q_rd_valid, aw_q_rd_ready;
    logic [AW_PKT_W-1:0] aw_q_rd_pkt;
    logic [$clog2(AW_DEPTH+1)-1:0] aw_q_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (AW_PKT_W),
        .DEPTH      (AW_DEPTH)
    ) u_aw_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (aw_q_wr_valid),
        .wr_ready   (aw_q_wr_ready),
        .wr_data    ({s_axil_awaddr, s_axil_awprot}),
        .count      (aw_q_count),
        .rd_valid   (aw_q_rd_valid),
        .rd_ready   (aw_q_rd_ready),
        .rd_data    (aw_q_rd_pkt)
    );

    // Push every accepted AW. AWREADY = NOT full.
    assign aw_q_wr_valid  = s_axil_awvalid;
    assign s_axil_awready = aw_q_wr_ready;

    logic [ADDR_WIDTH-1:0] aw_q_head_addr;
    /* verilator lint_off UNUSED */
    logic [2:0]            aw_q_head_prot;
    /* verilator lint_on UNUSED */
    assign {aw_q_head_addr, aw_q_head_prot} = aw_q_rd_pkt;

    // ---------------------------------------------------------------
    // W_queue : holds {data, strb}.
    // ---------------------------------------------------------------
    logic               w_q_wr_valid, w_q_wr_ready;
    logic               w_q_rd_valid, w_q_rd_ready;
    logic [W_PKT_W-1:0] w_q_rd_pkt;
    logic [$clog2(W_DEPTH+1)-1:0] w_q_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (W_PKT_W),
        .DEPTH      (W_DEPTH)
    ) u_w_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_q_wr_valid),
        .wr_ready   (w_q_wr_ready),
        .wr_data    ({s_axil_wdata, s_axil_wstrb}),
        .count      (w_q_count),
        .rd_valid   (w_q_rd_valid),
        .rd_ready   (w_q_rd_ready),
        .rd_data    (w_q_rd_pkt)
    );

    assign w_q_wr_valid  = s_axil_wvalid;
    assign s_axil_wready = w_q_wr_ready;

    logic [DATA_WIDTH-1:0] w_q_head_data;
    logic [STRB_W-1:0]     w_q_head_strb;
    assign {w_q_head_data, w_q_head_strb} = w_q_rd_pkt;

    // ---------------------------------------------------------------
    // B_queue : holds bresp until master pops it on the B channel.
    // ---------------------------------------------------------------
    logic       b_q_wr_valid, b_q_wr_ready;
    logic [1:0] b_q_wr_data;
    logic       b_q_rd_valid, b_q_rd_ready;
    logic [1:0] b_q_rd_data;
    logic [$clog2(B_DEPTH+1)-1:0] b_q_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (2),
        .DEPTH      (B_DEPTH)
    ) u_b_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (b_q_wr_valid),
        .wr_ready   (b_q_wr_ready),
        .wr_data    (b_q_wr_data),
        .count      (b_q_count),
        .rd_valid   (b_q_rd_valid),
        .rd_ready   (b_q_rd_ready),
        .rd_data    (b_q_rd_data)
    );

    assign s_axil_bvalid = b_q_rd_valid;
    assign s_axil_bresp  = b_q_rd_data;
    assign b_q_rd_ready  = s_axil_bready;

    // ---------------------------------------------------------------
    // Write fire — pop AW, W; push BRESP into B_queue.
    // ---------------------------------------------------------------
    // write_fire = AW head valid && W head valid && B has room.
    // Same cycle: BRAM port A receives wr_en=1, addr=AW head, data=W head,
    // byte enables = W strb. B_queue receives OKAY (or SLVERR if addr is
    // beyond MEM_DEPTH).
    logic                  write_fire;
    logic                  write_addr_in_range;
    logic [MEM_AW-1:0]     write_bram_addr;

    localparam int WORD_AW = ADDR_WIDTH - ADDR_LSB;
    wire [WORD_AW-1:0] aw_q_head_word_addr = aw_q_head_addr[ADDR_LSB +: WORD_AW];
    assign write_addr_in_range = (aw_q_head_word_addr < WORD_AW'(MEM_DEPTH));
    assign write_bram_addr = aw_q_head_addr[ADDR_LSB +: MEM_AW];

    assign write_fire   = aw_q_rd_valid && w_q_rd_valid && b_q_wr_ready;
    assign aw_q_rd_ready = write_fire;
    assign w_q_rd_ready  = write_fire;
    assign b_q_wr_valid  = write_fire;
    assign b_q_wr_data   = write_addr_in_range ? 2'b00 : 2'b10;  // OKAY / SLVERR

    // ---------------------------------------------------------------
    // AR_queue : holds {addr, prot} pending BRAM read.
    // ---------------------------------------------------------------
    logic                 ar_q_wr_valid, ar_q_wr_ready;
    logic                 ar_q_rd_valid, ar_q_rd_ready;
    logic [AR_PKT_W-1:0]  ar_q_rd_pkt;
    logic [$clog2(AR_DEPTH+1)-1:0] ar_q_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (AR_PKT_W),
        .DEPTH      (AR_DEPTH)
    ) u_ar_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (ar_q_wr_valid),
        .wr_ready   (ar_q_wr_ready),
        .wr_data    ({s_axil_araddr, s_axil_arprot}),
        .count      (ar_q_count),
        .rd_valid   (ar_q_rd_valid),
        .rd_ready   (ar_q_rd_ready),
        .rd_data    (ar_q_rd_pkt)
    );

    assign ar_q_wr_valid  = s_axil_arvalid;
    assign s_axil_arready = ar_q_wr_ready;

    logic [ADDR_WIDTH-1:0] ar_q_head_addr;
    /* verilator lint_off UNUSED */
    logic [2:0]            ar_q_head_prot;
    /* verilator lint_on UNUSED */
    assign {ar_q_head_addr, ar_q_head_prot} = ar_q_rd_pkt;

    logic                  read_addr_in_range;
    logic [MEM_AW-1:0]     read_bram_addr;
    wire [WORD_AW-1:0] ar_q_head_word_addr = ar_q_head_addr[ADDR_LSB +: WORD_AW];
    assign read_addr_in_range = (ar_q_head_word_addr < WORD_AW'(MEM_DEPTH));
    assign read_bram_addr = ar_q_head_addr[ADDR_LSB +: MEM_AW];

    // ---------------------------------------------------------------
    // R_out_queue : final R-channel skid. We push as BRAM data returns.
    // ---------------------------------------------------------------
    localparam int R_PKT_W = DATA_WIDTH + 2;       // {data, resp}
    logic               r_q_wr_valid, r_q_wr_ready;
    logic [R_PKT_W-1:0] r_q_wr_data;
    logic               r_q_rd_valid, r_q_rd_ready;
    logic [R_PKT_W-1:0] r_q_rd_data;
    logic [$clog2(R_DEPTH+1)-1:0] r_q_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (R_PKT_W),
        .DEPTH      (R_DEPTH)
    ) u_r_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (r_q_wr_valid),
        .wr_ready   (r_q_wr_ready),
        .wr_data    (r_q_wr_data),
        .count      (r_q_count),
        .rd_valid   (r_q_rd_valid),
        .rd_ready   (r_q_rd_ready),
        .rd_data    (r_q_rd_data)
    );

    assign s_axil_rvalid           = r_q_rd_valid;
    assign {s_axil_rdata, s_axil_rresp} = r_q_rd_data;
    assign r_q_rd_ready            = s_axil_rready;

    // ---------------------------------------------------------------
    // Read fire — pop AR_queue, drive BRAM port B, register the rresp
    // for one cycle (BRAM_READ_LAT=1), pair with returning BRAM data
    // next cycle and push into R_out_queue.
    //
    // We backpressure AR pop on r_q_wr_ready being able to absorb BOTH
    // the next BRAM data return AND the one currently being issued —
    // simplest gate: don't issue while a read is in flight AND R_queue
    // is one slot away from full. With R_DEPTH=4 and 1-cycle latency
    // this gives full 1-per-cycle throughput.
    // ---------------------------------------------------------------
    logic       r_inflight;            // 1 = BRAM data arriving next cycle
    logic [1:0] r_inflight_rresp;      // rresp tag for the in-flight read

    logic       read_issue;            // AR-pop + BRAM read this cycle

    // Pop AR only if (R_queue has room for a push next cycle).
    // r_q has space when count <= R_DEPTH - 1 - inflight_pushes.
    // Approx: r_q_count + r_inflight < R_DEPTH.
    wire r_queue_has_room =
        (r_q_count + {{($clog2(R_DEPTH+1)-1){1'b0}}, r_inflight}) <
        ($clog2(R_DEPTH+1))'(R_DEPTH);

    assign read_issue   = ar_q_rd_valid && r_queue_has_room;
    assign ar_q_rd_ready = read_issue;

    // BRAM read enable on port B (combinational gate of read_issue).
    logic bram_rd_en;
    assign bram_rd_en = read_issue;

    // ---------------------------------------------------------------
    // BRAM — inferred dual-port; one port write-only, one port read-only.
    // Vivado synth picks distributed/BRAM based on size; explicit
    // ram_style attribute keeps small builds in LUTRAM.
    // ---------------------------------------------------------------
    (* ram_style = "auto" *)
    logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH];

    // Port A: write w/ byte enables (one always_ff so Vivado infers BRAM).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // BRAM has no reset (data persists). Intentional no-op.
        end else begin
            if (write_fire && write_addr_in_range) begin
                for (int b = 0; b < STRB_W; b++) begin
                    if (w_q_head_strb[b]) begin
                        r_mem[write_bram_addr][8*b +: 8] <= w_q_head_data[8*b +: 8];
                    end
                end
            end
        end
    )

    // Port B: read (BRAM_READ_LAT=1).
    logic [DATA_WIDTH-1:0] r_bram_rdata;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bram_rdata <= '0;
        end else if (bram_rd_en) begin
            r_bram_rdata <= r_mem[read_bram_addr];
        end
    )

    // In-flight tracking: 1-cycle BRAM latency → 1 flop carries the
    // rresp and a "data arriving next cycle" valid. No shift register.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_inflight       <= 1'b0;
            r_inflight_rresp <= 2'b00;
        end else begin
            r_inflight       <= read_issue;
            // OKAY if in-range, SLVERR if not (still drives a R beat so
            // the master can't get orphaned).
            r_inflight_rresp <= read_addr_in_range ? 2'b00 : 2'b10;
        end
    )

    // R_queue push when BRAM data is valid (the cycle after read_issue).
    // r_queue_has_room above guarantees r_q_wr_ready here.
    assign r_q_wr_valid = r_inflight;
    assign r_q_wr_data  = {r_bram_rdata, r_inflight_rresp};

    // ---------------------------------------------------------------
    // Observation port wiring
    // ---------------------------------------------------------------
    assign o_dbg_vr = {
        s_axil_rready, s_axil_rvalid,
        s_axil_arready, s_axil_arvalid,
        s_axil_bready, s_axil_bvalid,
        s_axil_wready, s_axil_wvalid,
        s_axil_awready, s_axil_awvalid
    };

    // queue_full bits — convenient one-bit warnings for the host.
    assign o_dbg_q_full = {
        !r_q_wr_ready,
        !b_q_wr_ready,
        !ar_q_wr_ready,
        !w_q_wr_ready,
        !aw_q_wr_ready
    };

    assign o_dbg_q_count_aw = aw_q_count;
    assign o_dbg_q_count_w  = w_q_count;
    assign o_dbg_q_count_ar = ar_q_count;
    assign o_dbg_q_count_b  = b_q_count;
    assign o_dbg_q_count_r  = r_q_count;

    assign o_dbg_bram_wr = write_fire && write_addr_in_range;
    assign o_dbg_bram_rd = bram_rd_en;

endmodule : axil_sdpram_slave
