// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad_harness
// Purpose: the host side of gatling_tetrad's cell seams on the Nexys A7: per
//          cell, the configuration a cell's cfg stream would set, a fill
//          port into the input memory, a drain port out of the result
//          memory, a one-deep drain controller that captures each FLUSH
//          command, and the KICK / stall / consumed-line observers.
//
// Documentation: projects/fpga-systems/NexysA7/riscv-ip/gatling/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Created: 2026-11-26
//
// Address map (AXIL, byte addresses, 32-bit registers):
//   addr[8] = 0: cell c = addr[7:6], register = addr[5:2]
//     0x00 CFG_FUNC   RW  [8:0]   func_sel
//     0x04 CFG_LINES  RW  [1:0]   op_lines (2 = two lines, else one)
//     0x08 CFG_THR    RW  [15:0]  threshold
//     0x0C CFG_BATCH  RW  [31:0]  credit batch (CFG index 1; the FLUSH word)
//     0x10 FILL/OCC   W   push one line into the input memory (the write
//                         waits for min_wr_ready; the harness keeps the tail)
//                     R   {mout_occupancy[15:8], min_occupancy[7:0]}
//     0x14 DRAIN      R   pop one result line (head kept here); an empty
//                         result memory returns 0 and sets STAT[11]
//     0x18 FLUSH      R   {valid[31], kicks_at_capture[30:24], count[23:20],
//                          tag[18:15], dest[14:0]}; reading clears valid,
//                         which is the drain controller's ready
//     0x1C KICK       R   last kick value
//     0x20 KICKCNT    R   kicks seen
//     0x24 STAT       R   {underflow[11], alu_err[10], event[9], stalled[8],
//                          stall_seen[7:0] (one bit per funct3, sticky)}
//     0x28 CONSUMED   R   input-memory lines consumed (line_consumed count)
//   addr[8] = 1: global
//     0x100 ID        R   "TTRD"
//     0x104 FLAGS     R   {ctx_stalled[11:8], done[7:4], event_flags[3:0]}
//     0x108 CLEAR     W   any write clears the sticky observers (KICKCNT,
//                         STAT stall_seen / alu_err / underflow, CONSUMED,
//                         FLUSH count).  Never the fill tail or drain head:
//                         they track pointers inside the tetrad.
//
// Notes:
//   - The fill tail and drain head mirror the Xcell unit's input head and
//     result tail; both sides advance one per line and reset together, so
//     they stay aligned across runs.
//   - One outstanding read and one outstanding write (uart_axil_bridge
//     issues one command at a time).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_tetrad_harness #(
    parameter int NUM_HARTS = 4,
    parameter int IN_DEPTH  = 32,
    parameter int OUT_DEPTH = 32,
    parameter int IN_AW     = $clog2(IN_DEPTH),
    parameter int OUT_AW    = $clog2(OUT_DEPTH),
    parameter int IN_OCC_W  = $clog2(IN_DEPTH + 1),
    parameter int OUT_OCC_W = $clog2(OUT_DEPTH + 1)
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    // Host AXI4-Lite (12-bit window)
    input  logic [11:0]           s_axil_awaddr,
    input  logic [2:0]            s_axil_awprot,
    input  logic                  s_axil_awvalid,
    output logic                  s_axil_awready,
    input  logic [31:0]           s_axil_wdata,
    input  logic [3:0]            s_axil_wstrb,
    input  logic                  s_axil_wvalid,
    output logic                  s_axil_wready,
    output logic [1:0]            s_axil_bresp,
    output logic                  s_axil_bvalid,
    input  logic                  s_axil_bready,
    input  logic [11:0]           s_axil_araddr,
    input  logic [2:0]            s_axil_arprot,
    input  logic                  s_axil_arvalid,
    output logic                  s_axil_arready,
    output logic [31:0]           s_axil_rdata,
    output logic [1:0]            s_axil_rresp,
    output logic                  s_axil_rvalid,
    input  logic                  s_axil_rready,

    // gatling_tetrad cell seams
    output logic [8:0]            cfg_func_sel     [NUM_HARTS],
    output logic [1:0]            cfg_op_lines     [NUM_HARTS],
    output logic [15:0]           cfg_threshold    [NUM_HARTS],
    output logic [31:0]           cfg_credit_batch [NUM_HARTS],
    output logic                  min_wr_valid     [NUM_HARTS],
    input  logic                  min_wr_ready     [NUM_HARTS],
    output logic [IN_AW-1:0]      min_wr_addr      [NUM_HARTS],
    output logic [31:0]           min_wr_data      [NUM_HARTS],
    input  logic [IN_OCC_W-1:0]   min_occupancy    [NUM_HARTS],
    input  logic                  line_consumed    [NUM_HARTS],
    output logic                  mout_rd_valid    [NUM_HARTS],
    output logic [OUT_AW-1:0]     mout_rd_addr     [NUM_HARTS],
    input  logic [31:0]           mout_rd_data     [NUM_HARTS],
    input  logic [OUT_OCC_W-1:0]  mout_occupancy   [NUM_HARTS],
    input  logic                  flush_valid      [NUM_HARTS],
    output logic                  flush_ready      [NUM_HARTS],
    input  logic [14:0]           flush_dest       [NUM_HARTS],
    input  logic [3:0]            flush_tag        [NUM_HARTS],
    input  logic                  kick_valid       [NUM_HARTS],
    input  logic [31:0]           kick_value       [NUM_HARTS],
    input  logic [NUM_HARTS-1:0]  event_flags,
    input  logic [NUM_HARTS-1:0]  ctx_stalled,
    input  logic [2:0]            ctx_stall_op     [NUM_HARTS],
    input  logic                  alu_err_opcode   [NUM_HARTS],
    input  logic [NUM_HARTS-1:0]  done
);

    localparam logic [31:0] HARNESS_ID = 32'h5454_5244;   // "TTRD"
    localparam logic [1:0]  RESP_OKAY  = 2'b00;
    localparam int          HART_W     = $clog2(NUM_HARTS);

    localparam logic [3:0] R_FUNC = 4'h0, R_LINES = 4'h1, R_THR = 4'h2, R_BATCH = 4'h3,
                           R_FILL = 4'h4, R_DRAIN = 4'h5, R_FLUSH = 4'h6, R_KICK = 4'h7,
                           R_KICKCNT = 4'h8, R_STAT = 4'h9, R_CONSUMED = 4'hA;

    // =========================================================================
    // AXIL leaf slaves
    // =========================================================================
    logic [11:0] fub_awaddr, fub_araddr;
    logic [2:0]  fub_awprot, fub_arprot;
    logic        fub_awvalid, fub_awready, fub_wvalid, fub_wready;
    logic [31:0] fub_wdata, fub_rdata;
    logic [3:0]  fub_wstrb;
    logic [1:0]  fub_bresp, fub_rresp;
    logic        fub_bvalid, fub_bready, fub_arvalid, fub_arready;
    logic        fub_rvalid, fub_rready;

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH(12), .AXIL_DATA_WIDTH(32)
    ) u_axil_wr (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(s_axil_awaddr), .s_axil_awprot(s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata(s_axil_wdata), .s_axil_wstrb(s_axil_wstrb),
        .s_axil_wvalid(s_axil_wvalid), .s_axil_wready(s_axil_wready),
        .s_axil_bresp(s_axil_bresp), .s_axil_bvalid(s_axil_bvalid), .s_axil_bready(s_axil_bready),
        .fub_awaddr(fub_awaddr), .fub_awprot(fub_awprot),
        .fub_awvalid(fub_awvalid), .fub_awready(fub_awready),
        .fub_wdata(fub_wdata), .fub_wstrb(fub_wstrb),
        .fub_wvalid(fub_wvalid), .fub_wready(fub_wready),
        .fub_bresp(fub_bresp), .fub_bvalid(fub_bvalid), .fub_bready(fub_bready),
        .busy());

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH(12), .AXIL_DATA_WIDTH(32)
    ) u_axil_rd (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .fub_araddr(fub_araddr), .fub_arprot(fub_arprot),
        .fub_arvalid(fub_arvalid), .fub_arready(fub_arready),
        .fub_rdata(fub_rdata), .fub_rresp(fub_rresp),
        .fub_rvalid(fub_rvalid), .fub_rready(fub_rready),
        .busy());

    // =========================================================================
    // Write side: AW holding register + B holding bit
    // =========================================================================
    logic [11:0]       r_wr_addr;
    logic              r_wr_pend, r_b_pend;
    logic              w_aw_fire, w_w_fire, w_b_fire;
    logic              w_wr_glob;
    logic [HART_W-1:0] w_wr_cell;
    logic [3:0]        w_wr_reg;
    logic              w_wr_fill, w_fill_ok;

    assign w_aw_fire   = fub_awvalid && fub_awready;
    assign w_w_fire    = fub_wvalid  && fub_wready;
    assign w_b_fire    = fub_bvalid  && fub_bready;
    assign w_wr_glob   = r_wr_addr[8];
    assign w_wr_cell   = r_wr_addr[6 +: HART_W];
    assign w_wr_reg    = r_wr_addr[5:2];
    assign w_wr_fill   = !w_wr_glob && (w_wr_reg == R_FILL);
    assign w_fill_ok   = min_wr_ready[w_wr_cell];

    assign fub_awready = !r_wr_pend || w_w_fire;
    assign fub_wready  = r_wr_pend && !r_b_pend && (!w_wr_fill || w_fill_ok);
    assign fub_bvalid  = r_b_pend;
    assign fub_bresp   = RESP_OKAY;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_addr <= '0;
            r_wr_pend <= 1'b0;
            r_b_pend  <= 1'b0;
        end else begin
            if (w_aw_fire) r_wr_addr <= fub_awaddr;
            case ({w_aw_fire, w_w_fire})
                2'b10:   r_wr_pend <= 1'b1;
                2'b01:   r_wr_pend <= 1'b0;
                default: ;
            endcase
            if (w_w_fire)      r_b_pend <= 1'b1;
            else if (w_b_fire) r_b_pend <= 1'b0;
        end
    )

    logic w_clear;
    assign w_clear = w_w_fire && w_wr_glob && (w_wr_reg == 4'h2);   // 0x108

    // =========================================================================
    // Read side: AR -> one wait stage (the result-memory read) -> holding reg
    // =========================================================================
    logic              r_rd_wait, r_rd_full;
    logic              r_rd_glob;
    logic [HART_W-1:0] r_rd_cell;
    logic [3:0]        r_rd_reg;
    logic [31:0]       r_rd_data, w_rd_mux;
    logic              w_ar_fire;
    logic              w_ar_glob;
    logic [HART_W-1:0] w_ar_cell;
    logic [3:0]        w_ar_reg;

    assign fub_arready = !r_rd_wait && !r_rd_full;
    assign w_ar_fire   = fub_arvalid && fub_arready;
    assign w_ar_glob   = fub_araddr[8];
    assign w_ar_cell   = fub_araddr[6 +: HART_W];
    assign w_ar_reg    = fub_araddr[5:2];
    assign fub_rvalid  = r_rd_full;
    assign fub_rdata   = r_rd_data;
    assign fub_rresp   = RESP_OKAY;

    // =========================================================================
    // Per-cell state
    // =========================================================================
    logic [8:0]          r_func   [NUM_HARTS];
    logic [1:0]          r_lines  [NUM_HARTS];
    logic [15:0]         r_thr    [NUM_HARTS];
    logic [31:0]         r_batch  [NUM_HARTS];
    logic [IN_AW-1:0]    r_tail   [NUM_HARTS];
    logic [OUT_AW-1:0]   r_head   [NUM_HARTS];
    logic                r_fcap_v [NUM_HARTS];
    logic [14:0]         r_fcap_dest [NUM_HARTS];
    logic [3:0]          r_fcap_tag  [NUM_HARTS];
    logic [6:0]          r_fcap_kicks [NUM_HARTS];
    logic [3:0]          r_fcnt   [NUM_HARTS];
    logic [31:0]         r_kval   [NUM_HARTS];
    logic [7:0]          r_kcnt   [NUM_HARTS];
    logic [7:0]          r_seen   [NUM_HARTS];
    logic                r_aerr   [NUM_HARTS];
    logic                r_under  [NUM_HARTS];
    logic [31:0]         r_cons   [NUM_HARTS];
    logic [6:0]          r_kicks_total;

    logic [NUM_HARTS-1:0] w_drain_rd, w_drain_pop, w_flush_rd;

    always_comb begin
        for (int c = 0; c < NUM_HARTS; c++) begin
            w_drain_rd[c]  = w_ar_fire && !w_ar_glob && (w_ar_cell == HART_W'(c))
                             && (w_ar_reg == R_DRAIN);
            w_drain_pop[c] = w_drain_rd[c] && (mout_occupancy[c] != '0);
            w_flush_rd[c]  = w_ar_fire && !w_ar_glob && (w_ar_cell == HART_W'(c))
                             && (w_ar_reg == R_FLUSH);

            cfg_func_sel[c]     = r_func[c];
            cfg_op_lines[c]     = r_lines[c];
            cfg_threshold[c]    = r_thr[c];
            cfg_credit_batch[c] = r_batch[c];

            min_wr_valid[c] = w_w_fire && w_wr_fill && (w_wr_cell == HART_W'(c));
            min_wr_addr[c]  = r_tail[c];
            min_wr_data[c]  = fub_wdata;

            mout_rd_valid[c] = w_drain_pop[c];
            mout_rd_addr[c]  = r_head[c];

            flush_ready[c]   = !r_fcap_v[c];
        end
    end

    // Kicks this cycle, across cells (feeds the FLUSH capture's snapshot)
    logic [2:0] w_kicks_now;
    always_comb begin
        w_kicks_now = '0;
        for (int c = 0; c < NUM_HARTS; c++) w_kicks_now = w_kicks_now + 3'(kick_valid[c]);
    end

    // Configuration registers: clock-only (no reset; the host writes them
    // before it runs a context)
    always_ff @(posedge aclk) begin
        for (int c = 0; c < NUM_HARTS; c++) begin
            if (w_w_fire && !w_wr_glob && (w_wr_cell == HART_W'(c))) begin
                case (w_wr_reg)
                    R_FUNC:  r_func[c]  <= fub_wdata[8:0];
                    R_LINES: r_lines[c] <= fub_wdata[1:0];
                    R_THR:   r_thr[c]   <= fub_wdata[15:0];
                    R_BATCH: r_batch[c] <= fub_wdata;
                    default: ;
                endcase
            end
            if (kick_valid[c]) r_kval[c] <= kick_value[c];
            if (flush_valid[c] && !r_fcap_v[c]) begin
                r_fcap_dest[c]  <= flush_dest[c];
                r_fcap_tag[c]   <= flush_tag[c];
                r_fcap_kicks[c] <= r_kicks_total;
            end
        end
    end

    // Pointers, the capture valid, and the sticky observers
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                r_tail[c]   <= '0;
                r_head[c]   <= '0;
                r_fcap_v[c] <= 1'b0;
                r_fcnt[c]   <= '0;
                r_kcnt[c]   <= '0;
                r_seen[c]   <= '0;
                r_aerr[c]   <= 1'b0;
                r_under[c]  <= 1'b0;
                r_cons[c]   <= '0;
            end
            r_kicks_total <= '0;
        end else begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                if (min_wr_valid[c])
                    r_tail[c] <= (r_tail[c] == IN_AW'(IN_DEPTH - 1)) ? '0 : r_tail[c] + 1'b1;
                if (w_drain_pop[c])
                    r_head[c] <= (r_head[c] == OUT_AW'(OUT_DEPTH - 1)) ? '0 : r_head[c] + 1'b1;

                if (flush_valid[c] && !r_fcap_v[c]) r_fcap_v[c] <= 1'b1;
                else if (w_flush_rd[c])             r_fcap_v[c] <= 1'b0;

                if (w_clear) begin
                    r_fcnt[c]  <= '0;
                    r_kcnt[c]  <= '0;
                    r_seen[c]  <= '0;
                    r_aerr[c]  <= 1'b0;
                    r_under[c] <= 1'b0;
                    r_cons[c]  <= '0;
                end else begin
                    if (flush_valid[c] && !r_fcap_v[c]) r_fcnt[c] <= r_fcnt[c] + 1'b1;
                    if (kick_valid[c])    r_kcnt[c] <= r_kcnt[c] + 1'b1;
                    if (ctx_stalled[c])   r_seen[c][ctx_stall_op[c]] <= 1'b1;
                    if (alu_err_opcode[c]) r_aerr[c] <= 1'b1;
                    if (w_drain_rd[c] && !w_drain_pop[c]) r_under[c] <= 1'b1;
                    if (line_consumed[c]) r_cons[c] <= r_cons[c] + 1'b1;
                end
            end
            if (w_clear) r_kicks_total <= '0;
            else         r_kicks_total <= r_kicks_total + 7'(w_kicks_now);
        end
    )

    // Read data: chosen in the wait stage, when a DRAIN's line is on
    // mout_rd_data (the result memory's registered read)
    logic r_rd_pop;
    always_comb begin
        w_rd_mux = '0;
        if (r_rd_glob) begin
            case (r_rd_reg)
                4'h0:    w_rd_mux = HARNESS_ID;
                4'h1:    w_rd_mux = {20'd0, ctx_stalled, done, event_flags};
                default: w_rd_mux = '0;
            endcase
        end else begin
            case (r_rd_reg)
                R_FUNC:     w_rd_mux = {23'd0, r_func[r_rd_cell]};
                R_LINES:    w_rd_mux = {30'd0, r_lines[r_rd_cell]};
                R_THR:      w_rd_mux = {16'd0, r_thr[r_rd_cell]};
                R_BATCH:    w_rd_mux = r_batch[r_rd_cell];
                R_FILL:     w_rd_mux = {16'd0, 8'(mout_occupancy[r_rd_cell]),
                                        8'(min_occupancy[r_rd_cell])};
                R_DRAIN:    w_rd_mux = r_rd_pop ? mout_rd_data[r_rd_cell] : 32'd0;
                R_KICK:     w_rd_mux = r_kval[r_rd_cell];
                R_KICKCNT:  w_rd_mux = {24'd0, r_kcnt[r_rd_cell]};
                R_STAT:     w_rd_mux = {20'd0, r_under[r_rd_cell], r_aerr[r_rd_cell],
                                        event_flags[r_rd_cell], ctx_stalled[r_rd_cell],
                                        r_seen[r_rd_cell]};
                R_CONSUMED: w_rd_mux = r_cons[r_rd_cell];
                default:    w_rd_mux = '0;
            endcase
        end
    end

    // FLUSH is sampled at AR (the read clears the capture on the same edge)
    logic [31:0] r_flush_snap;
    always_ff @(posedge aclk) begin
        if (w_ar_fire)
            r_flush_snap <= {r_fcap_v[w_ar_cell], r_fcap_kicks[w_ar_cell], r_fcnt[w_ar_cell],
                             1'b0, r_fcap_tag[w_ar_cell], r_fcap_dest[w_ar_cell]};
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_wait <= 1'b0;
            r_rd_full <= 1'b0;
            r_rd_glob <= 1'b0;
            r_rd_cell <= '0;
            r_rd_reg  <= '0;
            r_rd_pop  <= 1'b0;
            r_rd_data <= '0;
        end else begin
            if (w_ar_fire) begin
                r_rd_wait <= 1'b1;
                r_rd_glob <= w_ar_glob;
                r_rd_cell <= w_ar_cell;
                r_rd_reg  <= w_ar_reg;
                r_rd_pop  <= |w_drain_pop;
            end else if (r_rd_wait) begin
                r_rd_wait <= 1'b0;
                r_rd_full <= 1'b1;
                r_rd_data <= (!r_rd_glob && r_rd_reg == R_FLUSH) ? r_flush_snap : w_rd_mux;
            end else if (fub_rvalid && fub_rready) begin
                r_rd_full <= 1'b0;
            end
        end
    )

endmodule : gatling_tetrad_harness
