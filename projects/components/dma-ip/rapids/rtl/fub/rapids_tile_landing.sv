// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_landing
// Purpose: Per-cell landing space on the sink port (TILE_SPEC 11.9, rapids TASK-027)
//
// Description:
//   A cell sends into RAPIDS only against a strap of LAND_FLITS flits, header
//   included, and RAPIDS reserves that space here: one FIFO of LAND_FLITS
//   beats per cell. The header has already been taken off by
//   rapids_tile_hdr_rx (and its flit returned there), so a FIFO holds only
//   payload beats, by sender. A cell under its strap can never fill its FIFO,
//   so the sink port never waits on a landing space.
//
//   Drain: one whole packet at a time into the sink data path. A packet is a
//   candidate once its tlast beat has landed, so a drain never waits on the
//   network, and only when its channel (its TID) can take all of it now
//   (snk_data_path_axis chan_can_take). A packet for a disabled channel is
//   drained and thrown away. Round-robin over the cells. A cell whose head
//   packet waits for its channel holds only its own landing space, never
//   another cell's.
//
//   Every beat that leaves a FIFO, delivered or thrown away, returns one flit
//   to its cell (ret_valid pulse with the cell slot), so the strap refills as
//   the data moves into its sink channel.
//
// Parameters:
//   - NUM_CHANNELS: sink channels (TID range)
//   - LAND_FLITS:   landing space per cell in beats (TILE_LAND_FLITS), >= 2
//   - NUM_CELLS:    cells with a landing space (rapids_pkg::TILE_NUM_CELLS)
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_tile_landing #(
    parameter int NUM_CHANNELS    = 8,
    parameter int DATA_WIDTH      = 512,
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,
    parameter int LAND_FLITS      = 16,
    parameter int NUM_CELLS       = rapids_pkg::TILE_NUM_CELLS,
    parameter int NC  = NUM_CHANNELS,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW / 8,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SLW = (NUM_CELLS > 1) ? $clog2(NUM_CELLS) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    input  logic [NC-1:0]               cfg_channel_enable,

    // From rapids_tile_hdr_rx: payload beats with their sender's cell slot
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic [SLW-1:0]              s_axis_tsender,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    // To snk_data_path_axis
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,
    input  logic [NC-1:0]               chan_can_take,

    // One flit back to a cell (registered pulse)
    output logic                        ret_valid,
    output logic [SLW-1:0]              ret_slot,

    // Status: a beat arrived for a full landing space (its cell overran its
    // strap; the sink port waits for room), sticky until reset
    output logic                        sts_overrun
);

    initial begin
        if (LAND_FLITS < 2)
            $fatal(1, "rapids_tile_landing: LAND_FLITS must be >= 2 (a header and one payload flit)");
    end

    localparam int EW  = DW + SW + 1 + AXIS_ID_WIDTH + AXIS_DEST_WIDTH + AXIS_USER_WIDTH;
    localparam int PCW = $clog2(LAND_FLITS + 1);

    logic [NUM_CELLS-1:0]          w_wr_valid, w_wr_ready;
    logic [NUM_CELLS-1:0]          w_rd_valid, w_rd_ready;
    logic [NUM_CELLS-1:0][EW-1:0]  w_rd_data;
    logic [EW-1:0]                 w_wr_data;
    logic [NUM_CELLS-1:0][PCW-1:0] r_pkts;         // whole packets landed per cell

    assign w_wr_data = {s_axis_tuser, s_axis_tdest, s_axis_tid, s_axis_tlast, s_axis_tstrb, s_axis_tdata};

    // Head beat of each FIFO, unpacked
    logic [NUM_CELLS-1:0]                      w_hd_last;
    logic [NUM_CELLS-1:0][AXIS_ID_WIDTH-1:0]   w_hd_tid;
    always_comb begin
        for (int c = 0; c < NUM_CELLS; c++) begin
            w_hd_last[c] = w_rd_data[c][DW + SW];
            w_hd_tid[c]  = w_rd_data[c][DW + SW + 1 +: AXIS_ID_WIDTH];
        end
    end

    // Drain state
    logic           r_busy;
    logic [SLW-1:0] r_cur;
    logic           r_drop;          // the packet being drained is thrown away
    logic [SLW-1:0] r_rr;

    // Candidates: a whole packet at the head, for a channel that can take it
    // or that is disabled (thrown away)
    logic [NUM_CELLS-1:0] w_cand, w_cand_drop;
    always_comb begin
        for (int c = 0; c < NUM_CELLS; c++) begin
            logic [CIW-1:0] ch;
            logic           ch_ok;
            ch    = w_hd_tid[c][CIW-1:0];
            ch_ok = (int'(ch) < NC) && ((w_hd_tid[c] >> CIW) == '0);
            w_cand_drop[c] = !ch_ok || !cfg_channel_enable[ch];
            w_cand[c]      = (r_pkts[c] != '0) && (w_cand_drop[c] || chan_can_take[ch]);
        end
    end

    logic           w_pick;
    logic [SLW-1:0] w_pick_c;
    always_comb begin
        w_pick   = 1'b0;
        w_pick_c = '0;
        for (int k = 1; k <= NUM_CELLS; k++) begin
            if (!w_pick && w_cand[(int'(r_rr) + k) % NUM_CELLS]) begin
                w_pick   = 1'b1;
                w_pick_c = SLW'((int'(r_rr) + k) % NUM_CELLS);
            end
        end
    end

    // Output: the head of the cell being drained
    logic [EW-1:0] w_cur_d;
    logic          w_cur_v, w_cur_take;
    assign w_cur_d    = w_rd_data[r_cur];
    assign w_cur_v    = r_busy && w_rd_valid[r_cur];
    assign w_cur_take = w_cur_v && (r_drop || m_axis_tready);

    assign m_axis_tvalid = w_cur_v && !r_drop;
    assign {m_axis_tuser, m_axis_tdest, m_axis_tid, m_axis_tlast, m_axis_tstrb, m_axis_tdata} = w_cur_d;

    always_comb begin
        for (int c = 0; c < NUM_CELLS; c++) begin
            w_wr_valid[c] = s_axis_tvalid && (s_axis_tsender == SLW'(c));
            w_rd_ready[c] = w_cur_take && (r_cur == SLW'(c));
        end
    end
    assign s_axis_tready = w_wr_ready[s_axis_tsender];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_busy      <= 1'b0;
            r_cur       <= '0;
            r_drop      <= 1'b0;
            r_rr        <= SLW'(NUM_CELLS - 1);
            r_pkts      <= '{default:'0};
            ret_valid   <= 1'b0;
            ret_slot    <= '0;
            sts_overrun <= 1'b0;
        end else begin
            for (int c = 0; c < NUM_CELLS; c++) begin
                logic in_pkt;
                logic out_pkt;
                in_pkt  = w_wr_valid[c] && w_wr_ready[c] && s_axis_tlast;
                out_pkt = w_rd_ready[c] && w_hd_last[c];
                if (in_pkt && !out_pkt)      r_pkts[c] <= r_pkts[c] + PCW'(1);
                else if (!in_pkt && out_pkt) r_pkts[c] <= r_pkts[c] - PCW'(1);
            end
            if (!r_busy) begin
                if (w_pick) begin
                    r_busy <= 1'b1;
                    r_cur  <= w_pick_c;
                    r_drop <= w_cand_drop[w_pick_c];
                    r_rr   <= w_pick_c;
                end
            end else if (w_cur_take && w_hd_last[r_cur]) begin
                r_busy <= 1'b0;
            end
            ret_valid <= w_cur_take;
            ret_slot  <= r_cur;
            if (s_axis_tvalid && !s_axis_tready) sts_overrun <= 1'b1;
        end
    )

    for (genvar c = 0; c < NUM_CELLS; c++) begin : g_cell
        gaxi_fifo_sync #(
            .DATA_WIDTH (EW),
            .DEPTH      (LAND_FLITS)
        ) u_land (
            .axi_aclk    (clk),
            .axi_aresetn (rst_n),
            .wr_valid    (w_wr_valid[c]),
            .wr_ready    (w_wr_ready[c]),
            .wr_data     (w_wr_data),
            .rd_ready    (w_rd_ready[c]),
            /* verilator lint_off PINCONNECTEMPTY */
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .rd_valid    (w_rd_valid[c]),
            .rd_data     (w_rd_data[c])
        );
    end

endmodule : rapids_tile_landing
