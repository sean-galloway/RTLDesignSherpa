// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: wr_beat_sequencer
// Purpose: Pull W beats out of the axi_frontend's `w_buf` via the wr CAM's
//          beat_pull port, pack them into DFI_RATE DRAM beats per DFI cycle,
//          drive dfi_wrdata / dfi_wrdata_en / dfi_wrdata_mask with PHY
//          alignment, and emit b_complete when the write retires.
//
// Body design:
//          Single-burst FSM:
//            IDLE → PULL → WAIT → DRIVE → COMPLETE
//
//          * PULL pulls one beat per cycle from w_buf via beat_pull_strb,
//            buffering data + strb into a per-burst staging register
//            array of depth MAX_BURST_LEN.
//          * WAIT counts down t_phy_wrlat_i cycles (PHY-defined latency
//            from WRITE command to wrdata_en assertion).
//          * DRIVE produces one DFI cycle per MC cycle: each DFI word
//            packs DFI_RATE DRAM beats from the staging buffer. The
//            last DFI cycle of a non-multiple burst is masked off via
//            dfi_wrdata_mask (DFI mask=1 means do-not-write).
//          * COMPLETE pulses b_complete_strb to the wr CAM.
//
// AXI ↔ DFI mask polarity:
//          AXI wstrb=1 means "write this byte". DFI mask=1 means
//          "MASK this byte (don't write)". So dfi_wrdata_mask = ~wstrb.
//
// v1 limitations — see TODO markers:
//   (TODO multi-outstanding) Single in-flight write at a time. The wr
//   CAM allows up to WR_CAM_DEPTH=16 concurrent slots; v2 should add
//   per-slot context so multiple ops can be pulled/driven concurrently.
//
//   (TODO streaming) PULL→WAIT→DRIVE is sequential. For bursts where
//   `len` > `t_phy_wrlat_i`, DRIVE happens later than the PHY-required
//   t_phy_wrlat cycles after the WRITE command. Real silicon requires
//   pre-pull during the scheduler's pipeline latency, or a wider
//   wbuf_ext_rd_data port (DFI_RATE beats per cycle). TB stubs must be
//   permissive about this offset until streaming pre-pull lands.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wr_beat_sequencer
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int W_BUF_PTR_WIDTH = 7,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_RATE        = 2,                                // 2 or 4
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DRAM_STRB_WIDTH = DRAM_BEAT_WIDTH / 8,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = 1,
    parameter int MAX_BURST_LEN   = 256,

    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int RATE_LOG2 = $clog2(DFI_RATE)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- timing (CSR-loaded after PHY init) -----
    input  logic [3:0]                 cwl_i,            // CAS write latency (informational; unused in v1)
    input  logic [7:0]                 t_phy_wrlat_i,    // PHY wrdata_en latency from WRITE command

    // ----- write-op handshake from scheduler -----
    input  logic                       op_valid_i,
    output logic                       op_ready_o,
    input  logic [WSL-1:0]             op_slot_i,
    input  logic [BLW-1:0]             op_len_i,

    // ----- pull beats out of axi_frontend's w_buf -----
    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    input  logic [DRAM_BEAT_WIDTH-1:0] wbuf_rd_data_i,
    input  logic [DRAM_STRB_WIDTH-1:0] wbuf_rd_strb_i,

    // ----- DFI write data interface -----
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,

    // ----- b_complete back to wr CAM -----
    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o
);

    //=========================================================================
    // FSM states
    //=========================================================================
    typedef enum logic [2:0] {
        S_IDLE     = 3'd0,
        S_PULL     = 3'd1,
        S_WAIT     = 3'd2,
        S_DRIVE    = 3'd3,
        S_COMPLETE = 3'd4
    } state_e;

    state_e         r_state;

    // Per-burst context
    logic [WSL-1:0] r_cur_slot;
    logic [BLW-1:0] r_cur_len;
    logic [BLW-1:0] r_beats_pulled;
    logic [BLW-1:0] r_dfi_cycle_cnt;
    logic [7:0]     r_wait_cnt;

    // Staging buffer (per-burst). For MAX_BURST_LEN=256 and DRAM_BEAT_WIDTH=64
    // this is 16 Kbit per slot — synth-mappable to distributed/block RAM.
    logic [DRAM_BEAT_WIDTH-1:0] r_stage_data [MAX_BURST_LEN];
    logic [DRAM_STRB_WIDTH-1:0] r_stage_strb [MAX_BURST_LEN];

    //=========================================================================
    // Pre-compute DFI cycles needed for the current burst.
    // ceil(len / DFI_RATE) when DFI_RATE is a power of two.
    //=========================================================================
    logic [BLW:0] w_dfi_cycles_total;
    assign w_dfi_cycles_total = ({1'b0, r_cur_len} + (BLW+1)'(DFI_RATE - 1))
                              >> RATE_LOG2;

    //=========================================================================
    // Sequential FSM
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state         <= S_IDLE;
            r_cur_slot      <= '0;
            r_cur_len       <= '0;
            r_beats_pulled  <= '0;
            r_dfi_cycle_cnt <= '0;
            r_wait_cnt      <= '0;
        end else begin
            unique case (r_state)

                S_IDLE: begin
                    if (op_valid_i && op_ready_o) begin
                        r_cur_slot     <= op_slot_i;
                        r_cur_len      <= op_len_i;
                        r_beats_pulled <= '0;
                        r_state        <= S_PULL;
                    end
                end

                S_PULL: begin
                    // Latch is gated on the REGISTERED `beat_pull_strb_o`
                    // so the wr CAM has a cycle to respond after seeing
                    // the strobe on its input port. (With combinational
                    // strb_o this gating wasn't necessary.)
                    if (beat_pull_strb_o) begin
                        r_stage_data[r_beats_pulled[$clog2(MAX_BURST_LEN)-1:0]]
                            <= wbuf_rd_data_i;
                        r_stage_strb[r_beats_pulled[$clog2(MAX_BURST_LEN)-1:0]]
                            <= wbuf_rd_strb_i;
                        r_beats_pulled <= r_beats_pulled + BLW'(1);
                        if (beat_pull_last_i) begin
                            r_state    <= S_WAIT;
                            r_wait_cnt <= t_phy_wrlat_i;
                        end
                    end
                end

                S_WAIT: begin
                    if (r_wait_cnt == 8'd0) begin
                        r_state         <= S_DRIVE;
                        r_dfi_cycle_cnt <= '0;
                    end else begin
                        r_wait_cnt <= r_wait_cnt - 8'd1;
                    end
                end

                S_DRIVE: begin
                    r_dfi_cycle_cnt <= r_dfi_cycle_cnt + BLW'(1);
                    if ((r_dfi_cycle_cnt + BLW'(1)) == BLW'(w_dfi_cycles_total)) begin
                        r_state <= S_COMPLETE;
                    end
                end

                S_COMPLETE: begin
                    r_state <= S_IDLE;
                end

                default: r_state <= S_IDLE;
            endcase
        end
    end)

    //=========================================================================
    // Next-cycle outputs — combinational on r_state.
    //=========================================================================
    localparam int MAX_LOG2 = $clog2(MAX_BURST_LEN);

    // Precompute the per-lane beat indices and validity mask outside
    // the always_comb (Verilator latch warning workaround).
    logic [BLW:0]        w_beat_idx_full [DFI_RATE];
    logic [MAX_LOG2-1:0] w_beat_idx      [DFI_RATE];
    logic                w_beat_in_burst [DFI_RATE];
    for (genvar r = 0; r < DFI_RATE; r++) begin : g_pack_idx
        assign w_beat_idx_full[r] = ({1'b0, r_dfi_cycle_cnt} << RATE_LOG2)
                                  + (BLW+1)'(r);
        assign w_beat_idx[r]      = w_beat_idx_full[r][MAX_LOG2-1:0];
        assign w_beat_in_burst[r] = (w_beat_idx_full[r] < {1'b0, r_cur_len});
    end

    logic [DFI_DATA_WIDTH-1:0] w_dfi_wrdata;
    logic [DFI_STRB_WIDTH-1:0] w_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]   w_dfi_wrdata_en;
    always_comb begin
        w_dfi_wrdata      = '0;
        w_dfi_wrdata_mask = '1;
        w_dfi_wrdata_en   = '0;
        if (r_state == S_DRIVE) begin
            w_dfi_wrdata_en = '1;
            for (int unsigned r = 0; r < DFI_RATE; r++) begin
                if (w_beat_in_burst[r]) begin
                    w_dfi_wrdata[r*DRAM_BEAT_WIDTH +: DRAM_BEAT_WIDTH]
                        = r_stage_data[w_beat_idx[r]];
                    w_dfi_wrdata_mask[r*DRAM_STRB_WIDTH +: DRAM_STRB_WIDTH]
                        = ~r_stage_strb[w_beat_idx[r]];
                end
            end
        end
    end

    //=========================================================================
    // Strict-flop outputs.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            op_ready_o        <= 1'b1;
            beat_pull_strb_o  <= 1'b0;
            beat_pull_slot_o  <= '0;
            dfi_wrdata_o      <= '0;
            dfi_wrdata_mask_o <= '1;
            dfi_wrdata_en_o   <= '0;
            b_complete_strb_o <= 1'b0;
            b_complete_slot_o <= '0;
        end else begin
            op_ready_o        <= (r_state == S_IDLE);
            beat_pull_strb_o  <= (r_state == S_PULL);
            beat_pull_slot_o  <= r_cur_slot;
            dfi_wrdata_o      <= w_dfi_wrdata;
            dfi_wrdata_mask_o <= w_dfi_wrdata_mask;
            dfi_wrdata_en_o   <= w_dfi_wrdata_en;
            b_complete_strb_o <= (r_state == S_COMPLETE);
            b_complete_slot_o <= r_cur_slot;
        end
    end)

    // Signals not consumed by v1 but kept on the port list for parity with
    // future implementations (streaming pre-pull, CWL sanity checks).
    wire unused_v1 = |{ cwl_i, beat_pull_ptr_i, beat_pull_strb_ptr_i };

endmodule : wr_beat_sequencer
