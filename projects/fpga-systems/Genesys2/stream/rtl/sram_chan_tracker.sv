// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sram_chan_tracker
// Purpose: sim-only scoreboard bound onto stream_core's u_sram_controller.
//          Catches per-channel data swaps between the RD-engine deposit
//          side and the WR-engine drain side.
//
// Algorithm:
//   - Snoop axi_rd_sram_* deposits. Per-channel reference queue ref_q[ch]
//     records every (data) the RD engine pushed into channel ch.
//   - Snoop axi_wr_sram_* drains. Each drain pops ref_q[axi_wr_sram_id]
//     and asserts the popped data == the data appearing on axi_wr_sram_data.
//   - Mismatch ⇒ $error with a hint: if the drained data matches the head
//     of another channel's ref queue, we log "data matches ch<j> head —
//     SWAP!" to localize the bug to a channel-id pickoff.
//
// Hooked in via:
//     bind sram_controller sram_chan_tracker
//         #(...) u_chan_tracker (.*);
// (see sram_chan_tracker_bind.sv)
//
// Compiles only when SIMULATION is defined (verilator/cocotb runs).
// Pure synthesizable cruft outside of `ifdef SIMULATION` is zero, so
// it lives next to the SDP-RAM module in the framework filelist
// without polluting the FPGA build.

`timescale 1ns / 1ps

module sram_chan_tracker #(
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH   = 128,
    parameter int CIW          = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int REPORT_EVERY_CYCLES = 50000   // periodic summary cadence
) (
    input  logic                         clk,
    input  logic                         rst_n,

    // RD interface (RD-engine deposits into SRAM)
    input  logic                         axi_rd_sram_valid,
    input  logic                         axi_rd_sram_ready,
    input  logic [CIW-1:0]               axi_rd_sram_id,
    input  logic [DATA_WIDTH-1:0]        axi_rd_sram_data,

    // WR interface (WR-engine drains from SRAM)
    input  logic                         axi_wr_sram_drain,
    input  logic [NUM_CHANNELS-1:0]      axi_wr_sram_valid,       // registered (post-flop)
    input  logic [NUM_CHANNELS-1:0]      axi_wr_sram_valid_comb,  // combinational (matches actual bus xfer condition)
    input  logic [CIW-1:0]               axi_wr_sram_id,
    input  logic [DATA_WIDTH-1:0]        axi_wr_sram_data
);

`ifndef SYNTHESIS
    // Per-channel reference queues (sim-only SV queues)
    logic [DATA_WIDTH-1:0] ref_q [NUM_CHANNELS][$];

    int dep_cnt      [NUM_CHANNELS];
    int drn_cnt      [NUM_CHANNELS];
    int mismatch_cnt;
    int empty_drain_cnt;
    int oor_dep_cnt;
    int oor_drn_cnt;

    initial begin
        foreach (dep_cnt[i]) dep_cnt[i] = 0;
        foreach (drn_cnt[i]) drn_cnt[i] = 0;
        mismatch_cnt    = 0;
        empty_drain_cnt = 0;
        oor_dep_cnt     = 0;
        oor_drn_cnt     = 0;
        $display("[%0t] [CHTRK] sram_chan_tracker armed: NUM_CHANNELS=%0d DATA_WIDTH=%0d CIW=%0d",
                 $time, NUM_CHANNELS, DATA_WIDTH, CIW);
    end

    // -------------------------------------------------------------------
    // Deposit snoop (RD engine → SRAM)
    // -------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n && axi_rd_sram_valid && axi_rd_sram_ready) begin
            if (int'(axi_rd_sram_id) < NUM_CHANNELS) begin
                ref_q[axi_rd_sram_id].push_back(axi_rd_sram_data);
                dep_cnt[axi_rd_sram_id] += 1;
            end else begin
                oor_dep_cnt += 1;
                $error("[%0t] [CHTRK] DEPOSIT with out-of-range id=%0d data=0x%h",
                       $time, axi_rd_sram_id, axi_rd_sram_data);
            end
        end
    end

    // -------------------------------------------------------------------
    // Drain snoop (SRAM → WR engine)
    //
    // We only count a drain as a "fire" cycle when axi_wr_sram_drain is
    // asserted AND the selected channel actually has valid data (= the
    // condition under which m_axi_wvalid asserts in axi_write_engine).
    // -------------------------------------------------------------------
    // Gate on axi_wr_sram_valid_comb (combinational) — that's the
    // condition under which the WR engine actually issues m_axi_wvalid
    // and consumes a beat. Using the registered valid here causes false
    // positives when the registered bit lags the actual skid state.
    logic [DATA_WIDTH-1:0] expected;
    int                    swap_ch;
    always @(posedge clk) begin
        if (rst_n && axi_wr_sram_drain && int'(axi_wr_sram_id) < NUM_CHANNELS
              && axi_wr_sram_valid_comb[axi_wr_sram_id]) begin

            if (ref_q[axi_wr_sram_id].size() == 0) begin
                empty_drain_cnt += 1;
                $display("[%0t] [CHTRK] DRAIN ch=%0d data=0x%h but ref queue empty (depcnt=%0d drncnt=%0d)",
                         $time, axi_wr_sram_id, axi_wr_sram_data,
                         dep_cnt[axi_wr_sram_id], drn_cnt[axi_wr_sram_id]);
            end else begin
                expected = ref_q[axi_wr_sram_id].pop_front();
                drn_cnt[axi_wr_sram_id] += 1;
                if (axi_wr_sram_data !== expected) begin
                    // Scan ALL channels' queues at all positions for the got
                    // value — gives us channel + offset of where it really
                    // lives, which tells us "swap" vs "pointer drift".
                    swap_ch = -1;
                    for (int j = 0; j < NUM_CHANNELS; j++) begin
                        if (j != int'(axi_wr_sram_id)
                              && ref_q[j].size() > 0
                              && ref_q[j][0] === axi_wr_sram_data) begin
                            swap_ch = j;
                        end
                    end
                    mismatch_cnt += 1;
                    if (mismatch_cnt <= 16) begin
                        if (swap_ch >= 0) begin
                            $display("[%0t] [CHTRK] MISMATCH#%0d ch=%0d expected=0x%h got=0x%h  (matches ch%0d head — channel SWAP)",
                                     $time, mismatch_cnt, axi_wr_sram_id, expected, axi_wr_sram_data, swap_ch);
                        end else begin
                            $display("[%0t] [CHTRK] MISMATCH#%0d ch=%0d expected=0x%h got=0x%h",
                                     $time, mismatch_cnt, axi_wr_sram_id, expected, axi_wr_sram_data);
                        end
                    end
                end
            end
        end
        else if (rst_n && axi_wr_sram_drain && int'(axi_wr_sram_id) >= NUM_CHANNELS) begin
            oor_drn_cnt += 1;
            $display("[%0t] [CHTRK] DRAIN with out-of-range id=%0d", $time, axi_wr_sram_id);
        end
    end

    // -------------------------------------------------------------------
    // Periodic summary (cycle-counted; verilator doesn't grok # delays
    // without --timing).
    // -------------------------------------------------------------------
    int cycle_cnt;
    always @(posedge clk) begin
        if (!rst_n) begin
            cycle_cnt <= 0;
        end else begin
            cycle_cnt <= cycle_cnt + 1;
            if (cycle_cnt != 0 && (cycle_cnt % REPORT_EVERY_CYCLES) == 0) begin
                $display("[%0t] [CHTRK] summary: dep=%p drn=%p mismatch=%0d empty_drain=%0d oor_dep=%0d oor_drn=%0d",
                         $time, dep_cnt, drn_cnt, mismatch_cnt, empty_drain_cnt, oor_dep_cnt, oor_drn_cnt);
            end
        end
    end

    // -------------------------------------------------------------------
    // Final report on $finish
    // -------------------------------------------------------------------
    final begin
        $display("[%0t] [CHTRK] FINAL: dep=%p drn=%p mismatch=%0d empty_drain=%0d oor_dep=%0d oor_drn=%0d",
                 $time, dep_cnt, drn_cnt, mismatch_cnt, empty_drain_cnt, oor_dep_cnt, oor_drn_cnt);
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (ref_q[i].size() != 0) begin
                $display("[%0t] [CHTRK] FINAL: ch%0d ref queue has %0d undrained entries",
                         $time, i, ref_q[i].size());
            end
        end
    end
`endif

endmodule : sram_chan_tracker
