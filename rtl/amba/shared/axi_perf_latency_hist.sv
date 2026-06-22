// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Module: axi_perf_latency_hist
// Purpose: Per-transaction AXI latency histogram (RFC perfmon Stage D).
//
// Documentation: rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md
// Subsystem: amba
//
// Captures per-transaction latency on an AXI master bus and bins it into a
// log2 histogram, surfaced via CSR-indexed readout (no MonBus packets). This
// is a self-contained snoop block (it does NOT gate the AXI path) instantiated
// alongside the datapath monitors -- it deliberately leaves the shared
// axi_monitor_base untouched.
//
// Metrics:
//   IS_READ=1 : metric 0 = AR handshake -> first R beat
//               metric 1 = AR handshake -> RLAST beat
//   IS_READ=0 : metric 0 = AW handshake -> B response
//
// Transaction matching: AXI requires same-ID responses in order, so a per-
// channel (channel = id[CW-1:0]) FIFO of command-phase timestamps matches each
// completion to its oldest outstanding command. A single AXI data/response bus
// carries at most one beat per cycle, so at most one push and one pop occur per
// cycle -- no multi-writer hazard on the shared histogram.
//
// Window control mirrors axi_bus_meter: i_clear (one-cycle pulse on the perf
// RUN rising edge) resets the histogram + FIFOs; i_freeze (~RUN) holds the
// histogram so a closed window can be read back. The free-running timestamp
// counter is NOT frozen so latencies straddling the close boundary stay correct.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_perf_latency_hist #(
    parameter int ID_WIDTH        = 8,
    parameter int NUM_CHANNELS    = 8,
    parameter int MAX_OUTSTANDING = 8,      // per-channel timestamp FIFO depth
    parameter int NUM_BINS        = 16,     // log2 bins: bin b counts [2^b, 2^(b+1))
    parameter bit IS_READ         = 1'b1,   // 1 = read (2 metrics), 0 = write (1 metric)
    parameter int CNT_W           = 32,
    // Derived
    parameter int CW   = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int PW   = (MAX_OUTSTANDING > 1) ? $clog2(MAX_OUTSTANDING) : 1,
    parameter int PW1  = PW + 1,
    parameter int BINW = (NUM_BINS > 1) ? $clog2(NUM_BINS) : 1
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    // Window control (drive from the perf RUN bit, same as axi_bus_meter)
    input  logic                 i_clear,    // one-cycle: reset histogram + FIFOs
    input  logic                 i_freeze,   // hold histogram (counters stop)

    // Command channel (AR for reads, AW for writes)
    input  logic                 cmd_valid,
    input  logic                 cmd_ready,
    input  logic [ID_WIDTH-1:0]  cmd_id,

    // Read data channel (R) -- used when IS_READ=1
    input  logic                 data_valid,
    input  logic                 data_ready,
    input  logic                 data_last,
    input  logic [ID_WIDTH-1:0]  data_id,

    // Write response channel (B) -- used when IS_READ=0
    input  logic                 resp_valid,
    input  logic                 resp_ready,
    input  logic [ID_WIDTH-1:0]  resp_id,

    // CSR-indexed readout
    input  logic                 i_hist_metric,        // 0 or 1 (1 = RLAST, reads only)
    input  logic [BINW-1:0]      i_hist_bin,           // which bin to read
    output logic [CNT_W-1:0]     o_hist_count,         // selected bin count
    output logic [CNT_W-1:0]     o_hist_total          // selected metric's total txns
);

    localparam int NUM_METRICS = IS_READ ? 2 : 1;

    // Free-running timestamp (NOT frozen -- absolute cycle clock).
    logic [31:0] r_time;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_time <= 32'h0;
        else                        r_time <= r_time + 32'h1;
    )

    // log2 bin: floor(log2(lat)) clamped to NUM_BINS-1. lat=0,1 -> bin 0.
    function automatic logic [BINW-1:0] latency_bin(input logic [31:0] lat);
        latency_bin = '0;
        for (int b = 0; b < NUM_BINS; b++)
            if (lat >= (32'h1 << b)) latency_bin = b[BINW-1:0];
    endfunction

    // Per-channel timestamp FIFO (command-phase start times).
    logic [31:0]   r_ts   [NUM_CHANNELS][MAX_OUTSTANDING];
    logic [PW-1:0] r_head [NUM_CHANNELS];
    logic [PW-1:0] r_tail [NUM_CHANNELS];
    logic [PW:0]   r_cnt  [NUM_CHANNELS];   // occupancy (extra bit for full)
    logic          r_burst_active [NUM_CHANNELS];  // read: first-R already seen

    // Histogram [metric][bin] + per-metric totals. Always size 2 metrics for
    // uniform indexing; the write build only uses metric 0.
    logic [CNT_W-1:0] r_hist  [2][NUM_BINS];
    logic [CNT_W-1:0] r_total [2];

    // Decoded channels + handshakes
    logic [CW-1:0] w_ch_cmd, w_ch_dat, w_ch_resp;
    logic          w_cmd_hs, w_dat_hs, w_resp_hs;
    assign w_ch_cmd  = cmd_id [CW-1:0];
    assign w_ch_dat  = data_id[CW-1:0];
    assign w_ch_resp = resp_id[CW-1:0];
    assign w_cmd_hs  = cmd_valid  && cmd_ready;
    assign w_dat_hs  = IS_READ  && data_valid && data_ready;
    assign w_resp_hs = !IS_READ && resp_valid && resp_ready;

    // Completion channel + start timestamp (read: data; write: resp).
    logic [CW-1:0] w_ch_done;
    logic          w_done_hs, w_done_last;
    assign w_ch_done   = IS_READ ? w_ch_dat : w_ch_resp;
    assign w_done_hs   = IS_READ ? w_dat_hs : w_resp_hs;
    assign w_done_last = IS_READ ? data_last : 1'b1;   // writes: B is always "last"

    // Start timestamp of the oldest outstanding command on the completing
    // channel (the latency subtract is done in the pipeline below, not here).
    logic [31:0] w_start_ts;
    assign w_start_ts = r_ts[w_ch_done][r_head[w_ch_done]];

    // First-beat detect for reads (metric 0 = AR->first R). For writes the only
    // metric (0) is recorded at the B handshake directly.
    logic w_first_beat;
    assign w_first_beat = IS_READ ? (w_dat_hs && !r_burst_active[w_ch_dat])
                                   : w_resp_hs;

    // FIFO push/pop qualifiers.
    logic w_push, w_pop;
    assign w_push = w_cmd_hs  && (r_cnt[w_ch_cmd]  <  PW1'(MAX_OUTSTANDING));
    assign w_pop  = w_done_hs && w_done_last && (r_cnt[w_ch_done] != '0);

    // Completion event this cycle (FIFO non-empty) + its metric flags.
    //   m0 = first R beat (reads) / B response (writes)
    //   m1 = RLAST (reads only)
    logic w_ev_m0, w_ev_m1, w_ev;
    assign w_ev_m0 = w_first_beat && (r_cnt[w_ch_done] != '0);
    assign w_ev_m1 = IS_READ && w_done_hs && w_done_last && (r_cnt[w_ch_done] != '0);
    assign w_ev    = w_ev_m0 || w_ev_m1;

    // -------------------------------------------------------------------------
    // Histogram update pipeline (FPGA timing closure). The chain FIFO-read ->
    // latency subtract -> log2 bin -> indexed histogram increment is far too
    // deep for one cycle (it was the routed critical path), so it is split into
    // 4 register stages: s0 captures {start_ts, time, metric flags}; s1 does the
    // subtract; s2 the log2 bin; s3 the increment. The increment is delayed a
    // few cycles, but the host reads the window long after RUN->0, by which time
    // the pipeline has drained (i_freeze gates s0 capture; s1..s3 keep advancing
    // to flush). A single AXI bus completes <=1 transaction/cycle and m0/m1 hit
    // different histograms, so consecutive same-bin increments are hazard-free
    // (cross-cycle NBA read-after-write is correct).
    // -------------------------------------------------------------------------
    logic            s0_valid, s0_m0, s0_m1;
    logic [31:0]     s0_start_ts, s0_time;
    logic            s1_valid, s1_m0, s1_m1;
    logic [31:0]     s1_lat;
    logic            s2_valid, s2_m0, s2_m1;
    logic [BINW-1:0] s2_bin;

    integer ci, bi;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn || i_clear) begin
            // Reset on hard reset or window open (RUN rising edge / i_clear).
            for (ci = 0; ci < NUM_CHANNELS; ci++) begin
                r_head[ci]         <= '0;
                r_tail[ci]         <= '0;
                r_cnt[ci]          <= '0;
                r_burst_active[ci] <= 1'b0;
            end
            for (ci = 0; ci < 2; ci++) begin
                r_total[ci] <= '0;
                for (bi = 0; bi < NUM_BINS; bi++) r_hist[ci][bi] <= '0;
            end
            s0_valid <= 1'b0; s0_m0 <= 1'b0; s0_m1 <= 1'b0;
            s1_valid <= 1'b0; s1_m0 <= 1'b0; s1_m1 <= 1'b0;
            s2_valid <= 1'b0; s2_m0 <= 1'b0; s2_m1 <= 1'b0;
            s0_start_ts <= '0; s0_time <= '0; s1_lat <= '0; s2_bin <= '0;
        end else begin
            // ---- FIFO management (single cycle, gated by freeze) ----
            if (!i_freeze) begin
                if (w_push) begin
                    r_ts[w_ch_cmd][r_tail[w_ch_cmd]] <= r_time;
                    r_tail[w_ch_cmd] <= (r_tail[w_ch_cmd] == PW'(MAX_OUTSTANDING-1))
                                        ? '0 : (r_tail[w_ch_cmd] + PW'(1));
                end
                if (w_ev_m0 && IS_READ) r_burst_active[w_ch_dat] <= 1'b1;
                if (w_pop) begin
                    r_head[w_ch_done] <= (r_head[w_ch_done] == PW'(MAX_OUTSTANDING-1))
                                         ? '0 : (r_head[w_ch_done] + PW'(1));
                    if (IS_READ) r_burst_active[w_ch_done] <= 1'b0;
                end
                if (w_push && w_pop && (w_ch_cmd == w_ch_done)) begin
                    r_cnt[w_ch_cmd] <= r_cnt[w_ch_cmd];  // net unchanged
                end else begin
                    if (w_push) r_cnt[w_ch_cmd]  <= r_cnt[w_ch_cmd]  + PW1'(1);
                    if (w_pop)  r_cnt[w_ch_done] <= r_cnt[w_ch_done] - PW1'(1);
                end
            end

            // ---- Stage 0: capture event (FIFO read result + timestamps) ----
            s0_valid    <= w_ev    && !i_freeze;
            s0_m0       <= w_ev_m0 && !i_freeze;
            s0_m1       <= w_ev_m1 && !i_freeze;
            s0_start_ts <= w_start_ts;   // r_ts[w_ch_done][r_head[w_ch_done]]
            s0_time     <= r_time;

            // ---- Stage 1: latency = completion time - start time ----
            s1_valid <= s0_valid; s1_m0 <= s0_m0; s1_m1 <= s0_m1;
            s1_lat   <= s0_time - s0_start_ts;

            // ---- Stage 2: log2 bin ----
            s2_valid <= s1_valid; s2_m0 <= s1_m0; s2_m1 <= s1_m1;
            s2_bin   <= latency_bin(s1_lat);

            // ---- Stage 3: increment the selected histogram bins + totals ----
            if (s2_valid && s2_m0) begin
                r_hist[0][s2_bin] <= r_hist[0][s2_bin] + CNT_W'(1);
                r_total[0]        <= r_total[0] + CNT_W'(1);
            end
            if (s2_valid && s2_m1) begin
                r_hist[1][s2_bin] <= r_hist[1][s2_bin] + CNT_W'(1);
                r_total[1]        <= r_total[1] + CNT_W'(1);
            end
        end
    end

    // CSR-indexed readout (combinational mux).
    assign o_hist_count = r_hist[i_hist_metric ? 1 : 0][i_hist_bin];
    assign o_hist_total = r_total[i_hist_metric ? 1 : 0];

endmodule : axi_perf_latency_hist
