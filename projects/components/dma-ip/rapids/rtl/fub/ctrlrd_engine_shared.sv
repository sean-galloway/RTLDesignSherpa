// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ctrlrd_engine_shared
// Purpose: One control-read engine serving every channel of a RAPIDS half
//
// Description:
//   One ctrlrd_engine plus scheduler-side arbitration, in place of one engine
//   per channel. The engine runs one request at a time, so sharing it needs
//   only three things around it:
//     - a round-robin pick among the channels' requests, offered to the engine
//       only while it is idle and its last MonBus packet has drained, so the
//       owner never changes under an operation;
//     - an owner register, set when the engine accepts a request;
//     - a per-channel view: the owner sees the engine's idle and error
//       exactly as a dedicated engine would show them; every other channel
//       sees idle=1, error=0.
//   The AXI master is owned outright (no arbiter behind it): ARID carries the
//   owner channel, and every R beat belongs to the engine. MonBus packets are
//   re-tagged with the owner's channel and agent ID.
//
//   Trade-off: a CTRL_READ poll that retries holds the engine, so other
//   channels' control reads wait behind it (data transfers are unaffected).
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_mas/
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

`include "reset_defs.svh"
`include "rapids_imports.svh"

module ctrlrd_engine_shared #(
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH   = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH   = 64,
    parameter int AXI_ID_WIDTH = 8,
    parameter logic [15:0] MON_AGENT_BASE = 16'h0020,   // agent = base + channel
    parameter logic [7:0]  MON_UNIT_ID    = 8'h01,
    parameter int NC = NUM_CHANNELS,
    parameter int CW = CHAN_WIDTH
) (
    input  logic                              clk,
    input  logic                              rst_n,

    // Per-channel scheduler requests
    input  logic [NC-1:0]                     ctrlrd_valid,
    output logic [NC-1:0]                     ctrlrd_ready,
    input  logic [NC-1:0][ADDR_WIDTH-1:0]     ctrlrd_addr,
    input  logic [NC-1:0][31:0]               ctrlrd_data,
    input  logic [NC-1:0][31:0]               ctrlrd_mask,
    output logic [NC-1:0]                     ctrlrd_error,
    output logic [NC-1:0]                     ctrlrd_idle,

    input  logic [8:0]                        cfg_ctrlrd_max_try,
    input  logic [NC-1:0]                     cfg_channel_reset,
    input  logic                              tick_1us,

    // AXI4 read master (owned; 32-bit data)
    output logic                              ar_valid,
    input  logic                              ar_ready,
    output logic [ADDR_WIDTH-1:0]             ar_addr,
    output logic [7:0]                        ar_len,
    output logic [2:0]                        ar_size,
    output logic [1:0]                        ar_burst,
    output logic [AXI_ID_WIDTH-1:0]           ar_id,
    output logic                              ar_lock,
    output logic [3:0]                        ar_cache,
    output logic [2:0]                        ar_prot,
    output logic [3:0]                        ar_qos,
    output logic [3:0]                        ar_region,
    input  logic                              r_valid,
    output logic                              r_ready,
    input  logic [31:0]                       r_data,
    input  logic [AXI_ID_WIDTH-1:0]           r_id,
    input  logic [1:0]                        r_resp,
    input  logic                              r_last,

    input  monitor_common_pkg::monbus_timestamp_t  i_mon_time,
    output logic                                   mon_valid,
    input  logic                                   mon_ready,
    output monitor_common_pkg::monitor_packet_t    mon_packet,
    output monitor_common_pkg::monbus_timestamp_t  mon_timestamp
);

    logic           w_eng_valid, w_eng_ready, w_eng_error, w_eng_idle;
    logic           w_eng_reset;
    logic [CW-1:0]  r_owner;
    logic           r_owner_valid;
    logic           r_busy, r_seen_busy;
    logic           w_offer;
    logic           w_pick_valid;
    logic [CW-1:0]  w_pick;
    logic [CW-1:0]  r_rr_ptr;
    logic           w_accept;
    logic           r_clear;     // one-cycle engine reset that clears a stale error
    monitor_common_pkg::monitor_packet_t w_eng_mon_packet;

    // Offer a request only to an idle engine with no packet waiting and no
    // error left over from the previous owner. The engine keeps its error
    // until its next success or a reset, so a stale one would fail the next
    // channel the moment it took ownership; r_clear wipes it first.
    assign w_offer = w_eng_idle && !r_busy && !mon_valid && !w_eng_error && !r_clear;

    always_comb begin
        w_pick_valid = 1'b0;
        w_pick       = r_rr_ptr;
        for (int k = 1; k <= NC; k++) begin
            int idx;
            idx = (int'(r_rr_ptr) + k) % NC;
            if (!w_pick_valid && ctrlrd_valid[idx]) begin
                w_pick_valid = 1'b1;
                w_pick       = CW'(idx);
            end
        end
    end

    assign w_eng_valid = w_offer && w_pick_valid;
    assign w_accept    = w_eng_valid && w_eng_ready;

    always_comb begin
        ctrlrd_ready = '0;
        if (w_offer && w_pick_valid) ctrlrd_ready[w_pick] = w_eng_ready;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_owner       <= '0;
            r_owner_valid <= 1'b0;
            r_busy        <= 1'b0;
            r_seen_busy   <= 1'b0;
            r_rr_ptr      <= '0;
            r_clear       <= 1'b0;
        end else begin
            // A request is waiting behind a stale error: pulse the engine
            // reset (its error clears through r_channel_reset_active).
            r_clear <= !r_busy && w_eng_error && w_pick_valid && !r_clear;

            // The owner's reset after its op finished only drops ownership,
            // so the stale view cannot linger and the engine is not held.
            if (!r_busy && r_owner_valid && cfg_channel_reset[r_owner])
                r_owner_valid <= 1'b0;

            if (w_accept) begin
                r_owner       <= w_pick;
                r_owner_valid <= 1'b1;
                r_busy        <= 1'b1;
                r_seen_busy   <= 1'b0;
                r_rr_ptr      <= w_pick;
            end else if (r_busy) begin
                if (!w_eng_idle)                r_seen_busy <= 1'b1;
                if ((r_seen_busy && w_eng_idle) || w_eng_reset) begin
                    r_busy      <= 1'b0;
                    r_seen_busy <= 1'b0;
                end
            end
        end
    )

    // The owner's channel reset resets the engine only while its op is in
    // flight: a channel parked in reset must not hold the engine (and so
    // every other channel's control ops) in reset.
    assign w_eng_reset = (r_busy && cfg_channel_reset[r_owner]) || r_clear;

    always_comb begin
        for (int c = 0; c < NC; c++) begin
            ctrlrd_idle[c]  = (r_owner_valid && (r_owner == CW'(c))) ? w_eng_idle  : 1'b1;
            ctrlrd_error[c] = (r_owner_valid && (r_owner == CW'(c))) ? w_eng_error : 1'b0;
        end
    end

    ctrlrd_engine #(
        .CHANNEL_ID     (0),
        .NUM_CHANNELS   (NC),
        .CHAN_WIDTH     (CW),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .AXI_DATA_WIDTH (32),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .MON_AGENT_ID   (MON_AGENT_BASE),
        .MON_UNIT_ID    (MON_UNIT_ID),
        .MON_CHANNEL_ID (9'h000)
    ) u_engine (
        .clk                (clk),
        .rst_n              (rst_n),
        .ctrlrd_valid       (w_eng_valid),
        .ctrlrd_ready       (w_eng_ready),
        .ctrlrd_pkt_addr    (ctrlrd_addr[w_pick]),
        .ctrlrd_pkt_data    (ctrlrd_data[w_pick]),
        .ctrlrd_pkt_mask    (ctrlrd_mask[w_pick]),
        .ctrlrd_error       (w_eng_error),
        /* verilator lint_off PINCONNECTEMPTY */
        .ctrlrd_result      (),
        /* verilator lint_on PINCONNECTEMPTY */
        .cfg_ctrlrd_max_try (cfg_ctrlrd_max_try),
        .cfg_channel_reset  (w_eng_reset),
        .tick_1us           (tick_1us),
        .ctrlrd_engine_idle (w_eng_idle),
        .ar_valid           (ar_valid),
        .ar_ready           (ar_ready),
        .ar_addr            (ar_addr),
        .ar_len             (ar_len),
        .ar_size            (ar_size),
        .ar_burst           (ar_burst),
        /* verilator lint_off PINCONNECTEMPTY */
        .ar_id              (),
        /* verilator lint_on PINCONNECTEMPTY */
        .ar_lock            (ar_lock),
        .ar_cache           (ar_cache),
        .ar_prot            (ar_prot),
        .ar_qos             (ar_qos),
        .ar_region          (ar_region),
        .r_valid            (r_valid),
        .r_ready            (r_ready),
        .r_data             (r_data),
        .r_id               ('0),          // every beat is the engine's
        .r_resp             (r_resp),
        .r_last             (r_last),
        .i_mon_time         (i_mon_time),
        .mon_valid          (mon_valid),
        .mon_ready          (mon_ready),
        .mon_packet         (w_eng_mon_packet),
        .mon_timestamp      (mon_timestamp)
    );

    assign ar_id = AXI_ID_WIDTH'(r_owner);

    // Re-tag the engine's packets: channel_id [96:88], agent_id [87:72]
    always_comb begin
        mon_packet        = w_eng_mon_packet;
        mon_packet[96:88] = 9'(r_owner);
        mon_packet[87:72] = MON_AGENT_BASE + 16'(r_owner);
    end

    logic unused_ok;
    assign unused_ok = &{1'b0, r_id};

endmodule : ctrlrd_engine_shared
