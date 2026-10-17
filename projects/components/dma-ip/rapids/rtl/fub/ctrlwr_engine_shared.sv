// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ctrlwr_engine_shared
// Purpose: One control-write engine serving every channel of a RAPIDS half
//
// Description:
//   One ctrlwr_engine plus scheduler-side arbitration, in place of one engine
//   per channel; the same structure as ctrlrd_engine_shared:
//     - round-robin pick, offered only while the engine is idle and its last
//       MonBus packet has drained;
//     - owner register set on accept;
//     - the owner sees the engine's idle and error, others see idle=1,
//       error=0.
//   The AXI write master is owned outright: AWID carries the owner channel and
//   every B belongs to the engine. One write in flight at a time, which the
//   old array-level serializer also enforced.
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_mas/
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

`include "reset_defs.svh"
`include "rapids_imports.svh"

module ctrlwr_engine_shared #(
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH   = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH   = 64,
    parameter int AXI_ID_WIDTH = 8,
    parameter logic [15:0] MON_AGENT_BASE = 16'h0028,   // agent = base + channel
    parameter logic [7:0]  MON_UNIT_ID    = 8'h01,
    parameter int NC = NUM_CHANNELS,
    parameter int CW = CHAN_WIDTH
) (
    input  logic                              clk,
    input  logic                              rst_n,

    input  logic [NC-1:0]                     ctrlwr_valid,
    output logic [NC-1:0]                     ctrlwr_ready,
    input  logic [NC-1:0][ADDR_WIDTH-1:0]     ctrlwr_addr,
    input  logic [NC-1:0][31:0]               ctrlwr_data,
    output logic [NC-1:0]                     ctrlwr_error,
    output logic [NC-1:0]                     ctrlwr_idle,

    input  logic [NC-1:0]                     cfg_channel_reset,

    output logic                              aw_valid,
    input  logic                              aw_ready,
    output logic [ADDR_WIDTH-1:0]             aw_addr,
    output logic [7:0]                        aw_len,
    output logic [2:0]                        aw_size,
    output logic [1:0]                        aw_burst,
    output logic [AXI_ID_WIDTH-1:0]           aw_id,
    output logic                              aw_lock,
    output logic [3:0]                        aw_cache,
    output logic [2:0]                        aw_prot,
    output logic [3:0]                        aw_qos,
    output logic [3:0]                        aw_region,
    output logic                              w_valid,
    input  logic                              w_ready,
    output logic [31:0]                       w_data,
    output logic [3:0]                        w_strb,
    output logic                              w_last,
    input  logic                              b_valid,
    output logic                              b_ready,
    input  logic [AXI_ID_WIDTH-1:0]           b_id,
    input  logic [1:0]                        b_resp,

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

    // Offer only to an idle engine with no packet waiting and no error left
    // over from the previous owner (r_clear wipes a stale error first; see
    // ctrlrd_engine_shared).
    assign w_offer = w_eng_idle && !r_busy && !mon_valid && !w_eng_error && !r_clear;

    always_comb begin
        w_pick_valid = 1'b0;
        w_pick       = r_rr_ptr;
        for (int k = 1; k <= NC; k++) begin
            int idx;
            idx = (int'(r_rr_ptr) + k) % NC;
            if (!w_pick_valid && ctrlwr_valid[idx]) begin
                w_pick_valid = 1'b1;
                w_pick       = CW'(idx);
            end
        end
    end

    assign w_eng_valid = w_offer && w_pick_valid;
    assign w_accept    = w_eng_valid && w_eng_ready;

    always_comb begin
        ctrlwr_ready = '0;
        if (w_offer && w_pick_valid) ctrlwr_ready[w_pick] = w_eng_ready;
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

    // Owner reset only while its op is in flight; see ctrlrd_engine_shared.
    assign w_eng_reset = (r_busy && cfg_channel_reset[r_owner]) || r_clear;

    always_comb begin
        for (int c = 0; c < NC; c++) begin
            ctrlwr_idle[c]  = (r_owner_valid && (r_owner == CW'(c))) ? w_eng_idle  : 1'b1;
            ctrlwr_error[c] = (r_owner_valid && (r_owner == CW'(c))) ? w_eng_error : 1'b0;
        end
    end

    ctrlwr_engine #(
        .CHANNEL_ID     (0),
        .NUM_CHANNELS   (NC),
        .CHAN_WIDTH     (CW),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .MON_AGENT_ID   (MON_AGENT_BASE),
        .MON_UNIT_ID    (MON_UNIT_ID),
        .MON_CHANNEL_ID (9'h000)
    ) u_engine (
        .clk                (clk),
        .rst_n              (rst_n),
        .ctrlwr_valid       (w_eng_valid),
        .ctrlwr_ready       (w_eng_ready),
        .ctrlwr_pkt_addr    (ctrlwr_addr[w_pick]),
        .ctrlwr_pkt_data    (ctrlwr_data[w_pick]),
        .ctrlwr_error       (w_eng_error),
        .cfg_channel_reset  (w_eng_reset),
        .ctrlwr_engine_idle (w_eng_idle),
        .aw_valid           (aw_valid),
        .aw_ready           (aw_ready),
        .aw_addr            (aw_addr),
        .aw_len             (aw_len),
        .aw_size            (aw_size),
        .aw_burst           (aw_burst),
        /* verilator lint_off PINCONNECTEMPTY */
        .aw_id              (),
        /* verilator lint_on PINCONNECTEMPTY */
        .aw_lock            (aw_lock),
        .aw_cache           (aw_cache),
        .aw_prot            (aw_prot),
        .aw_qos             (aw_qos),
        .aw_region          (aw_region),
        .w_valid            (w_valid),
        .w_ready            (w_ready),
        .w_data             (w_data),
        .w_strb             (w_strb),
        .w_last             (w_last),
        .b_valid            (b_valid),
        .b_ready            (b_ready),
        .b_id               ('0),          // every B is the engine's
        .b_resp             (b_resp),
        .i_mon_time         (i_mon_time),
        .mon_valid          (mon_valid),
        .mon_ready          (mon_ready),
        .mon_packet         (w_eng_mon_packet),
        .mon_timestamp      (mon_timestamp)
    );

    assign aw_id = AXI_ID_WIDTH'(r_owner);

    always_comb begin
        mon_packet        = w_eng_mon_packet;
        mon_packet[96:88] = 9'(r_owner);
        mon_packet[87:72] = MON_AGENT_BASE + 16'(r_owner);
    end

    logic unused_ok;
    assign unused_ok = &{1'b0, b_id};

endmodule : ctrlwr_engine_shared
