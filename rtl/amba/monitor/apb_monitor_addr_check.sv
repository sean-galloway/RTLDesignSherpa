// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_monitor_addr_check
// Purpose: Configurable N-range address-violation checker for APB monitors
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba

`timescale 1ns / 1ps

`include "reset_defs.svh"

/**
 * APB Monitor — Address-Range Violation Checker
 *
 * Mirror of axi_monitor_addr_check for the APB monitor pipeline. Watches
 * the cmd_valid/cmd_ready handshake the apb4_monitor already snoops and
 * emits a PktTypeError packet with event code APB_ERR_ADDR_RANGE (8'h08)
 * when an accepted command's paddr falls within any of N configured
 * [low, high] inclusive ranges.
 *
 * Encoding (128-bit packet, 64-bit event_data):
 *   - protocol = PROTOCOL_APB (4'h2)
 *   - event_code = APB_ERR_ADDR_RANGE (8'h08)
 *   - channel_id = 0 (APB has no ID concept)
 *   - event_data[63:60] = range_index (4 bits, 16 ranges)
 *   - event_data[59]    = is_read (1 = read, 0 = write) — kept for APB
 *   - event_data[58: 0] = cmd_paddr (zero-padded if narrower than 59 bits)
 *
 * The is_read bit is preserved here (carve-out from the 60-bit address
 * slot) because APB has no separate AR/AW channels — the same monitor
 * sees both directions and consumers need a way to disambiguate. The
 * AXI variant drops this bit since direction is implied by which
 * monitor (AR vs AW) emitted the packet.
 *
 * Side-band timestamp: same scheme as the AXI variant — sample
 * `i_mon_time` on emission, drive on `addr_pkt_timestamp`.
 *
 * Set both addr_low[i] and addr_high[i] equal for exact-match semantics.
 */
module apb_monitor_addr_check
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int N_ADDR_RANGES = 4,
    parameter int ADDR_WIDTH    = 32,
    parameter logic [7:0]  UNIT_ID  = 8'h00,
    parameter logic [15:0] AGENT_ID = 16'h0000,

    parameter int M = ADDR_WIDTH
)
(
    input  logic                                       clk,
    input  logic                                       aresetn,

    // Free-running counter from the monbus_group family, broadcast to every wrapper
    input  monbus_timestamp_t                          i_mon_time,

    // Snooped APB command stream
    input  logic [M-1:0]                               cmd_paddr,
    input  logic                                       cmd_pwrite,
    input  logic                                       cmd_valid,
    input  logic                                       cmd_ready,

    // Range configuration
    input  logic                                       cfg_addr_check_enable,
    input  logic [N_ADDR_RANGES-1:0]                   cfg_addr_range_enable,
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_low,
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_high,

    // Outgoing monbus packet
    output logic                                       addr_pkt_valid,
    input  logic                                       addr_pkt_ready,
    output monitor_packet_t                            addr_pkt_data,
    output monbus_timestamp_t                          addr_pkt_timestamp
);

    // -------------------------------------------------------------------------
    // Combinational range hits
    // -------------------------------------------------------------------------
    logic                       cmd_fire;
    logic [N_ADDR_RANGES-1:0]   hit_oh;

    assign cmd_fire = cmd_valid && cmd_ready && cfg_addr_check_enable;

    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            hit_oh[i] = cfg_addr_range_enable[i] && cmd_fire &&
                        (cmd_paddr >= cfg_addr_range_low[i]) &&
                        (cmd_paddr <= cfg_addr_range_high[i]);
        end
    end

    // -------------------------------------------------------------------------
    // Per-range pending mask + latched snapshot (address + is_read sense)
    // -------------------------------------------------------------------------
    logic [N_ADDR_RANGES-1:0]               r_pending;
    logic [N_ADDR_RANGES-1:0][M-1:0]        r_lat_addr;
    logic [N_ADDR_RANGES-1:0]               r_lat_is_read;

    logic [N_ADDR_RANGES-1:0]  emit_oh;
    logic                      emit_any;
    logic [3:0]                emit_idx;
    assign emit_any = |r_pending;

    // First-match pick over the pending mask.
    logic [N_ADDR_RANGES-1:0]  w_emit_pick;
    always_comb begin
        w_emit_pick = '0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (r_pending[i] && w_emit_pick == '0)
                w_emit_pick[i] = 1'b1;
        end
    end

    // Hold the SELECTION across a stalled beat. The pick is first-match, so a
    // lower-index range going pending mid-stall would otherwise displace the
    // beat already on the wire -- changing the packet's identity (range index
    // AND address) under a held valid. That is the same valid/ready violation
    // as the payload overwrite below, by a different route: there the chosen
    // range's payload changed, here the chosen range does. Nothing is delayed
    // indefinitely -- a pending bit only clears when its own beat is accepted,
    // so the displaced range is picked on the next free cycle.
    logic [N_ADDR_RANGES-1:0] r_emit_hold;
    logic                     r_emit_held;

    assign emit_oh = r_emit_held ? r_emit_hold : w_emit_pick;

    always_comb begin
        emit_idx = 4'h0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (emit_oh[i]) emit_idx = 4'(i);
        end
    end

    // Per-range shadow slot. A hit arriving while THAT range's packet is
    // already on the bus must not rewrite the beat being presented: the monbus
    // is valid/ready, so the payload has to hold until the beat is accepted.
    // The newer hit is buffered here and installed on accept, which keeps
    // "newest wins" for every beat except the one already on the wire.
    // Mirrors the axi_monitor_addr_check fix (AMBA-MONBUS-STABILITY); this
    // module is the same structure and had the same defect.
    logic [N_ADDR_RANGES-1:0]        r_shadow_valid;
    logic [N_ADDR_RANGES-1:0][M-1:0] r_shadow_addr;
    logic [N_ADDR_RANGES-1:0]        r_shadow_is_read;

    assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
    logic accept;
    assign accept = addr_pkt_valid && addr_pkt_ready;

    // This range's packet is on the bus right now / is accepted this cycle.
    logic [N_ADDR_RANGES-1:0] w_presented, w_range_accept;
    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            w_presented[i]    = addr_pkt_valid && emit_oh[i];
            w_range_accept[i] = accept         && emit_oh[i];
        end
    end

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pending        <= '0;
            r_lat_addr       <= '0;
            r_lat_is_read    <= '0;
            r_shadow_valid   <= '0;
            r_shadow_addr    <= '0;
            r_shadow_is_read <= '0;
            r_emit_hold      <= '0;
            r_emit_held      <= 1'b0;
        end else begin
            // 0) Freeze the selection while a beat is presented and unaccepted;
            //    release it on accept so the next range can be picked.
            if (accept)
                r_emit_held <= 1'b0;
            else if (addr_pkt_valid && !addr_pkt_ready) begin
                r_emit_held <= 1'b1;
                r_emit_hold <= emit_oh;
            end
            // 1) Latched payload. A fresh hit updates it ONLY when that
            //    range's beat is not currently presented; otherwise the hit
            //    goes to the shadow and is installed on accept, newest first
            //    (a hit in the accept cycle beats an older shadow).
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (w_range_accept[i]) begin
                    if (hit_oh[i]) begin
                        r_lat_addr   [i] <= cmd_paddr;
                        r_lat_is_read[i] <= !cmd_pwrite;
                    end else if (r_shadow_valid[i]) begin
                        r_lat_addr   [i] <= r_shadow_addr   [i];
                        r_lat_is_read[i] <= r_shadow_is_read[i];
                    end
                end else if (hit_oh[i] && !w_presented[i]) begin
                    r_lat_addr   [i] <= cmd_paddr;
                    r_lat_is_read[i] <= !cmd_pwrite;   // 1 = read
                end
            end
            // 2) Shadow slot: filled by a hit landing on a presented beat,
            //    emptied when that beat is accepted (value installed above).
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (w_range_accept[i]) begin
                    r_shadow_valid[i] <= 1'b0;
                end else if (hit_oh[i] && w_presented[i]) begin
                    r_shadow_valid  [i] <= 1'b1;
                    r_shadow_addr   [i] <= cmd_paddr;
                    r_shadow_is_read[i] <= !cmd_pwrite;
                end
            end
            // 3) Pending clears on accept only when nothing queued behind it.
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (hit_oh[i])
                    r_pending[i] <= 1'b1;
                else if (w_range_accept[i] && !r_shadow_valid[i])
                    r_pending[i] <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Pack the emitted packet (128-bit format, 64-bit event_data)
    // -------------------------------------------------------------------------
    // event_data[63:60] = range_index (4 bits, 16 ranges)
    // event_data[59]    = is_read flag
    // event_data[58: 0] = cmd_paddr (zero-padded if narrower than 59 bits)
    localparam logic [3:0] PKT_TYPE_FIELD = PktTypeError;
    localparam logic [3:0] PROTOCOL_FIELD = PROTOCOL_APB;            // 4'h2
    localparam logic [7:0] EVENT_CODE     = APB_ERR_ADDR_RANGE;      // 8'h08

    logic [M-1:0]  emit_addr;
    logic          emit_is_read;
    logic [63:0]   event_data_field;
    logic [58:0]   addr_payload;

    always_comb begin
        emit_addr    = '0;
        emit_is_read = 1'b0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (emit_oh[i]) begin
                emit_addr    = r_lat_addr   [i];
                emit_is_read = r_lat_is_read[i];
            end
        end
    end

    if (M >= 59) begin : g_addr_wide
        assign addr_payload = emit_addr[58:0];
    end else begin : g_addr_narrow
        assign addr_payload = {{(59-M){1'b0}}, emit_addr};
    end

    assign event_data_field = {emit_idx[3:0], emit_is_read, addr_payload};

    assign addr_pkt_data = create_monitor_packet(
        PKT_TYPE_FIELD,
        protocol_type_t'(PROTOCOL_FIELD),
        EVENT_CODE,
        9'h0,                            // channel_id: APB has no ID
        UNIT_ID,
        AGENT_ID,
        event_data_field
    );

    assign addr_pkt_timestamp = i_mon_time;

endmodule : apb_monitor_addr_check
