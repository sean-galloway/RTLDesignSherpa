// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_addr_check
// Purpose: Configurable N-range address-violation checker for AXI monitors
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba

`timescale 1ns / 1ps

`include "reset_defs.svh"

/**
 * AXI Monitor — Address-Range Violation Checker
 *
 * Watches the cmd_addr / cmd_valid / cmd_ready handshake already snooped by
 * axi_monitor_base and emits a PktTypeError packet with event code
 * AXI_ERR_ADDR_RANGE (4'hD) whenever an accepted command's address falls
 * inside one of N user-configured [low, high] inclusive ranges.
 *
 * Encoding:
 *   - packet_type = PktTypeError (4'h0)
 *   - protocol    = PROTOCOL_AXI (3'b000)
 *   - event_code  = AXI_ERR_ADDR_RANGE (4'hD)
 *   - event_data[34:30] = range_index (5 bits, supports up to 32 ranges)
 *   - event_data[29]    = is_read flag (1 = AR, 0 = AW)
 *   - event_data[28: 0] = lower 29 bits of cmd_addr that hit
 *
 * Per-range coalescing:
 *   When a command hits range i, the address is latched into per-range state
 *   and a pending bit is set. If new commands hit range i before its event
 *   has been emitted, the latched address is overwritten (the latest hit
 *   wins). One emission per cycle drains the pending mask via a lowest-
 *   index priority encoder. This guarantees no event loss for distinct
 *   ranges and a bounded N-cycle drain to clear all pending under sustained
 *   load.
 *
 * Set both addr_low[i] and addr_high[i] equal for exact-match semantics.
 *
 * When cfg_addr_check_enable is 0 the module is fully quiescent
 * (addr_pkt_valid stays low, no flops update).
 */
module axi_monitor_addr_check
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int N_ADDR_RANGES = 4,             // number of independent ranges (>=1)
    parameter int ADDR_WIDTH    = 32,            // address width
    parameter int ID_WIDTH      = 6,             // cmd_id width (clipped to 6 bits for channel_id)
    parameter int UNIT_ID       = 4'h0,          // 4-bit Unit ID in monitor packets
    parameter int AGENT_ID      = 8'h00,         // 8-bit Agent ID in monitor packets
    parameter bit IS_READ       = 1'b1,          // 1 if this monitor watches reads (AR), 0 if writes (AW)

    // Local widths
    parameter int M  = ADDR_WIDTH,
    parameter int IW = ID_WIDTH
)
(
    input  logic                                       clk,
    input  logic                                       aresetn,

    // Snooped command stream (tap point: same wires as axi_monitor_base sees)
    input  logic [M-1:0]                               cmd_addr,
    input  logic [IW-1:0]                              cmd_id,
    input  logic                                       cmd_valid,
    input  logic                                       cmd_ready,

    // Range configuration
    input  logic                                       cfg_addr_check_enable,           // master on/off
    input  logic [N_ADDR_RANGES-1:0]                   cfg_addr_range_enable,           // per-range enable
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_low,              // inclusive low
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_high,             // inclusive high

    // Outgoing monbus packet (consumer typically merges with reporter stream)
    output logic                                       addr_pkt_valid,
    input  logic                                       addr_pkt_ready,
    output logic [63:0]                                addr_pkt_data
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
                        (cmd_addr >= cfg_addr_range_low[i]) &&
                        (cmd_addr <= cfg_addr_range_high[i]);
        end
    end

    // -------------------------------------------------------------------------
    // Per-range pending mask + latched (address, id) snapshot
    // -------------------------------------------------------------------------
    // When a range hits, latch its address + id and set its pending bit.
    // Emission drains the lowest-index pending bit each cycle.
    logic [N_ADDR_RANGES-1:0]               r_pending;
    logic [N_ADDR_RANGES-1:0][M-1:0]        r_lat_addr;
    logic [N_ADDR_RANGES-1:0][IW-1:0]       r_lat_id;

    // Lowest-index pending: priority encoder picks the next range to emit
    logic [N_ADDR_RANGES-1:0] emit_oh;
    logic                     emit_any;
    logic [4:0]               emit_idx;       // 5-bit range_index, supports up to 32 ranges
    assign emit_any = |r_pending;
    always_comb begin
        emit_oh  = '0;
        emit_idx = 5'h0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (r_pending[i] && emit_oh == '0) begin
                emit_oh[i] = 1'b1;
                emit_idx   = 5'(i);
            end
        end
    end

    // Handshake: addr_pkt_valid asserts whenever something is pending and the
    // module is enabled. Pop on consumer ready.
    assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
    logic accept;
    assign accept = addr_pkt_valid && addr_pkt_ready;

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pending  <= '0;
            r_lat_addr <= '0;
            r_lat_id   <= '0;
        end else begin
            // 1) Latch new hits this cycle. If a new hit collides with the
            //    same-range pending event being emitted right now, the latch
            //    wins (so the consumer never misses a fresh address).
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (hit_oh[i]) begin
                    r_lat_addr[i] <= cmd_addr;
                    r_lat_id  [i] <= cmd_id;
                end
            end

            // 2) Update per-range pending bits: set on hit, clear on accept.
            //    Set wins on collision (don't lose the new event).
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (hit_oh[i])
                    r_pending[i] <= 1'b1;
                else if (accept && emit_oh[i])
                    r_pending[i] <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Pack the emitted packet
    // -------------------------------------------------------------------------
    // event_data[34:30] = range_index, [29] = is_read, [28:0] = lower addr bits
    localparam logic [3:0] PKT_TYPE_FIELD = PktTypeError;
    localparam logic [2:0] PROTOCOL_FIELD = 3'b000;                  // PROTOCOL_AXI
    localparam logic [3:0] EVENT_CODE     = AXI_ERR_ADDR_RANGE;      // 4'hD

    logic [M-1:0]   emit_addr;
    logic [IW-1:0]  emit_id;
    logic [5:0]     channel_id_field;
    logic [34:0]    event_data_field;

    always_comb begin
        emit_addr = '0;
        emit_id   = '0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (emit_oh[i]) begin
                emit_addr = r_lat_addr[i];
                emit_id   = r_lat_id[i];
            end
        end
    end

    // channel_id is 6 bits in the packet — clip or zero-extend cmd_id.
    // Done as a generate-if so the dead branch's replication count never
    // goes negative when IW >= 6 (Verilator elaborates both arms of a
    // ternary and flags the negative {{(6-IW){...}}} otherwise).
    if (IW >= 6) begin : g_chan_id_wide
        assign channel_id_field = emit_id[5:0];
    end else begin : g_chan_id_narrow
        assign channel_id_field = {{(6-IW){1'b0}}, emit_id};
    end

    assign event_data_field = {emit_idx[4:0], IS_READ, emit_addr[28:0]};

    assign addr_pkt_data = create_monitor_packet(
        PKT_TYPE_FIELD,                  // [63:60] packet_type
        protocol_type_t'(PROTOCOL_FIELD),// [59:57] protocol
        EVENT_CODE,                      // [56:53] event_code
        channel_id_field,                // [52:47] channel_id
        UNIT_ID[3:0],                    // [46:43] unit_id
        AGENT_ID[7:0],                   // [42:35] agent_id
        event_data_field                 // [34: 0] event_data
    );

endmodule : axi_monitor_addr_check
