// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_monitor_addr_check
// Purpose: Configurable N-range address-violation checker for APB monitors
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba

`timescale 1ns / 1ps

`include "reset_defs.svh"

/**
 * APB Monitor — Address-Range Violation Checker
 *
 * Mirror of axi_monitor_addr_check for the APB monitor pipeline. Watches
 * the cmd_valid/cmd_ready handshake the apb_monitor already snoops and
 * emits a PktTypeError packet with event code APB_ERR_ADDR_RANGE (4'h8)
 * when an accepted command's paddr falls within any of N configured
 * [low, high] inclusive ranges.
 *
 * Differences vs the AXI variant:
 *   - protocol field is PROTOCOL_APB (3'b010)
 *   - event_code is APB_ERR_ADDR_RANGE (4'h8)
 *   - channel_id slot in the packet is fixed at 0 (APB has no ID concept)
 *   - is_read flag in event_data reflects cmd_pwrite (0 for read, 1 for write)
 *     — encoded as !cmd_pwrite so the field matches the AXI semantics
 *     (1 = read, 0 = write).
 *
 * Set both addr_low[i] and addr_high[i] equal for exact-match semantics.
 */
module apb_monitor_addr_check
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int N_ADDR_RANGES = 4,
    parameter int ADDR_WIDTH    = 32,
    parameter int UNIT_ID       = 4'h0,
    parameter int AGENT_ID      = 8'h00,

    parameter int M = ADDR_WIDTH
)
(
    input  logic                                       clk,
    input  logic                                       aresetn,

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
    logic [4:0]                emit_idx;
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

    assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
    logic accept;
    assign accept = addr_pkt_valid && addr_pkt_ready;

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pending     <= '0;
            r_lat_addr    <= '0;
            r_lat_is_read <= '0;
        end else begin
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (hit_oh[i]) begin
                    r_lat_addr   [i] <= cmd_paddr;
                    r_lat_is_read[i] <= !cmd_pwrite;   // 1 = read
                end
            end
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
    localparam logic [3:0] PKT_TYPE_FIELD = PktTypeError;
    localparam logic [2:0] PROTOCOL_FIELD = 3'b010;                  // PROTOCOL_APB
    localparam logic [3:0] EVENT_CODE     = APB_ERR_ADDR_RANGE;      // 4'h8

    logic [M-1:0]  emit_addr;
    logic          emit_is_read;
    logic [34:0]   event_data_field;

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

    assign event_data_field = {emit_idx[4:0], emit_is_read, emit_addr[28:0]};

    assign addr_pkt_data = create_monitor_packet(
        PKT_TYPE_FIELD,
        protocol_type_t'(PROTOCOL_FIELD),
        EVENT_CODE,
        6'h0,                            // channel_id: APB has no ID
        UNIT_ID[3:0],
        AGENT_ID[7:0],
        event_data_field
    );

endmodule : apb_monitor_addr_check
