// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_stall_mon
// Purpose: Stalled-data check on MonBus (TILE_SPEC 11.9 hazard rules, rapids TASK-027)
//
// Description:
//   With straps in both directions every packet has space at its destination
//   and always drains, so data that stops moving is a fault somewhere, and it
//   is reported rather than waited on. Per channel, pending[ch] says the
//   channel has data it expects to move and moved[ch] pulses when some of it
//   does:
//     sink half    data in the channel's sink SRAM / a W beat of the channel
//     source half  reads outstanding / an R beat for the channel
//   A channel pending for cfg_stall_cycles cycles with no movement raises one
//   MonBus error packet (PktTypeError, PROTOCOL_CORE, RAPIDS_EVENT_STALL;
//   payload bit 32 = KIND, bits [31:0] the threshold), and no other until it
//   moves or empties. cfg_stall_cycles = 0 turns the check off.
//
// Parameters:
//   - NUM_CHANNELS: channels watched
//   - KIND:         0 = sink, 1 = source (carried in the payload)
//   - MON_AGENT_ID / MON_UNIT_ID: the packet's agent and unit
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_tile_stall_mon #(
    parameter int          NUM_CHANNELS = 8,
    parameter bit          KIND         = 1'b0,
    parameter logic [15:0] MON_AGENT_ID = 16'h000B,
    parameter logic [7:0]  MON_UNIT_ID  = 8'h01,
    parameter int NC  = NUM_CHANNELS,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    input  logic                                   clk,
    input  logic                                   rst_n,

    input  logic [31:0]                            cfg_stall_cycles,   // 0 = off
    input  logic [NC-1:0]                          pending,
    input  logic [NC-1:0]                          moved,

    input  monitor_common_pkg::monbus_timestamp_t  i_mon_time,
    output logic                                   mon_valid,
    input  logic                                   mon_ready,
    output monitor_common_pkg::monitor_packet_t    mon_packet,
    output monitor_common_pkg::monbus_timestamp_t  mon_timestamp,

    output logic [NC-1:0]                          sts_stalled        // stalled now (one episode)
);

    logic [NC-1:0][31:0] r_cnt;
    logic [NC-1:0]       r_fired;     // this episode has been reported
    logic [NC-1:0]       r_due;       // ...and its packet is still to go out
    logic [CIW-1:0]      r_rr;

    // Next channel with a packet due, round-robin
    logic           w_pick;
    logic [CIW-1:0] w_pick_ch;
    always_comb begin
        w_pick    = 1'b0;
        w_pick_ch = '0;
        for (int k = 1; k <= NC; k++) begin
            if (!w_pick && r_due[(int'(r_rr) + k) % NC]) begin
                w_pick    = 1'b1;
                w_pick_ch = CIW'((int'(r_rr) + k) % NC);
            end
        end
    end

    logic w_load;
    assign w_load = w_pick && (!mon_valid || mon_ready);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cnt         <= '{default:'0};
            r_fired       <= '0;
            r_due         <= '0;
            r_rr          <= CIW'(NC - 1);
            mon_valid     <= 1'b0;
            mon_packet    <= '0;
            mon_timestamp <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (!pending[ch] || moved[ch] || (cfg_stall_cycles == '0)) begin
                    r_cnt[ch]   <= '0;
                    r_fired[ch] <= 1'b0;
                end else if (!r_fired[ch]) begin
                    if (r_cnt[ch] + 32'd1 >= cfg_stall_cycles) begin
                        r_fired[ch] <= 1'b1;
                        r_due[ch]   <= 1'b1;
                    end
                    r_cnt[ch] <= r_cnt[ch] + 32'd1;
                end
            end
            if (mon_valid && mon_ready) mon_valid <= 1'b0;
            if (w_load) begin
                r_due[w_pick_ch] <= 1'b0;
                r_rr             <= w_pick_ch;
                mon_valid        <= 1'b1;
                mon_packet       <= create_monitor_packet(
                    PktTypeError,
                    PROTOCOL_CORE,
                    RAPIDS_EVENT_STALL,
                    9'(w_pick_ch),
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    {31'h0, KIND, cfg_stall_cycles});
                mon_timestamp    <= i_mon_time;
            end
        end
    )

    assign sts_stalled = r_fired;

endmodule : rapids_tile_stall_mon
