// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_record_expander
// Purpose: Raw 3-beat record expander for the monbus group family.
//
//   Turns one (packet, source timestamp) record into three 64-bit beats
//   pushed atomically into a beat-granular write FIFO:
//     beat 0 = {tag[3:0]=4'h0, source_ts[59:0]}
//     beat 1 = packet[127:64]
//     beat 2 = packet[63:0]
//   A record is never split across backpressure: once beat 0 is accepted
//   the expander commits to beats 1 and 2, holding out_valid until each is
//   taken. in_ready is the beat-0 handshake, so the upstream record is
//   consumed exactly when its first beat enters the FIFO. Per-beat
//   out_ready is used (not a "3 slots free" precheck) to keep the FIFO
//   count -> wr_valid -> count path from closing a combinational loop.
//
//   This is the expander monbus_group_core carries inline, lifted out so
//   monbus_group_core_1wr can run one per source (error path, trace path).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_record_expander
    import ocelus_common_pkg::*;
(
    input  logic                  axi_aclk,
    input  logic                  axi_aresetn,

    // Record in: the caller qualifies in_valid with its routing decision.
    input  logic                  in_valid,
    output logic                  in_ready,     // beat-0 accepted this cycle
    input  monitor_packet_t       in_packet,
    input  monbus_timestamp_t     in_source_ts,

    // Beats out (to a 64-bit FIFO write port)
    output logic                  out_valid,
    input  logic                  out_ready,
    output logic [63:0]           out_data
);

    localparam logic [3:0] WRITE_TAG_RAW = 4'h0;

    typedef enum logic [1:0] {
        EXP_TS   = 2'd0,
        EXP_HI   = 2'd1,
        EXP_LO   = 2'd2,
        EXP_RSVD = 2'd3
    } exp_state_t;

    exp_state_t        r_exp_state;
    monitor_packet_t   r_lat_packet;

    logic w_accepting_now;
    assign w_accepting_now = (r_exp_state == EXP_TS) && in_valid;

    always_comb begin
        out_valid = 1'b0;
        out_data  = 64'd0;
        unique case (r_exp_state)
            EXP_TS:   if (w_accepting_now) begin
                          out_valid = 1'b1;
                          out_data  = {WRITE_TAG_RAW, in_source_ts[59:0]};
                      end
            EXP_HI:   begin
                          out_valid = 1'b1;
                          out_data  = r_lat_packet[MONBUS_PKT_WIDTH-1:64];
                      end
            EXP_LO:   begin
                          out_valid = 1'b1;
                          out_data  = r_lat_packet[63:0];
                      end
            default:  ;
        endcase
    end

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_exp_state  <= EXP_TS;
            r_lat_packet <= '0;
        end else begin
            unique case (r_exp_state)
                EXP_TS: if (w_accepting_now && out_ready) begin
                            r_lat_packet <= in_packet;
                            r_exp_state  <= EXP_HI;
                        end
                EXP_HI: if (out_ready) r_exp_state <= EXP_LO;
                EXP_LO: if (out_ready) r_exp_state <= EXP_TS;
                default: r_exp_state <= EXP_TS;
            endcase
        end
    )

    assign in_ready = w_accepting_now && out_ready;

    /* verilator lint_off UNUSED */
    logic [3:0] _unused_ts_hi = in_source_ts[63:60];
    /* verilator lint_on UNUSED */

endmodule : monbus_record_expander
