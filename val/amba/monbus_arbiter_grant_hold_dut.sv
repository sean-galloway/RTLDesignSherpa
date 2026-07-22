// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: monbus_arbiter_grant_hold_dut
// Purpose: Cosim harness for monbus_arbiter. The arbiter's client-side ports
//          are SystemVerilog UNPACKED arrays (`logic monbus_valid_in [CLIENTS]`,
//          `monitor_packet_t monbus_packet_in [CLIENTS]`, ...). Verilator
//          flattens unpacked array ports on the cosim toplevel, so cocotb
//          cannot index them. This wrapper re-presents them as packed vectors
//          so the grant-hold regression can drive per-client valid/ready and
//          per-client payloads directly.
//
//          Pure wiring - no logic is added or removed.

`timescale 1ns / 1ps

module monbus_arbiter_grant_hold_dut
    import monitor_common_pkg::*;
#(
    parameter int CLIENTS            = 4,
    parameter int INPUT_SKID_ENABLE  = 0,
    parameter int OUTPUT_SKID_ENABLE = 0,
    parameter int N = $clog2(CLIENTS)
) (
    input  logic                                     axi_aclk,
    input  logic                                     axi_aresetn,
    input  logic                                     block_arb,

    // Client side - packed for cocotb visibility
    input  logic [CLIENTS-1:0]                       monbus_valid_in,
    output logic [CLIENTS-1:0]                       monbus_ready_in,
    input  logic [CLIENTS*MONBUS_PKT_WIDTH-1:0]      monbus_packet_in,
    input  logic [CLIENTS*MONBUS_TS_WIDTH-1:0]       monbus_timestamp_in,

    // Arbitrated output
    output logic                                     monbus_valid,
    input  logic                                     monbus_ready,
    output monitor_packet_t                          monbus_packet,
    output monbus_timestamp_t                        monbus_timestamp,

    // Debug/status
    output logic                                     grant_valid,
    output logic [CLIENTS-1:0]                       grant,
    output logic [N-1:0]                             grant_id,
    output logic [CLIENTS-1:0]                       last_grant
);

    logic              w_valid_in     [CLIENTS];
    logic              w_ready_in     [CLIENTS];
    monitor_packet_t   w_packet_in    [CLIENTS];
    monbus_timestamp_t w_timestamp_in [CLIENTS];

    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : g_unpack
            assign w_valid_in[i]     = monbus_valid_in[i];
            assign monbus_ready_in[i] = w_ready_in[i];
            assign w_packet_in[i]    =
                monbus_packet_in[i*MONBUS_PKT_WIDTH +: MONBUS_PKT_WIDTH];
            assign w_timestamp_in[i] =
                monbus_timestamp_in[i*MONBUS_TS_WIDTH +: MONBUS_TS_WIDTH];
        end
    endgenerate

    monbus_arbiter #(
        .CLIENTS            (CLIENTS),
        .INPUT_SKID_ENABLE  (INPUT_SKID_ENABLE),
        .OUTPUT_SKID_ENABLE (OUTPUT_SKID_ENABLE)
    ) u_arb (
        .axi_aclk            (axi_aclk),
        .axi_aresetn         (axi_aresetn),
        .block_arb           (block_arb),
        .monbus_valid_in     (w_valid_in),
        .monbus_ready_in     (w_ready_in),
        .monbus_packet_in    (w_packet_in),
        .monbus_timestamp_in (w_timestamp_in),
        .monbus_valid        (monbus_valid),
        .monbus_ready        (monbus_ready),
        .monbus_packet       (monbus_packet),
        .monbus_timestamp    (monbus_timestamp),
        .grant_valid         (grant_valid),
        .grant               (grant),
        .grant_id            (grant_id),
        .last_grant          (last_grant)
    );

endmodule : monbus_arbiter_grant_hold_dut
