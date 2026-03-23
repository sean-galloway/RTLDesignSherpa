// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Stripped copy of monbus_arbiter for yosys formal verification.
// Changes:
//   - Unpacked array ports replaced with packed equivalents
//   - Internal unpacked arrays replaced with packed equivalents
//   - Array indexing adapted for packed bit-slicing
//   - $error(...) calls removed
//   - CLIENTS fixed at 4 for tractability

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_arbiter #(
    parameter int CLIENTS            = 4,
    parameter int INPUT_SKID_ENABLE  = 0,
    parameter int OUTPUT_SKID_ENABLE = 0,
    parameter int INPUT_SKID_DEPTH   = 2,
    parameter int OUTPUT_SKID_DEPTH  = 2,
    parameter int N = $clog2(CLIENTS)
) (
    // Global Clock and Reset
    input  logic                         axi_aclk,
    input  logic                         axi_aresetn,

    // Optional block arbitration
    input  logic                         block_arb,

    // Monitor bus inputs from clients (packed for yosys)
    input  logic [CLIENTS-1:0]           monbus_valid_in,
    output logic [CLIENTS-1:0]           monbus_ready_in,
    input  logic [CLIENTS*64-1:0]        monbus_packet_in,

    // Monitor bus output - arbitrated result
    output logic                         monbus_valid,
    input  logic                         monbus_ready,
    output logic [63:0]                  monbus_packet,

    // Debug/Status outputs
    output logic                         grant_valid,
    output logic [CLIENTS-1:0]           grant,
    output logic [N-1:0]                 grant_id,
    output logic [CLIENTS-1:0]           last_grant
);

    // =======================================================================
    // Convert int parameters to 1-bit for generate blocks
    // =======================================================================

    localparam bit INPUT_SKID_EN  = (INPUT_SKID_ENABLE != 0);
    localparam bit OUTPUT_SKID_EN = (OUTPUT_SKID_ENABLE != 0);

    // =======================================================================
    // Internal signals for input skid buffers (packed)
    // =======================================================================

    logic [CLIENTS-1:0]           int_monbus_valid_in;
    logic [CLIENTS-1:0]           int_monbus_ready_in;
    logic [CLIENTS*64-1:0]        int_monbus_packet_in;

    // =======================================================================
    // Internal signals for output (before optional output skid buffer)
    // =======================================================================

    logic                    int_monbus_valid;
    logic                    int_monbus_ready;
    logic [63:0]             int_monbus_packet;

    // =======================================================================
    // Input Skid Buffers (Optional)
    // =======================================================================

    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_input_skid
            if (INPUT_SKID_EN == 1'b1) begin : gen_input_skid_enabled
                gaxi_skid_buffer #(
                    .DATA_WIDTH   (64),
                    .DEPTH        (INPUT_SKID_DEPTH)
                ) u_input_skid (
                    .axi_aclk     (axi_aclk),
                    .axi_aresetn  (axi_aresetn),
                    .wr_valid     (monbus_valid_in[i]),
                    .wr_ready     (monbus_ready_in[i]),
                    .wr_data      (monbus_packet_in[i*64 +: 64]),
                    .rd_valid     (int_monbus_valid_in[i]),
                    .rd_ready     (int_monbus_ready_in[i]),
                    .rd_data      (int_monbus_packet_in[i*64 +: 64]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .count        (),
                    .rd_count     ()
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end else begin : gen_input_skid_disabled
                // Direct connection when skid buffer disabled
                assign int_monbus_valid_in[i]          = monbus_valid_in[i];
                assign monbus_ready_in[i]              = int_monbus_ready_in[i];
                assign int_monbus_packet_in[i*64 +: 64] = monbus_packet_in[i*64 +: 64];
            end
        end
    endgenerate

    // =======================================================================
    // Arbiter Request and Grant ACK Logic
    // =======================================================================

    logic [CLIENTS-1:0] request;
    logic [CLIENTS-1:0] grant_ack;

    // Map monitor bus valid signals to arbiter requests
    always_comb begin
        for (int i = 0; i < CLIENTS; i++) begin
            request[i] = int_monbus_valid_in[i];
        end
    end

    // Grant ACK occurs when both grant is asserted AND client has valid data
    always_comb begin
        for (int i = 0; i < CLIENTS; i++) begin
            grant_ack[i] = grant[i] && int_monbus_valid_in[i];
        end
    end

    // =======================================================================
    // Round Robin Arbiter Instance (ACK Mode)
    // =======================================================================

    arbiter_round_robin #(
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (1)
    ) u_arbiter (
        .clk          (axi_aclk),
        .rst_n        (axi_aresetn),
        .block_arb    (block_arb),
        .request      (request),
        .grant_ack    (grant_ack),
        .grant_valid  (grant_valid),
        .grant        (grant),
        .grant_id     (grant_id),
        .last_grant   (last_grant)
    );

    // =======================================================================
    // Client Ready Signal Generation
    // =======================================================================

    always_comb begin
        for (int i = 0; i < CLIENTS; i++) begin
            int_monbus_ready_in[i] = grant[i] && int_monbus_ready;
        end
    end

    // =======================================================================
    // Output Multiplexer
    // =======================================================================

    always_comb begin
        int_monbus_valid  = grant_valid;
        int_monbus_packet = '0;

        if (grant_valid) begin
            int_monbus_packet = int_monbus_packet_in[grant_id*64 +: 64];
        end
    end

    // =======================================================================
    // Output Skid Buffer (Optional)
    // =======================================================================

    generate
        if (OUTPUT_SKID_EN == 1'b1) begin : gen_output_skid_enabled
            gaxi_skid_buffer #(
                .DATA_WIDTH   (64),
                .DEPTH        (OUTPUT_SKID_DEPTH)
            ) u_output_skid (
                .axi_aclk     (axi_aclk),
                .axi_aresetn  (axi_aresetn),
                .wr_valid     (int_monbus_valid),
                .wr_ready     (int_monbus_ready),
                .wr_data      (int_monbus_packet),
                .rd_valid     (monbus_valid),
                .rd_ready     (monbus_ready),
                .rd_data      (monbus_packet),
                /* verilator lint_off PINCONNECTEMPTY */
                .count        (),
                .rd_count     ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end else begin : gen_output_skid_disabled
            // Direct connection when output skid buffer disabled
            assign monbus_valid     = int_monbus_valid;
            assign int_monbus_ready = monbus_ready;
            assign monbus_packet    = int_monbus_packet;
        end
    endgenerate

    // =======================================================================
    // Assertions removed for yosys compatibility
    // (original contained $error calls and $onehot which yosys cannot parse)
    // =======================================================================

endmodule : monbus_arbiter
