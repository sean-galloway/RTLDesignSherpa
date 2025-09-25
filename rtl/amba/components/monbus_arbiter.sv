`timescale 1ns / 1ps

/*
================================================================================
Monitor Bus Round Robin Arbiter with Optional Skid Buffers
================================================================================

This module implements a round-robin arbiter for monitor bus interfaces with
optional input and output skid buffers. The arbiter operates in ACK mode,
where grants are held until both request and grant_ack are asserted.

Key Features:
- Round-robin arbitration ensuring fairness
- ACK mode operation (grants held until acknowledged)
- Optional input skid buffers per client
- Optional output skid buffer
- 64-bit monitor bus packet interface
- Parameterizable number of clients

Interface Mapping:
- Requests: monbus_valid_in signals from clients
- Grant ACK: grant && monbus_valid_in (client accepts the grant)
- Data: monbus_packet_in from winning client passed to output

Parameters:
- CLIENTS: Number of monitor bus clients
- INPUT_SKID_ENABLE: Enable skid buffers on input interfaces
- OUTPUT_SKID_ENABLE: Enable skid buffer on output interface
- INPUT_SKID_DEPTH: Depth of input skid buffers (2, 4, 6, or 8)
- OUTPUT_SKID_DEPTH: Depth of output skid buffer (2, 4, 6, or 8)

================================================================================
*/

module monbus_arbiter #(
    parameter int CLIENTS            = 4,
    parameter int INPUT_SKID_ENABLE  = 1,        // Keep as int but convert internally
    parameter int OUTPUT_SKID_ENABLE = 1,        // Keep as int but convert internally
    parameter int INPUT_SKID_DEPTH   = 2,        // Must be one of {2, 4, 6, 8}
    parameter int OUTPUT_SKID_DEPTH  = 2,        // Must be one of {2, 4, 6, 8}
    parameter int N = $clog2(CLIENTS)
) (
    // Global Clock and Reset
    input  logic                    axi_aclk,
    input  logic                    axi_aresetn,

    // Optional block arbitration
    input  logic                    block_arb,

    // Monitor bus inputs from clients
    input  logic                    monbus_valid_in[CLIENTS],
    output logic                    monbus_ready_in[CLIENTS],
    input  logic [63:0]             monbus_packet_in[CLIENTS],

    // Monitor bus output - arbitrated result
    output logic                    monbus_valid,
    input  logic                    monbus_ready,
    output logic [63:0]             monbus_packet,

    // Debug/Status outputs
    output logic                    grant_valid,
    output logic [CLIENTS-1:0]      grant,
    output logic [N-1:0]            grant_id,
    output logic [CLIENTS-1:0]      last_grant
);

    // =======================================================================
    // Convert int parameters to 1-bit for generate blocks
    // =======================================================================

    localparam bit INPUT_SKID_EN  = (INPUT_SKID_ENABLE != 0);
    localparam bit OUTPUT_SKID_EN = (OUTPUT_SKID_ENABLE != 0);

    // =======================================================================
    // Internal signals for input skid buffers
    // =======================================================================

    logic                    int_monbus_valid_in[CLIENTS];
    logic                    int_monbus_ready_in[CLIENTS];
    logic [63:0]             int_monbus_packet_in[CLIENTS];

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
                    .DEPTH        (INPUT_SKID_DEPTH),
                    .INSTANCE_NAME($sformatf("INPUT_SKID_%0d", i))
                ) u_input_skid (
                    .axi_aclk     (axi_aclk),
                    .axi_aresetn  (axi_aresetn),
                    .wr_valid     (monbus_valid_in[i]),
                    .wr_ready     (monbus_ready_in[i]),
                    .wr_data      (monbus_packet_in[i]),
                    .rd_valid     (int_monbus_valid_in[i]),
                    .rd_ready     (int_monbus_ready_in[i]),
                    .rd_data      (int_monbus_packet_in[i]),
                    /* verilator lint_off PINCONNECTEMPTY */
                    .count        (), // Unused
                    .rd_count     ()  // Unused
                    /* verilator lint_on PINCONNECTEMPTY */
                );
            end else begin : gen_input_skid_disabled
                // Direct connection when skid buffer disabled
                assign int_monbus_valid_in[i]  = monbus_valid_in[i];
                assign monbus_ready_in[i]      = int_monbus_ready_in[i];
                assign int_monbus_packet_in[i] = monbus_packet_in[i];
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
    // This implements the "stick on grant until both request and grant ack are high" requirement
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
        .WAIT_GNT_ACK (1)        // Enable ACK mode
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

    // Each client's ready signal is asserted when:
    // 1. That client is currently granted AND
    // 2. The downstream (internal output) is ready to accept data
    always_comb begin
        for (int i = 0; i < CLIENTS; i++) begin
            int_monbus_ready_in[i] = grant[i] && int_monbus_ready;
        end
    end

    // =======================================================================
    // Output Multiplexer
    // =======================================================================

    // Select data from the granted client
    always_comb begin
        int_monbus_valid  = grant_valid;
        int_monbus_packet = '0;  // Default to zero

        if (grant_valid) begin
            int_monbus_packet = int_monbus_packet_in[grant_id];
        end
    end

    // =======================================================================
    // Output Skid Buffer (Optional)
    // =======================================================================

    generate
        if (OUTPUT_SKID_EN == 1'b1) begin : gen_output_skid_enabled
            gaxi_skid_buffer #(
                .DATA_WIDTH   (64),
                .DEPTH        (OUTPUT_SKID_DEPTH),
                .INSTANCE_NAME("OUTPUT_SKID")
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
                .count        (), // Unused
                .rd_count     ()  // Unused
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
    // Assertions for Design Verification
    // =======================================================================

    // synthesis translate_off

    // Verify grant is always one-hot when valid
    always @(posedge axi_aclk) begin
        if (axi_aresetn && grant_valid) begin
            assert ($onehot(grant)) else
                $error("Grant vector is not one-hot when grant_valid is asserted");
        end
    end

    // Verify grant_id corresponds to the asserted grant bit
    always @(posedge axi_aclk) begin
        if (axi_aresetn && grant_valid) begin
            assert (grant[grant_id]) else
                $error("grant_id does not correspond to asserted grant bit");
        end
    end

    // Verify only granted client receives ready
    always @(posedge axi_aclk) begin
        if (axi_aresetn) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (!grant[i]) begin
                    assert (!int_monbus_ready_in[i]) else
                        $error("Non-granted client %0d received ready signal", i);
                end
            end
        end
    end

    // synthesis translate_on

endmodule : monbus_arbiter
