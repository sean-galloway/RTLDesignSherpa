// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for monbus_arbiter (yosys-compatible)
// Uses stripped copy with packed arrays. Skid buffers disabled.

module formal_monbus_arbiter #(
    parameter int CLIENTS = 4,
    parameter int N = $clog2(CLIENTS)
) (
    input  logic                       clk,
    input  logic                       rst_n,
    input  logic [CLIENTS-1:0]         monbus_valid_in,
    input  logic [CLIENTS*64-1:0]      monbus_packet_in,
    input  logic                       monbus_ready,
    input  logic                       block_arb
);

    logic [CLIENTS-1:0]        monbus_ready_in;
    logic                      monbus_valid;
    logic [63:0]               monbus_packet;

    monbus_arbiter #(
        .CLIENTS(CLIENTS),
        .INPUT_SKID_ENABLE(0),
        .OUTPUT_SKID_ENABLE(0)
    ) dut (
        .axi_aclk           (clk),
        .axi_aresetn         (rst_n),
        .block_arb           (block_arb),
        .monbus_valid_in     (monbus_valid_in),
        .monbus_ready_in     (monbus_ready_in),
        .monbus_packet_in    (monbus_packet_in),
        .monbus_valid        (monbus_valid),
        .monbus_ready        (monbus_ready),
        .monbus_packet       (monbus_packet)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // Assume block_arb is low (normal operation)
    always @(posedge clk) begin
        if (rst_n) assume (!block_arb);
    end

    // Input handshake: valid stable until ready
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_assume
            always @(posedge clk) begin
                if (f_past_valid > 0 && rst_n && $past(rst_n))
                    if ($past(monbus_valid_in[i]) && !$past(monbus_ready_in[i]))
                        assume (monbus_valid_in[i]);
            end
        end
    endgenerate

    // Reset clears output
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset: assert (!monbus_valid);
    end

    // No output valid without any input valid (with skid disabled)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(!|monbus_valid_in))
                ap_no_spurious: assert (!monbus_valid);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_output: cover (monbus_valid && monbus_ready);
            cp_all_req: cover (&monbus_valid_in);
        end
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_rotate: cover (monbus_valid && $past(monbus_valid));
    end

endmodule
