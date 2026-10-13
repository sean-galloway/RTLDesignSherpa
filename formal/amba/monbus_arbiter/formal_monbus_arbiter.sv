// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for monbus_arbiter (yosys-compatible, reads the sv2v flat).
//
// The three properties that used to sit at the bottom of
// rtl/amba/ocelus/monbus_arbiter.sv as runtime assertions (issue #112; no
// assertions in RTL -- vault/handbook/design/no-assertions-in-rtl.md):
//   A1  grant is one-hot whenever grant_valid
//   A2  grant[grant_id] is set whenever grant_valid
//   A3  a client that is not granted never sees ready
//
// Configuration: CLIENTS=4, INPUT_SKID_ENABLE=0, OUTPUT_SKID_ENABLE=1.
// With the input skids off, the gen_input_skid_disabled branch assigns
// monbus_ready_in[i] = int_monbus_ready_in[i], so A3 -- a property of the
// internal ready -- is checked on a PORT, with no hierarchical reference
// (a hierarchical ref to a missing net elaborates as a free wire and passes
// vacuously; see vault/handbook/dv/formal.md). A1/A2 are properties of the
// arbiter core and do not depend on the skid configuration.
//
// Port shapes follow the sv2v flat: the unpacked [CLIENTS] arrays become
// ascending [0:CLIENTS-1] vectors, so ready_in[i] is client i; grant is
// [CLIENTS-1:0] as in the RTL.

`timescale 1ns / 1ps

module formal_monbus_arbiter #(
    parameter int CLIENTS = 4
) (
    input logic clk,
    input logic rst_n
);

    localparam int N = $clog2(CLIENTS);

    // ---------------------------------------------------------------------
    // Formal infrastructure: reset held for the first cycle, then released
    // ---------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 1) assume (rst_n);
    end

    // ---------------------------------------------------------------------
    // Free inputs
    // ---------------------------------------------------------------------
    (* anyseq *) logic                          block_arb;
    (* anyseq *) logic [0:CLIENTS-1]            valid_in;
    (* anyseq *) logic [CLIENTS*128-1:0]        packet_in;
    (* anyseq *) logic [CLIENTS*64-1:0]         timestamp_in;
    (* anyseq *) logic                          monbus_ready;

    // ---------------------------------------------------------------------
    // DUT outputs
    // ---------------------------------------------------------------------
    logic [0:CLIENTS-1]   ready_in;
    logic                 monbus_valid;
    logic [127:0]         monbus_packet;
    logic [63:0]          monbus_timestamp;
    logic                 grant_valid;
    logic [CLIENTS-1:0]   grant;
    logic [N-1:0]         grant_id;
    logic [CLIENTS-1:0]   last_grant;

    monbus_arbiter #(
        .CLIENTS            (CLIENTS),
        .INPUT_SKID_ENABLE  (0),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_dut (
        .axi_aclk            (clk),
        .axi_aresetn         (rst_n),
        .block_arb           (block_arb),
        .monbus_valid_in     (valid_in),
        .monbus_ready_in     (ready_in),
        .monbus_packet_in    (packet_in),
        .monbus_timestamp_in (timestamp_in),
        .monbus_valid        (monbus_valid),
        .monbus_ready        (monbus_ready),
        .monbus_packet       (monbus_packet),
        .monbus_timestamp    (monbus_timestamp),
        .grant_valid         (grant_valid),
        .grant               (grant),
        .grant_id            (grant_id),
        .last_grant          (last_grant)
    );

    // ---------------------------------------------------------------------
    // Properties (sampled on the clock, out of reset -- the same sampling
    // the removed in-RTL always @(posedge axi_aclk) assertions used)
    // ---------------------------------------------------------------------
    wire f_live = (f_past_valid >= 1) && rst_n;

    always @(posedge clk) begin
        if (f_live && grant_valid) begin
            // A1: one-hot
            assert ((grant != '0) && ((grant & (grant - 1'b1)) == '0));
            // A2: grant_id names the granted client
            assert (grant[grant_id]);
        end
    end

    genvar gi;
    generate
        for (gi = 0; gi < CLIENTS; gi++) begin : g_ready
            always @(posedge clk) begin
                // A3: only the granted client sees ready
                if (f_live && !grant[gi])
                    assert (!ready_in[gi]);
            end
        end
    endgenerate

    // ---------------------------------------------------------------------
    // Covers: the antecedents are reachable (non-vacuity)
    // ---------------------------------------------------------------------
    always @(posedge clk) begin
        if (f_live) begin
            cover (grant_valid && grant[0]);
            cover (grant_valid && grant[CLIENTS-1]);
            cover (ready_in[0]);
            cover (ready_in[CLIENTS-1]);
            // two different clients granted on consecutive cycles
            cover (grant_valid && grant[1] && last_grant[0]);
        end
    end

endmodule : formal_monbus_arbiter
