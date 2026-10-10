// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for amber_pending_fill_bypass (yosys-compatible)
// Run with: sby amber_pending_fill_bypass.sby
//
// Task 13 proof (MAS ch02_blocks/02, standalone leaf at the tiny geometry
// SETS=16 / LINE_BYTES=64 / BUS_WIDTH=64 -> FILL_BEATS=8, LINE_ADDR_WIDTH=26).
//
// Assumption inventory (smallest sound choices; the amber_control integration
// is discharged in the amber_control proof):
//   - reset protocol: house pattern (initially in reset, release after 2
//     cycles, never re-asserts).
//   - A1 (environment contract from amber_control): pf_load never arms an
//     Invalid install state -- control only loads READ_SHARED->S / else->M.
//     The leaf itself is state-agnostic; this mirrors its only in-system use.
// Everything else (pf_clear/pf_beat timing, addresses, indices) is free.
//
// Abstraction: none -- the whole leaf is the DUT; no memories inside.

module formal_amber_pending_fill_bypass (
    input  logic        clk,
    input  logic        rst_n,

    // free environment inputs
    input  logic        pf_load,
    input  logic [25:0] pf_load_addr,
    input  logic [2:0]  pf_load_state,
    input  logic        pf_beat_set,
    input  logic [2:0]  pf_beat_idx,
    input  logic [25:0] pf_snoop_addr,
    input  logic        pf_clear
);

    localparam SETS        = 16;
    localparam LINE_BYTES  = 64;
    localparam BUS_WIDTH   = 64;
    localparam FILL_BEATS  = LINE_BYTES / (BUS_WIDTH/8);   // 8
    localparam LINE_ADDR_WIDTH = 26;

    localparam [2:0] ST_I = 3'b000;
    localparam [2:0] ST_S = 3'b001;
    localparam [2:0] ST_M = 3'b011;

    // DUT outputs
    logic                        pf_match;
    logic                        pf_active;
    logic [LINE_ADDR_WIDTH-1:0]  pf_addr;
    logic [2:0]                  pf_state;
    logic [FILL_BEATS-1:0]       pf_data_valid;
    logic                        pf_beat_valid;

    amber_pending_fill_bypass #(
        .ADDR_WIDTH (32),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) dut (
        .clk           (clk),
        .rst_n         (rst_n),
        .pf_load       (pf_load),
        .pf_load_addr  (pf_load_addr),
        .pf_load_state (pf_load_state),
        .pf_beat_set   (pf_beat_set),
        .pf_beat_idx   (pf_beat_idx),
        .pf_snoop_addr (pf_snoop_addr),
        .pf_match      (pf_match),
        .pf_active     (pf_active),
        .pf_addr       (pf_addr),
        .pf_state      (pf_state),
        .pf_data_valid (pf_data_valid),
        .pf_beat_valid (pf_beat_valid),
        .pf_clear      (pf_clear)
    );

    // =========================================================================
    // Formal infrastructure (house pattern)
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // A1: control only ever arms S/M install states (never pre-fill Invalid)
    always @(posedge clk) begin
        if (rst_n)
            as_load_never_i: assume (!(pf_load && (pf_load_state == ST_I)));
    end

    // =========================================================================
    // Ghost mirror of the register contents (loaded values)
    // =========================================================================
    reg                        f_active_q;
    reg [LINE_ADDR_WIDTH-1:0]  f_addr_q;
    reg [2:0]                  f_state_q;
    reg [FILL_BEATS-1:0]       f_beats_q;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_active_q <= 1'b0;
            f_addr_q   <= '0;
            f_state_q  <= ST_I;
            f_beats_q  <= '0;
        end else if (pf_load) begin
            f_active_q <= 1'b1;
            f_addr_q   <= pf_load_addr;
            f_state_q  <= pf_load_state;
            f_beats_q  <= '0;
        end else if (pf_clear) begin
            f_active_q <= 1'b0;
        end else if (pf_beat_set) begin
            f_beats_q[pf_beat_idx] <= 1'b1;
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1 state accuracy: while armed the register holds exactly the loaded
    // line address and install state (never drifts, never reverts to the
    // pre-fill Invalid on its own).
    always @(posedge clk) begin
        if (rst_n)
            ap_state_accuracy: assert (!pf_active
                || ((pf_addr == f_addr_q) && (pf_state == f_state_q)));
    end

    // P2 match implies armed (a snoop can never be answered from a retired
    // register).
    always @(posedge clk) begin
        if (rst_n)
            ap_match_implies_active: assert (!pf_match || pf_active);
    end

    // P3 the state-accuracy claim of MAS ch02/02: a matching snoop is answered
    // at the post-fill state, never the pre-fill Invalid.
    always @(posedge clk) begin
        if (rst_n)
            ap_never_pre_fill_i: assert (!pf_match || (pf_state != ST_I));
    end

    // P4 beat mask is monotonic while armed: bits only set, never cleared
    // (a beat, once received, stays received -- MAS ch02/06).
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0 && $past(rst_n) && $past(pf_active)
            && !$past(pf_load))
            ap_beats_monotonic: assert ((~pf_data_valid & $past(pf_data_valid)) == '0);
    end

    // P5 pf_beat_valid is exactly the mask bit at the presented index.
    always @(posedge clk) begin
        if (rst_n)
            ap_beat_valid_bit: assert (pf_beat_valid == pf_data_valid[pf_beat_idx]);
    end

    // P6 load wins over clear, clear wins over a beat strobe (the documented
    // priority), and a load resets the beat mask.
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0 && $past(rst_n)) begin
            if ($past(pf_load))
                ap_load_priority: assert (pf_active && (pf_data_valid == '0)
                    && (pf_addr == $past(pf_load_addr))
                    && (pf_state == $past(pf_load_state)));
            else if ($past(pf_clear))
                ap_clear_priority: assert (!pf_active);
            else if ($past(pf_beat_set))
                ap_beat_accum: assert (pf_data_valid[$past(pf_beat_idx)]);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    reg f_saw_load;
    always @(posedge clk) begin
        if (!rst_n) f_saw_load <= 1'b0;
        else if (pf_load) f_saw_load <= 1'b1;
        else if (pf_clear) f_saw_load <= 1'b0;
    end

    // A snoop mid-fill with only part of the beats received (the CD-gating
    // scenario the leaf exists for).
    always @(posedge clk) begin
        if (rst_n)
            cp_mid_fill_match: cover (pf_match && (pf_data_valid != '0)
                                      && (pf_data_valid != {FILL_BEATS{1'b1}}));
    end

    // Full lifecycle: load -> all beats -> clear.
    always @(posedge clk) begin
        if (rst_n)
            cp_full_lifecycle: cover (f_saw_load && (pf_data_valid == {FILL_BEATS{1'b1}})
                                      && pf_clear);
    end

endmodule
