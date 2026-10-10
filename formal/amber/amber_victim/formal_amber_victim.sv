// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for amber_victim (yosys-compatible)
// Run with: sby amber_victim.sby
//
// Task 13 proof (MAS ch02_blocks/05, standalone leaf at the tiny geometry
// LINE_BYTES=64 / BUS_WIDTH=64 -> a 512-bit victim line).
//
// Assumption inventory: none on the environment beyond the house reset
// protocol -- every input is free. The leaf must be safe for ANY load/clear
// timing (the control FSM is well-behaved, but the guard must hold even for
// a broken requester).
//
// Abstraction: none -- the whole leaf is the DUT; no memories inside.

module formal_amber_victim (
    input  logic        clk,
    input  logic        rst_n,

    // free environment inputs
    input  logic        victim_load,
    input  logic [31:0] victim_addr_in,
    input  logic [511:0] victim_data_in,
    input  logic        victim_clear
);

    localparam ADDR_WIDTH = 32;
    localparam LINE_WIDTH = 512;

    // DUT outputs
    logic                      victim_busy;
    logic                      victim_empty;
    logic                      victim_valid;
    logic [ADDR_WIDTH-1:0]     victim_addr;
    logic [LINE_WIDTH-1:0]     victim_data;

    amber_victim #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (16),
        .LINE_BYTES (64),
        .BUS_WIDTH  (64)
    ) dut (
        .clk            (clk),
        .rst_n          (rst_n),
        .victim_load    (victim_load),
        .victim_addr_in (victim_addr_in),
        .victim_data_in (victim_data_in),
        .victim_clear   (victim_clear),
        .victim_busy    (victim_busy),
        .victim_empty   (victim_empty),
        .victim_valid   (victim_valid),
        .victim_addr    (victim_addr),
        .victim_data    (victim_data)
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

    // =========================================================================
    // Ghost mirror of the accepted load (the load that actually landed)
    // =========================================================================
    reg                      f_loaded_q;
    reg [ADDR_WIDTH-1:0]     f_addr_q;
    reg [LINE_WIDTH-1:0]     f_data_q;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_loaded_q <= 1'b0;
            f_addr_q   <= '0;
            f_data_q   <= '0;
        end else if (victim_clear) begin
            // mirror the RTL priority: clear wins over a coincident load
            f_loaded_q <= 1'b0;
        end else if (victim_load && !victim_valid) begin
            // mirror the guard: only a load accepted while empty lands
            f_loaded_q <= 1'b1;
            f_addr_q   <= victim_addr_in;
            f_data_q   <= victim_data_in;
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // V1 never loaded while busy (MAS ch02_blocks/05, Review Focus 2): a load
    // requested while a victim's write-back is still in flight is ignored,
    // never overwriting the buffer.
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0 && $past(rst_n)
            && $past(victim_load) && $past(victim_valid) && !$past(victim_clear))
            ap_never_loaded_busy: assert (victim_valid
                && (victim_addr == $past(victim_addr))
                && (victim_data == $past(victim_data)));
    end

    // V2 handoff payload: once loaded, the buffer holds exactly the staged
    // address and line data, stably, for as long as it is valid.
    always @(posedge clk) begin
        if (rst_n)
            ap_payload_stable: assert (!victim_valid
                || ((victim_addr == f_addr_q) && (victim_data == f_data_q)));
    end

    // V3 occupancy: valid from the accepted load until the clear (drain-done
    // ordering); a clear on an empty buffer retires nothing.
    always @(posedge clk) begin
        if (rst_n) begin
            ap_busy_is_valid:  assert (victim_busy == victim_valid);
            ap_empty_is_nvalid: assert (victim_empty == !victim_valid);
        end
    end

    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0 && $past(rst_n)) begin
            // load accepted while empty -> valid with the staged payload
            // (a coincident clear wins, so it is excluded)
            if ($past(victim_load) && !$past(victim_valid) && !$past(victim_clear))
                ap_load_lands: assert (victim_valid
                    && (victim_addr == $past(victim_addr_in))
                    && (victim_data == $past(victim_data_in)));
            // valid survives until the clear arrives
            if ($past(victim_valid) && !$past(victim_clear))
                ap_holds_until_clear: assert (victim_valid);
            // clear (no coincident load) empties the buffer
            if ($past(victim_clear) && !$past(victim_load))
                ap_clear_empties: assert (!victim_valid);
            // clear wins if both ever coincided (documented priority)
            if ($past(victim_clear))
                ap_clear_priority: assert (!victim_valid);
        end
    end

    // V4 the buffer is only ever occupied by an accepted load: valid implies
    // a load landed earlier and nothing has been cleared since.
    always @(posedge clk) begin
        if (rst_n)
            ap_valid_implies_loaded: assert (!victim_valid || f_loaded_q);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    reg f_saw_valid;
    always @(posedge clk) begin
        if (!rst_n) f_saw_valid <= 1'b0;
        else if (victim_valid) f_saw_valid <= 1'b1;
        else if (victim_clear) f_saw_valid <= 1'b0;
    end

    // The depth-1 cycle the buffer exists for: load -> busy -> clear -> empty,
    // then reusable.
    always @(posedge clk) begin
        if (rst_n)
            cp_load_clear_reload: cover (f_saw_valid && victim_clear
                && victim_load && !victim_valid);
    end

endmodule
