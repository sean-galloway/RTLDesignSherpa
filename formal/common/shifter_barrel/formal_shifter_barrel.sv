// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for shifter_barrel (yosys-compatible)

module formal_shifter_barrel #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    localparam int SHIFT_BITS = $clog2(WIDTH) + 1;

    (* anyconst *) logic [WIDTH-1:0]      data;
    (* anyconst *) logic [2:0]            ctrl;
    (* anyconst *) logic [SHIFT_BITS-1:0] shift_amount;

    logic [WIDTH-1:0] data_out;

    shifter_barrel #(.WIDTH(WIDTH)) dut (
        .data        (data),
        .ctrl        (ctrl),
        .shift_amount(shift_amount),
        .data_out    (data_out)
    );

    // Clamped shift amount modulo WIDTH (matching RTL)
    logic [$clog2(WIDTH)-1:0] shift_mod;
    assign shift_mod = shift_amount[$clog2(WIDTH)-1:0];

    // Reference model: compute expected output for each mode
    logic [WIDTH-1:0] f_expected;
    always_comb begin
        case (ctrl)
            3'b000: f_expected = data;
            3'b001: f_expected = (shift_mod == 0) ? data : data >> shift_amount;
            3'b010: f_expected = $signed(data) >>> shift_mod;
            3'b011: begin
                // Right rotation: lower bits wrap to top
                if (shift_mod == 0)
                    f_expected = data;
                else
                    f_expected = (data >> shift_mod) | (data << (WIDTH - shift_mod));
            end
            3'b100: f_expected = (shift_mod == 0) ? data : data << shift_amount;
            3'b110: begin
                // Left rotation: upper bits wrap to bottom
                if (shift_mod == 0)
                    f_expected = data;
                else
                    f_expected = (data << shift_mod) | (data >> (WIDTH - shift_mod));
            end
            default: f_expected = data;
        endcase
    end

    // =========================================================================
    // Master equivalence: output matches reference model
    // =========================================================================

    always @(posedge clk)
        ap_equiv: assert (data_out == f_expected);

    // =========================================================================
    // Safety properties: NOP (ctrl == 3'b000)
    // =========================================================================

    always @(posedge clk)
        if (ctrl == 3'b000)
            ap_nop: assert (data_out == data);

    // =========================================================================
    // Safety properties: Logical Right Shift (ctrl == 3'b001)
    // =========================================================================

    // When shift_mod is 0, RTL returns data unchanged (identity)
    always @(posedge clk)
        if (ctrl == 3'b001 && shift_mod == 0)
            ap_lsr_zero: assert (data_out == data);

    // Non-zero shift with shift_amount < WIDTH: standard right shift
    always @(posedge clk)
        if (ctrl == 3'b001 && shift_amount > 0 && shift_amount < WIDTH)
            ap_lsr_shift: assert (data_out == (data >> shift_amount));

    // =========================================================================
    // Safety properties: Arithmetic Right Shift (ctrl == 3'b010)
    // =========================================================================

    // Sign bit is preserved in output MSB when shifting
    always @(posedge clk)
        if (ctrl == 3'b010 && shift_mod > 0 && data[WIDTH-1])
            ap_asr_sign_fill: assert (data_out[WIDTH-1]);

    // When input MSB is 0, ASR matches LSR for clamped amount
    always @(posedge clk)
        if (ctrl == 3'b010 && !data[WIDTH-1])
            ap_asr_positive: assert (data_out == (data >> shift_mod));

    // =========================================================================
    // Safety properties: Logical Left Shift (ctrl == 3'b100)
    // =========================================================================

    // When shift_mod is 0, RTL returns data unchanged (identity)
    always @(posedge clk)
        if (ctrl == 3'b100 && shift_mod == 0)
            ap_lsl_zero: assert (data_out == data);

    // Non-zero shift with shift_amount < WIDTH: standard left shift
    always @(posedge clk)
        if (ctrl == 3'b100 && shift_amount > 0 && shift_amount < WIDTH)
            ap_lsl_shift: assert (data_out == (data << shift_amount));

    // =========================================================================
    // Safety properties: Right Rotation (ctrl == 3'b011)
    // =========================================================================

    // Rotation preserves all bits (popcount unchanged)
    always @(posedge clk)
        if (ctrl == 3'b011)
            ap_ror_popcount: assert ($countones(data_out) == $countones(data));

    // Rotation by 0 is identity
    always @(posedge clk)
        if (ctrl == 3'b011 && shift_mod == 0)
            ap_ror_zero: assert (data_out == data);

    // =========================================================================
    // Safety properties: Left Rotation (ctrl == 3'b110)
    // =========================================================================

    // Rotation preserves all bits (popcount unchanged)
    always @(posedge clk)
        if (ctrl == 3'b110)
            ap_rol_popcount: assert ($countones(data_out) == $countones(data));

    // Rotation by 0 is identity
    always @(posedge clk)
        if (ctrl == 3'b110 && shift_mod == 0)
            ap_rol_zero: assert (data_out == data);

    // =========================================================================
    // Safety properties: Default cases (ctrl == 3'b101, 3'b111)
    // =========================================================================

    always @(posedge clk)
        if (ctrl == 3'b101 || ctrl == 3'b111)
            ap_default: assert (data_out == data);

    // =========================================================================
    // Cover properties: each shift mode exercised
    // =========================================================================

    always @(posedge clk)
        cp_nop: cover (ctrl == 3'b000 && data != '0);

    always @(posedge clk)
        cp_lsr: cover (ctrl == 3'b001 && shift_amount > 0 && shift_amount < WIDTH && data != '0);

    always @(posedge clk)
        cp_asr_neg: cover (ctrl == 3'b010 && shift_mod > 0 && data[WIDTH-1]);

    always @(posedge clk)
        cp_asr_pos: cover (ctrl == 3'b010 && shift_mod > 0 && !data[WIDTH-1] && data != '0);

    always @(posedge clk)
        cp_ror: cover (ctrl == 3'b011 && shift_mod > 0 && data != '0);

    always @(posedge clk)
        cp_lsl: cover (ctrl == 3'b100 && shift_amount > 0 && shift_amount < WIDTH && data != '0);

    always @(posedge clk)
        cp_rol: cover (ctrl == 3'b110 && shift_mod > 0 && data != '0);

    always @(posedge clk)
        cp_full_rotate_right: cover (ctrl == 3'b011 && shift_mod == 3'd4 && data == 8'hA5);

    always @(posedge clk)
        cp_full_rotate_left: cover (ctrl == 3'b110 && shift_mod == 3'd4 && data == 8'hA5);

endmodule
