`timescale 1ns / 1ps

module counter_freq_invariant
#(
    parameter int COUNTER_WIDTH = 5      // Width of the output counter
) (
    input  logic                        i_clk,         // Input clock
    input  logic                        i_rst_n,       // Active low reset
    input  logic [3:0]                  i_freq_sel,    // Frequency selection (configurable)
    output logic [COUNTER_WIDTH-1:0]    o_counter,     // 5-bit output counter
    output logic                        o_tick         // Pulse every time counter increments
);

    // Configuration registers
    logic [15:0] w_division_factor;     // How many clock cycles per tick

    // Frequency selection change detection
    logic [3:0] r_prev_freq_sel;        // Previous frequency selection
    logic       r_clear_pulse;     // Indicates frequency selection changed

    // Internal counters
    logic w_prescaler_done;

    // Config lookup - Maps i_freq_sel to division factors
    always_comb begin
        case (i_freq_sel)
            4'b0000: w_division_factor = 16'd1;      // 1000MHz (1GHz)  - 1:1 division
            4'b0001: w_division_factor = 16'd10;     // 100MHz          - 10:1 division
            4'b0010: w_division_factor = 16'd20;     // 50MHz           - 20:1 division
            4'b0011: w_division_factor = 16'd25;     // 40MHz           - 25:1 division
            4'b0100: w_division_factor = 16'd40;     // 25MHz           - 40:1 division
            4'b0101: w_division_factor = 16'd50;     // 20MHz           - 50:1 division
            4'b0110: w_division_factor = 16'd80;     // 12.5MHz         - 80:1 division
            4'b0111: w_division_factor = 16'd100;    // 10MHz           - 100:1 division
            4'b1000: w_division_factor = 16'd125;    // 8MHz            - 125:1 division
            4'b1001: w_division_factor = 16'd200;    // 5MHz            - 200:1 division
            4'b1010: w_division_factor = 16'd250;    // 4MHz            - 250:1 division
            4'b1011: w_division_factor = 16'd500;    // 2MHz            - 500:1 division
            4'b1100: w_division_factor = 16'd1000;   // 1MHz            - 1000:1 division
            4'b1101: w_division_factor = 16'd2000;   // 500kHz          - 2000:1 division
            4'b1110: w_division_factor = 16'd5000;   // 200kHz          - 5000:1 division
            4'b1111: w_division_factor = 16'd10000;  // 100kHz          - 10000:1 division
            default: w_division_factor = 16'd1;      // Default to 1:1
        endcase
    end

    // Detect frequency selection changes
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_prev_freq_sel <= 4'b0;
            r_clear_pulse <= 1'b0;
        end
        else begin
            r_prev_freq_sel <= i_freq_sel;

            // Pulse w_freq_sel_changed for one cycle when i_freq_sel changes
            r_clear_pulse <= (i_freq_sel != r_prev_freq_sel);
        end
    end

    // Prescaler counter using the provided counter_load_clear
    counter_load_clear #(
        .MAX(16'hFFFF)  // Max value for the prescaler
    ) prescaler_counter (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_clear(r_clear_pulse),         // Clear the prescaler when frequency selection changes
        .i_increment(1'b1),              // Always increment
        .i_load(1'b1),                   // Always have a valid load value
        .i_loadval(w_division_factor-1), // Load the division factor (minus 1)
        .o_count(),
        .ow_done(w_prescaler_done)
    );

    // Generate tick signal and
    // COUNTER_WIDTH-bit output counter that increments on tick
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            o_counter <= 'b0;
            o_tick <= 'b0;
        end
        else begin
            if (w_prescaler_done && &o_counter)
                o_tick <= 'b1;
            else
                o_tick <= 'b0;

            if (r_clear_pulse)
                o_counter <= 'b0;
            else if (w_prescaler_done)
                o_counter <= o_counter + 1'b1;  // Will naturally roll over at 2^COUNTER_WIDTH
        end
    end

endmodule : counter_freq_invariant
