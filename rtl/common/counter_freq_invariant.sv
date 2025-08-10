`timescale 1ns / 1ps

/**
 * Frequency Invariant Counter with Microsecond Tick Generation
 *
 * CIRCUIT DESCRIPTION:
 * ===================
 * This module generates a frequency-invariant microsecond tick and maintains a counter
 * that increments every microsecond, regardless of the input clock frequency.
 *
 * The circuit consists of three main components:
 * 1. Frequency Selection Logic: Maps 7-bit freq_sel to division factors
 * 2. Prescaler Counter: Divides input clock to generate microsecond ticks
 * 3. Output Counter: Counts microseconds and generates tick pulses
 *
 * PROGRAMMING MODEL:
 * ==================
 * 1. Initial State: sync_reset_n = 0 (module in reset state)
 * 2. Programming: Set freq_sel[6:0] to desired frequency, then set sync_reset_n = 1
 * 3. Operation: Module generates 1MHz tick rate (1 tick per microsecond)
 * 4. Frequency Change: Set sync_reset_n = 0, change freq_sel, then set sync_reset_n = 1
 *
 * SUPPORTED FREQUENCIES:
 * ======================
 * Input clock frequencies from 100MHz to 2GHz are supported.
 * The freq_sel encoding provides fine-grained frequency selection.
 * All frequencies generate a consistent 1MHz output tick rate.
 *
 * TIMING:
 * =======
 * - tick: Asserts for one clock cycle every microsecond
 * - counter: Increments every microsecond, rolls over at 2^COUNTER_WIDTH
 * - Frequency changes cause immediate reset of internal counters
 */
module counter_freq_invariant
#(
    parameter int COUNTER_WIDTH = 16,     // Width of the output counter (default 16-bit = ~65ms rollover)
    parameter int PRESCALER_MAX = 2048    // Maximum value of the pre-scaler (supports up to 2GHz)
) (
    input  logic                        clk,         // Input clock (100MHz to 2GHz)
    input  logic                        rst_n,       // Active low reset
    input  logic                        sync_reset_n,// Synchronous reset (0=reset, 1=run)
    input  logic [6:0]                  freq_sel,    // Frequency selection (7-bit for fine control)
    output logic [COUNTER_WIDTH-1:0]    counter,     // Output counter (increments every microsecond)
    output logic                        tick         // Pulse every microsecond
);

    // Configuration registers (combinational)
    logic [10:0] w_division_factor;     // Clock cycles per microsecond (up to 2000 for 2GHz)

    // Frequency selection change detection (flopped)
    logic [6:0] r_prev_freq_sel;        // Previous frequency selection
    logic       r_clear_pulse;          // Indicates frequency selection changed or sync reset

    // Internal counters (combinational)
    logic w_prescaler_done;

    // Frequency lookup table - Maps freq_sel to division factors for 1MHz output
    // Each entry represents clock cycles needed for 1 microsecond
    always_comb begin
        case (freq_sel)
            // 100-200 MHz range
            7'd0:   w_division_factor = 11'd100;    // 100MHz   -> 100 cycles/μs
            7'd1:   w_division_factor = 11'd105;    // 105MHz   -> 105 cycles/μs
            7'd2:   w_division_factor = 11'd110;    // 110MHz   -> 110 cycles/μs
            7'd3:   w_division_factor = 11'd115;    // 115MHz   -> 115 cycles/μs
            7'd4:   w_division_factor = 11'd120;    // 120MHz   -> 120 cycles/μs
            7'd5:   w_division_factor = 11'd125;    // 125MHz   -> 125 cycles/μs
            7'd6:   w_division_factor = 11'd130;    // 130MHz   -> 130 cycles/μs
            7'd7:   w_division_factor = 11'd135;    // 135MHz   -> 135 cycles/μs
            7'd8:   w_division_factor = 11'd140;    // 140MHz   -> 140 cycles/μs
            7'd9:   w_division_factor = 11'd145;    // 145MHz   -> 145 cycles/μs
            7'd10:  w_division_factor = 11'd150;    // 150MHz   -> 150 cycles/μs
            7'd11:  w_division_factor = 11'd160;    // 160MHz   -> 160 cycles/μs
            7'd12:  w_division_factor = 11'd170;    // 170MHz   -> 170 cycles/μs
            7'd13:  w_division_factor = 11'd180;    // 180MHz   -> 180 cycles/μs
            7'd14:  w_division_factor = 11'd190;    // 190MHz   -> 190 cycles/μs
            7'd15:  w_division_factor = 11'd200;    // 200MHz   -> 200 cycles/μs

            // 200-500 MHz range
            7'd16:  w_division_factor = 11'd220;    // 220MHz   -> 220 cycles/μs
            7'd17:  w_division_factor = 11'd240;    // 240MHz   -> 240 cycles/μs
            7'd18:  w_division_factor = 11'd250;    // 250MHz   -> 250 cycles/μs
            7'd19:  w_division_factor = 11'd260;    // 260MHz   -> 260 cycles/μs
            7'd20:  w_division_factor = 11'd280;    // 280MHz   -> 280 cycles/μs
            7'd21:  w_division_factor = 11'd300;    // 300MHz   -> 300 cycles/μs
            7'd22:  w_division_factor = 11'd320;    // 320MHz   -> 320 cycles/μs
            7'd23:  w_division_factor = 11'd340;    // 340MHz   -> 340 cycles/μs
            7'd24:  w_division_factor = 11'd360;    // 360MHz   -> 360 cycles/μs
            7'd25:  w_division_factor = 11'd380;    // 380MHz   -> 380 cycles/μs
            7'd26:  w_division_factor = 11'd400;    // 400MHz   -> 400 cycles/μs
            7'd27:  w_division_factor = 11'd420;    // 420MHz   -> 420 cycles/μs
            7'd28:  w_division_factor = 11'd440;    // 440MHz   -> 440 cycles/μs
            7'd29:  w_division_factor = 11'd460;    // 460MHz   -> 460 cycles/μs
            7'd30:  w_division_factor = 11'd480;    // 480MHz   -> 480 cycles/μs
            7'd31:  w_division_factor = 11'd500;    // 500MHz   -> 500 cycles/μs

            // 500MHz-1GHz range
            7'd32:  w_division_factor = 11'd520;    // 520MHz   -> 520 cycles/μs
            7'd33:  w_division_factor = 11'd540;    // 540MHz   -> 540 cycles/μs
            7'd34:  w_division_factor = 11'd560;    // 560MHz   -> 560 cycles/μs
            7'd35:  w_division_factor = 11'd580;    // 580MHz   -> 580 cycles/μs
            7'd36:  w_division_factor = 11'd600;    // 600MHz   -> 600 cycles/μs
            7'd37:  w_division_factor = 11'd620;    // 620MHz   -> 620 cycles/μs
            7'd38:  w_division_factor = 11'd640;    // 640MHz   -> 640 cycles/μs
            7'd39:  w_division_factor = 11'd660;    // 660MHz   -> 660 cycles/μs
            7'd40:  w_division_factor = 11'd680;    // 680MHz   -> 680 cycles/μs
            7'd41:  w_division_factor = 11'd700;    // 700MHz   -> 700 cycles/μs
            7'd42:  w_division_factor = 11'd750;    // 750MHz   -> 750 cycles/μs
            7'd43:  w_division_factor = 11'd800;    // 800MHz   -> 800 cycles/μs
            7'd44:  w_division_factor = 11'd850;    // 850MHz   -> 850 cycles/μs
            7'd45:  w_division_factor = 11'd900;    // 900MHz   -> 900 cycles/μs
            7'd46:  w_division_factor = 11'd950;    // 950MHz   -> 950 cycles/μs
            7'd47:  w_division_factor = 11'd1000;   // 1000MHz  -> 1000 cycles/μs

            // 1GHz-1.5GHz range
            7'd48:  w_division_factor = 11'd1050;   // 1050MHz  -> 1050 cycles/μs
            7'd49:  w_division_factor = 11'd1100;   // 1100MHz  -> 1100 cycles/μs
            7'd50:  w_division_factor = 11'd1150;   // 1150MHz  -> 1150 cycles/μs
            7'd51:  w_division_factor = 11'd1200;   // 1200MHz  -> 1200 cycles/μs
            7'd52:  w_division_factor = 11'd1250;   // 1250MHz  -> 1250 cycles/μs
            7'd53:  w_division_factor = 11'd1300;   // 1300MHz  -> 1300 cycles/μs
            7'd54:  w_division_factor = 11'd1350;   // 1350MHz  -> 1350 cycles/μs
            7'd55:  w_division_factor = 11'd1400;   // 1400MHz  -> 1400 cycles/μs
            7'd56:  w_division_factor = 11'd1450;   // 1450MHz  -> 1450 cycles/μs
            7'd57:  w_division_factor = 11'd1500;   // 1500MHz  -> 1500 cycles/μs

            // 1.5GHz-2GHz range
            7'd58:  w_division_factor = 11'd1550;   // 1550MHz  -> 1550 cycles/μs
            7'd59:  w_division_factor = 11'd1600;   // 1600MHz  -> 1600 cycles/μs
            7'd60:  w_division_factor = 11'd1650;   // 1650MHz  -> 1650 cycles/μs
            7'd61:  w_division_factor = 11'd1700;   // 1700MHz  -> 1700 cycles/μs
            7'd62:  w_division_factor = 11'd1750;   // 1750MHz  -> 1750 cycles/μs
            7'd63:  w_division_factor = 11'd1800;   // 1800MHz  -> 1800 cycles/μs
            7'd64:  w_division_factor = 11'd1850;   // 1850MHz  -> 1850 cycles/μs
            7'd65:  w_division_factor = 11'd1900;   // 1900MHz  -> 1900 cycles/μs
            7'd66:  w_division_factor = 11'd1950;   // 1950MHz  -> 1950 cycles/μs
            7'd67:  w_division_factor = 11'd2000;   // 2000MHz  -> 2000 cycles/μs

            // Reserved for future expansion
            default: w_division_factor = 11'd1000;  // Default to 1GHz
        endcase
    end

    // Detect frequency selection changes and sync reset
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_prev_freq_sel <= 7'b0;
            r_clear_pulse <= 1'b1;  // Start in reset state
        end
        else begin
            r_prev_freq_sel <= freq_sel;

            // Generate clear pulse when:
            // 1. Frequency selection changes
            // 2. sync_reset_n is deasserted (synchronous reset active)
            r_clear_pulse <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
        end
    end

    // Prescaler counter using the provided counter_load_clear
    // This generates a done pulse every microsecond
    counter_load_clear #(
        .MAX            (PRESCALER_MAX)
    ) prescaler_counter(
        .clk            (clk),
        .rst_n          (rst_n),
        .clear          (r_clear_pulse),         // Clear when frequency changes or sync reset
        .increment      (1'b1),                  // Always increment
        .load           (1'b1),                  // Always load the division factor
        .loadval        (w_division_factor[$clog2(PRESCALER_MAX)-1:0] - 1'b1), // Load cycles-1 for proper timing
        .done           (w_prescaler_done),
        /* verilator lint_off PINCONNECTEMPTY */
        .count          ()                       // Internal count not needed
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Generate microsecond tick signal and maintain output counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 'b0;
            tick <= 1'b0;
        end
        else begin
            // Clear has highest priority - reset counter when in sync reset or frequency changes
            if (r_clear_pulse) begin
                counter <= 'b0;
                tick <= 1'b0;
            end
            else begin
                // Generate tick pulse every microsecond (only when not in sync reset)
                if (w_prescaler_done && sync_reset_n) begin
                    tick <= 1'b1;
                    counter <= counter + 1'b1;  // Increment counter every microsecond
                end
                else begin
                    tick <= 1'b0;
                    // Keep counter value unchanged
                end
            end
        end
    end

endmodule : counter_freq_invariant
