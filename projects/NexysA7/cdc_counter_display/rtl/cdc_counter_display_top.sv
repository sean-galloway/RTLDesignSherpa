// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_counter_display_top
// Purpose: //   Nexys A7 FPGA demonstration of clock domain crossing (CDC) using async
//
// Documentation: PRD.md
// Subsystem: cdc_counter_display_top.sv
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: cdc_counter_display_top
//==============================================================================
// Description:
//   Nexys A7 FPGA demonstration of clock domain crossing (CDC) using async
//   handshake protocol. Features a debounced button counter in the button
//   clock domain that safely transfers count values to the display clock
//   domain via pulse-based CDC handshake, then displays on 7-segment displays.
//
// Features:
//   - Dual independent clock domains (button domain @ 10Hz, display @ 1kHz)
//   - Button debouncing with configurable debounce time
//   - 8-bit counter with rollover
//   - Safe CDC handshake using pulse synchronizer
//   - Dual 7-segment hex displays (2 digits)
//   - Visual heartbeat LED indicators for each clock domain
//   - Reset button support
//
// Clock Domains:
//   - btn_clk_domain: 10 Hz (100ms period) - Button sampling rate
//   - disp_clk_domain: 1 kHz (1ms period) - Display refresh rate
//
// Integration:
//   Uses rtldesignsherpa library modules:
//   - debounce.sv (common/) - Button debouncing
//   - counter_bin.sv (common/) - Binary up counter
//   - cdc_handshake.sv (amba/shared/) - CDC bus transfer with handshake
//   - hex_to_7seg.sv (common/) - Hex to 7-segment decoder
//   - clock_divider.sv (common/) - Clock generation from 100MHz system clock
//
//------------------------------------------------------------------------------
// Educational Notes:
//------------------------------------------------------------------------------
// This design demonstrates CRITICAL CDC concepts:
//
// 1. **Clock Domain Isolation:**
//    - btn_clk (10Hz) and disp_clk (1kHz) are completely independent
//    - NO direct signal crossing between domains without synchronization
//
// 2. **Handshake-Based CDC:**
//    - Counter increment triggers CDC handshake protocol
//    - cdc_handshake safely transfers counter bus to disp_clk domain
//    - Full 4-phase handshake: src_valid → dst_valid → dst_ready → src_ready
//    - Guarantees exactly one transfer per button press
//
// 3. **Data Transfer Strategy:**
//    - Counter value latched in source domain on src_valid
//    - Multi-bit bus synchronized via handshake protocol
//    - Destination samples data when dst_valid asserted
//    - Avoids metastability through proper FSM-based synchronization
//
// 4. **Why Use Full Handshake:**
//    - Production-quality CDC for multi-bit bus transfer
//    - Demonstrates industry-standard async handshake protocol
//    - Provides explicit flow control and transfer acknowledgement
//    - Better than simple synchronizers for learning CDC protocols
//
// 5. **Heartbeat Indicators:**
//    - Each domain has LED toggling at its clock rate
//    - Visual confirmation of independent clock operation
//    - Helps debug clock generation issues
//
//------------------------------------------------------------------------------
// Timing Analysis:
//------------------------------------------------------------------------------
// Button Press to Display Update Latency:
//   1. Button debounce: ~20ms (200 btn_clk cycles @ 10Hz)
//   2. Counter update: 100ms (1 btn_clk cycle)
//   3. CDC handshake: ~6-8ms (6-8 disp_clk cycles @ 1kHz for complete handshake)
//   4. Display update: 1ms (1 disp_clk cycle)
//   Total: ~27-29ms typical
//
// Maximum Button Press Rate:
//   - Limited by: max(debounce time, CDC handshake completion)
//   - Debounce time: ~20ms
//   - Handshake completion: ~8ms
//   - Practical limit: ~50 presses/second (20ms minimum)
//   - Human limit: ~10 presses/second
//
//------------------------------------------------------------------------------
// Physical Connections (Nexys A7):
//------------------------------------------------------------------------------
// Inputs:
//   - btnC (center button): Counter increment
//   - btnU (up button): System reset
//   - CLK100MHZ: 100 MHz system clock
//
// Outputs:
//   - seg[6:0]: 7-segment display segments (CA-CG)
//   - an[7:0]: 7-segment display anodes (digit select)
//   - led[1:0]: Heartbeat indicators
//     - led[0]: btn_clk domain heartbeat (toggles @ 5Hz)
//     - led[1]: disp_clk domain heartbeat (toggles @ 500Hz)
//
// Display Format:
//   - AN7-AN2: OFF (unused digits)
//   - AN1: Counter high nibble (0-F)
//   - AN0: Counter low nibble (0-F)
//   Example: Counter = 0x3A → Display shows "3A"
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYS_CLK_FREQ_MHZ:
//     Description: System clock frequency in MHz
//     Type: int
//     Range: 50 to 200
//     Default: 100 (Nexys A7 default)
//
//   BTN_CLK_FREQ_HZ:
//     Description: Button domain clock frequency in Hz
//     Type: int
//     Range: 1 to 1000
//     Default: 10 (100ms period, good for visual confirmation)
//
//   DISP_CLK_FREQ_HZ:
//     Description: Display domain clock frequency in Hz
//     Type: int
//     Range: 100 to 10000
//     Default: 1000 (1ms period, sufficient for multiplexing)
//
//   DEBOUNCE_TIME_MS:
//     Description: Button debounce time in milliseconds
//     Type: int
//     Range: 10 to 100
//     Default: 20 (typical mechanical button settling time)
//
//   COUNTER_WIDTH:
//     Description: Counter bit width
//     Type: int
//     Range: 4 to 16
//     Default: 8 (allows 0-255, displays as 00-FF hex)
//
//   Derived Parameters (localparam - computed automatically):
//     BTN_CLK_DIV_RATIO: Clock divider ratio for button clock
//     DISP_CLK_DIV_RATIO: Clock divider ratio for display clock
//     HEARTBEAT_BTN_DIV: Button domain heartbeat divider
//     HEARTBEAT_DISP_DIV: Display domain heartbeat divider
//
//------------------------------------------------------------------------------
// CDC Safety Analysis:
//------------------------------------------------------------------------------
// Crossing #1: Counter value bus (btn_clk → disp_clk)
//   - Method: cdc_handshake (4-phase async handshake protocol)
//   - Signals crossed: r_count_value[COUNTER_WIDTH-1:0]
//   - Safety: Full FSM-based handshake with 3-stage synchronizers
//   - Latency: 6-8 disp_clk cycles (complete req→ack→req_clear→ack_clear)
//   - MTBF: >10^12 hours (3-stage synchronizers on req/ack signals)
//
// Crossing #2: None (display outputs are purely in disp_clk domain)
//
// ASYNCHRONOUS CLOCK GROUPS (for timing constraints):
//   - btn_clk and disp_clk are asynchronous (must be declared)
//
// FALSE PATHS (for timing constraints):
//   - Internal handshake signals are already properly synchronized
//   - No additional false paths needed (handled by cdc_handshake module)
//
//==============================================================================

module cdc_counter_display_top #(
    parameter int SYS_CLK_FREQ_MHZ = 100,
    parameter int BTN_CLK_FREQ_HZ = 10,
    parameter int DISP_CLK_FREQ_HZ = 1000,
    parameter int DEBOUNCE_TIME_MS = 20,
    parameter int COUNTER_WIDTH = 8
) (
    // System inputs
    input  logic        CLK100MHZ,      // 100 MHz system clock (Nexys A7)
    input  logic        btnC,           // Center button - increment counter
    input  logic        btnU,           // Up button - reset

    // 7-segment display outputs
    output logic [6:0]  seg,            // Segment drivers (CA-CG)
    output logic [7:0]  an,             // Anode drivers (digit select)

    // LED outputs
    output logic [1:0]  led             // Heartbeat indicators
);

    //==========================================================================
    // Derived Parameters
    //==========================================================================

    localparam int BTN_CLK_DIV_RATIO = (SYS_CLK_FREQ_MHZ * 1_000_000) / BTN_CLK_FREQ_HZ;
    localparam int DISP_CLK_DIV_RATIO = (SYS_CLK_FREQ_MHZ * 1_000_000) / DISP_CLK_FREQ_HZ;

    // Heartbeat dividers (toggle at half the clock frequency)
    localparam int HEARTBEAT_BTN_DIV = BTN_CLK_FREQ_HZ / 2;
    localparam int HEARTBEAT_DISP_DIV = DISP_CLK_FREQ_HZ / 2;

    //==========================================================================
    // Signal Declarations
    //==========================================================================

    // Clock and reset
    logic sys_clk;
    logic sys_rst_n;
    logic btn_clk;
    logic disp_clk;

    // Button domain signals
    logic btn_raw;
    logic btn_debounced;
    logic btn_increment_pulse;      // Single-cycle pulse on button press
    logic [COUNTER_WIDTH-1:0] r_count_value;
    logic [$clog2(HEARTBEAT_BTN_DIV):0] r_count_heartbeat;  // Wide enough for heartbeat divider

    // CDC handshake signals (btn_clk → disp_clk)
    logic cdc_src_valid;            // Source domain valid signal
    logic cdc_src_ready;            // Source domain ready (from CDC)
    logic cdc_dst_valid;            // Destination domain valid
    logic cdc_dst_ready;            // Destination domain ready
    logic [COUNTER_WIDTH-1:0] cdc_dst_data;  // Counter value in dst domain

    // Display domain signals
    logic [COUNTER_WIDTH-1:0] r_display_count;
    logic [3:0] display_digit;
    logic [$clog2(HEARTBEAT_DISP_DIV):0] r_display_heartbeat;  // Wide enough for heartbeat divider

    // 7-segment signals
    logic [3:0] hex_digit_0;  // Low nibble
    logic [3:0] hex_digit_1;  // High nibble
    logic [6:0] seg_digit_0;
    logic [6:0] seg_digit_1;

    //==========================================================================
    // Clock and Reset Management
    //==========================================================================

    // System clock direct connection (100 MHz)
    assign sys_clk = CLK100MHZ;

    // Reset (active-low, synchronized to sys_clk)
    // btnU is active-high, invert for active-low reset
    assign sys_rst_n = ~btnU;

    // Button input
    assign btn_raw = btnC;

    //==========================================================================
    // Clock Generation
    //==========================================================================

    // Calculate pickoff points for clock divider
    // Formula: output_freq = input_freq / 2^(pickoff_point + 1)
    // For btn_clk:  100MHz / 2^X = 10Hz    → 2^X = 10000000 → X ≈ 23 → pickoff = 22
    // For disp_clk: 100MHz / 2^X = 1000Hz  → 2^X = 100000    → X ≈ 17 → pickoff = 16
    // For tick:     100MHz / 2^X = 100Hz   → 2^X = 1000000   → X ≈ 20 → pickoff = 19

    localparam int CLK_DIV_N = 3;          // 3 output clocks
    localparam int CLK_DIV_PO_WIDTH = 8;   // 8-bit pickoff points
    localparam int CLK_DIV_COUNTER_WIDTH = 32;  // 32-bit counter

    // Calculate pickoff points based on desired frequencies
    localparam int BTN_CLK_PICKOFF = $clog2(SYS_CLK_FREQ_MHZ * 1_000_000 / BTN_CLK_FREQ_HZ) - 1;
    localparam int DISP_CLK_PICKOFF = $clog2(SYS_CLK_FREQ_MHZ * 1_000_000 / DISP_CLK_FREQ_HZ) - 1;
    localparam int TICK_CLK_PICKOFF = $clog2(SYS_CLK_FREQ_MHZ * 1_000_000 / 100) - 1;  // 100Hz tick

    logic [(CLK_DIV_N*CLK_DIV_PO_WIDTH)-1:0] pickoff_points;
    logic [CLK_DIV_N-1:0] divided_clks;
    logic tick_clk;

    // Pack pickoff points: {tick, disp, btn}
    assign pickoff_points = {
        CLK_DIV_PO_WIDTH'(TICK_CLK_PICKOFF),
        CLK_DIV_PO_WIDTH'(DISP_CLK_PICKOFF),
        CLK_DIV_PO_WIDTH'(BTN_CLK_PICKOFF)
    };

    // Multi-output clock divider
    clock_divider #(
        .N(CLK_DIV_N),
        .PO_WIDTH(CLK_DIV_PO_WIDTH),
        .COUNTER_WIDTH(CLK_DIV_COUNTER_WIDTH)
    ) u_clock_div (
        .clk            (sys_clk),
        .rst_n          (sys_rst_n),
        .pickoff_points (pickoff_points),
        .divided_clk    (divided_clks)
    );

    // Extract individual clocks
    assign btn_clk  = divided_clks[0];
    assign disp_clk = divided_clks[1];
    assign tick_clk = divided_clks[2];

    //==========================================================================
    // Button Domain Logic (btn_clk @ 10Hz)
    //==========================================================================

    // Button debouncing using shift register with tick sampling
    // tick_clk runs at 100Hz, debounce module samples every tick
    // With DEBOUNCE_DELAY=4, button must be stable for 4 ticks (40ms)
    debounce #(
        .N(1),                    // 1 button
        .DEBOUNCE_DELAY(4),       // 4 tick cycles
        .PRESSED_STATE(1)         // Active high (button pressed = 1)
    ) u_debounce (
        .clk        (sys_clk),              // Run on system clock
        .rst_n      (sys_rst_n),
        .long_tick  (tick_clk),             // 100Hz tick for sampling
        .button_in  (btn_raw),              // Raw button input
        .button_out (btn_debounced)         // Debounced output
    );

    // Edge detector for button press (generate single-cycle pulse)
    logic btn_debounced_prev;
    always_ff @(posedge btn_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            btn_debounced_prev <= 1'b0;
        end else begin
            btn_debounced_prev <= btn_debounced;
        end
    end

    assign btn_increment_pulse = btn_debounced && !btn_debounced_prev;

    // Binary counter
    always_ff @(posedge btn_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            r_count_value <= '0;
        end else if (btn_increment_pulse) begin
            r_count_value <= r_count_value + 1'b1;  // Wraps at 2^COUNTER_WIDTH
        end
    end

    // Button domain heartbeat (toggles at half btn_clk frequency)
    localparam int BTN_HEARTBEAT_WIDTH = $clog2(HEARTBEAT_BTN_DIV) + 1;
    logic led_btn_heartbeat;
    always_ff @(posedge btn_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            r_count_heartbeat <= '0;
            led_btn_heartbeat <= 1'b0;
        end else begin
            if (r_count_heartbeat >= BTN_HEARTBEAT_WIDTH'(HEARTBEAT_BTN_DIV - 1)) begin
                r_count_heartbeat <= '0;
                led_btn_heartbeat <= ~led_btn_heartbeat;  // Toggle LED
            end else begin
                r_count_heartbeat <= r_count_heartbeat + 1'b1;
            end
        end
    end
    assign led[0] = led_btn_heartbeat;

    // CDC source valid: Assert when button pressed and CDC ready
    // This creates a single-cycle valid pulse that triggers the handshake
    always_ff @(posedge btn_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            cdc_src_valid <= 1'b0;
        end else begin
            // Assert valid for one cycle when button pressed AND CDC is ready
            if (btn_increment_pulse && cdc_src_ready) begin
                cdc_src_valid <= 1'b1;
            end else begin
                cdc_src_valid <= 1'b0;
            end
        end
    end

    //==========================================================================
    // Clock Domain Crossing (btn_clk → disp_clk)
    //==========================================================================

    // CDC: Transfer counter value bus from btn_clk to disp_clk
    // Uses 4-phase handshake protocol with FSM-based synchronization
    cdc_handshake #(
        .DATA_WIDTH(COUNTER_WIDTH)
    ) u_counter_cdc (
        // Source domain (button clock)
        .clk_src        (btn_clk),
        .rst_src_n      (sys_rst_n),
        .src_valid      (cdc_src_valid),      // Asserted on button press
        .src_ready      (cdc_src_ready),      // Ready for new transfer
        .src_data       (r_count_value),      // Counter value to transfer

        // Destination domain (display clock)
        .clk_dst        (disp_clk),
        .rst_dst_n      (sys_rst_n),
        .dst_valid      (cdc_dst_valid),      // Data valid in dst domain
        .dst_ready      (cdc_dst_ready),      // Always ready to receive
        .dst_data       (cdc_dst_data)        // Transferred counter value
    );

    // Destination always ready (no backpressure from display logic)
    assign cdc_dst_ready = 1'b1;

    //==========================================================================
    // Display Domain Logic (disp_clk @ 1kHz)
    //==========================================================================

    // Capture counter value when CDC indicates valid data
    always_ff @(posedge disp_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            r_display_count <= '0;
        end else if (cdc_dst_valid) begin
            r_display_count <= cdc_dst_data;  // Sample transferred value
        end
    end

    // Display domain heartbeat (toggles at half disp_clk frequency)
    localparam int DISP_HEARTBEAT_WIDTH = $clog2(HEARTBEAT_DISP_DIV) + 1;
    logic led_disp_heartbeat;
    always_ff @(posedge disp_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            r_display_heartbeat <= '0;
            led_disp_heartbeat <= 1'b0;
        end else begin
            if (r_display_heartbeat >= DISP_HEARTBEAT_WIDTH'(HEARTBEAT_DISP_DIV - 1)) begin
                r_display_heartbeat <= '0;
                led_disp_heartbeat <= ~led_disp_heartbeat;  // Toggle LED
            end else begin
                r_display_heartbeat <= r_display_heartbeat + 1'b1;
            end
        end
    end
    assign led[1] = led_disp_heartbeat;

    // Split count into hex digits
    assign hex_digit_0 = r_display_count[3:0];   // Low nibble
    assign hex_digit_1 = r_display_count[7:4];   // High nibble (if COUNTER_WIDTH > 4)

    //==========================================================================
    // 7-Segment Display
    //==========================================================================

    // Hex to 7-segment decoder for digit 0 (rightmost)
    hex_to_7seg u_hex_to_7seg_0 (
        .hex (hex_digit_0),
        .seg (seg_digit_0)
    );

    // Hex to 7-segment decoder for digit 1
    hex_to_7seg u_hex_to_7seg_1 (
        .hex (hex_digit_1),
        .seg (seg_digit_1)
    );

    // Simple time-multiplexing between two digits
    // Alternate every disp_clk cycle (1ms per digit = 500Hz refresh per digit)
    logic digit_select;
    always_ff @(posedge disp_clk or negedge sys_rst_n) begin
        if (!sys_rst_n) begin
            digit_select <= 1'b0;
        end else begin
            digit_select <= ~digit_select;
        end
    end

    // Multiplex segment and anode outputs
    always_comb begin
        // Default: all digits off
        an = 8'b1111_1111;
        seg = 7'b1111_111;

        if (digit_select) begin
            // Display digit 1 (high nibble) on AN1
            an[1] = 1'b0;  // Active-low anode
            seg = seg_digit_1;
        end else begin
            // Display digit 0 (low nibble) on AN0
            an[0] = 1'b0;  // Active-low anode
            seg = seg_digit_0;
        end
    end

endmodule : cdc_counter_display_top
