//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: clock_divider
        // Purpose: //   Multi-output programmable clock divider that generates up to N divided clock
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: clock_divider
        //==============================================================================
        // Description:
        //   Multi-output programmable clock divider that generates up to N divided clock
        //   outputs from a single input clock. Uses configurable "pickoff points" to select
        //   counter bits as clock sources, enabling flexible power-of-2 division ratios.
        //   Useful for generating multiple test clocks, baud rate generators, and debug
        //   clock outputs. NOT recommended for functional clocks (use PLL/clock managers).
        //
        // Features:
        //   - Up to N independent divided clock outputs
        //   - Runtime programmable division ratios (via pickoff_points)
        //   - Binary counter with bit-select outputs (power-of-2 divisions)
        //   - Wide counter width (up to 64-bit) for ultra-low frequencies
        //   - Automatic clamping of out-of-range pickoff values
        //   - Registered outputs (glitch-free)
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   N:
        //     Description: Number of divided clock outputs
        //     Type: int
        //     Range: 1 to 16
        //     Default: 4
        //     Constraints: Each output independently configurable
        //                  Resource usage: N registers + N muxes
        //
        //   PO_WIDTH:
        //     Description: Width of each pickoff point register (bits)
        //     Type: int
        //     Range: 4 to 8
        //     Default: 8
        //     Constraints: Must be > $clog2(COUNTER_WIDTH) to avoid truncation
        //                  Equivalently: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)
        //                  This ensures PO_WIDTH can hold the value COUNTER_WIDTH
        //                  Larger values allow finer counter bit selection
        //                  Examples: CW=16 needs PO≥5, CW=32 needs PO≥6, CW=64 needs PO≥7
        //                  Typical: PO_WIDTH=8 for COUNTER_WIDTH up to 128
        //
        //   COUNTER_WIDTH:
        //     Description: Width of binary counter (determines max division)
        //     Type: int
        //     Range: 2 to 64
        //     Default: 64
        //     Constraints: Max division = 2^COUNTER_WIDTH
        //                  Larger counter → slower min frequency, more resources
        //                  Example: WIDTH=16 → div by 65536 max
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     clk:                       Input clock (source to be divided)
        //     rst_n:                     Asynchronous active-low reset
        //     pickoff_points[N*PO_WIDTH-1:0]: Packed pickoff point configuration
        //                                     Format: {po[N-1], ..., po[1], po[0]}
        //                                     Each po[i] = counter bit index to sample
        //
        //   Outputs:
        //     divided_clk[N-1:0]:        Divided clock outputs (registered)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency:        1 cycle (output registered)
        //   Clock-to-Q:     Standard flip-flop delay
        //   Division Ratio: 2^(pickoff_point+1) (e.g., pickoff=3 → divide by 16)
        //   Output Duty:    50% (square wave from counter bit toggle)
        //   Jitter:         Input clock jitter + 1 cycle quantization
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Counter Operation:
        //   - r_divider_counters increments every input clock cycle
        //   - Counter wraps at 2^COUNTER_WIDTH (free-running binary counter)
        //   - Each bit toggles at half the frequency of the previous bit
        //   - Bit 0 toggles every cycle (clk/2), bit 1 every 2 cycles (clk/4), etc.
        //
        //   Pickoff Point Selection:
        //   - Each output i samples counter bit at pickoff_points[i*PO_WIDTH +: PO_WIDTH]
        //   - pickoff_point = N → output = counter[N] → frequency = clk / 2^(N+1)
        //   - Example: pickoff=0 → clk/2, pickoff=1 → clk/4, pickoff=5 → clk/64
        //
        //   Out-of-Range Handling:
        //   - If pickoff_points[i] ≥ COUNTER_WIDTH, clamp to COUNTER_WIDTH-1 (MSB)
        //   - Prevents illegal bit indexing
        //   - MSB provides slowest possible division
        //
        //   Output Registration:
        //   - All divided_clk outputs are registered for glitch-free operation
        //   - Adds 1 cycle latency but prevents combinational glitches
        //   - Reset clears all outputs to 0 (low phase)
        //
        //   Division Ratio Table (for reference):
        //   pickoff_point | Counter Bit | Division Ratio | Output Freq (100MHz clk)
        //   --------------|-------------|----------------|-------------------------
        //   0             | [0]         | 2              | 50MHz
        //   1             | [1]         | 4              | 25MHz
        //   2             | [2]         | 8              | 12.5MHz
        //   3             | [3]         | 16             | 6.25MHz
        //   4             | [4]         | 32             | 3.125MHz
        //   5             | [5]         | 64             | 1.5625MHz
        //   10            | [10]        | 2048           | 48.8kHz
        //   15            | [15]        | 65536          | 1.5kHz
        //   19            | [19]        | 1048576        | 95Hz
        //   23            | [23]        | 16777216       | 6Hz
        //
        //   Timing Diagram (COUNTER_WIDTH=8, pickoff_points={3,1}):
        //
        //   {signal: [
        //     {name: 'clk (input)',        wave: 'p................'},
        //     {name: 'rst_n',              wave: '01...............'},
        //     {},
        //     {name: 'r_divider_counters', wave: 'x.2.3.4.5.6.7.8.9', data: ['00','01','02','03','04','05','06','07']},
        //     {},
        //     {name: 'counter[0] (÷2)',    wave: 'x.0.1.0.1.0.1.0.1'},
        //     {name: 'counter[1] (÷4)',    wave: 'x.0...1...0...1..'},
        //     {name: 'counter[3] (÷16)',   wave: 'x.0...............1'},
        //     {},
        //     {name: 'divided_clk[0] (po=1)', wave: 'x..0...1...0...1.', node: '...................a'},
        //     {name: 'divided_clk[1] (po=3)', wave: 'x..0...............', node: '...................b'},
        //     {},
        //     {name: 'Division',           wave: 'x..2...4..........', data: ['clk÷4','clk÷16']}
        //   ],
        //   edge: ['a clk÷4 output', 'b clk÷16 (slow)']}
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // Generate 4 divided clocks: clk/4, clk/16, clk/256, clk/65536
        //   logic [31:0] pickoff_cfg;
        //   assign pickoff_cfg = {8'd15, 8'd7, 8'd3, 8'd1};  // {po3, po2, po1, po0}
        //
        //   clock_divider #(
        //       .N(4),              // 4 outputs
        //       .PO_WIDTH(8),       // 8-bit pickoff point
        //       .COUNTER_WIDTH(16)  // 16-bit counter (max div = 65536)
        //   ) u_clk_div (
        //       .clk           (clk_100mhz),
        //       .rst_n         (rst_n),
        //       .pickoff_points(pickoff_cfg),
        //       .divided_clk   ({clk_1p5khz, clk_390khz, clk_6p25mhz, clk_25mhz})
        //   );
        //
        //   // Baud rate generator for UART (115200 baud from 100MHz)
        //   // Target: 115200 Hz → division = 100MHz / 115200 ≈ 868
        //   // Use counter_load_clear instead (not power-of-2)
        //   // But for 9600 baud: 100MHz / 9600 ≈ 10417 ≈ 2^13.3 → use pickoff=13
        //   logic [7:0] baud_pickoff = 8'd13;  // Approx 12207 Hz (close enough for 9600)
        //
        //   clock_divider #(
        //       .N(1),
        //       .PO_WIDTH(8),
        //       .COUNTER_WIDTH(16)
        //   ) u_baud_clk (
        //       .clk           (sys_clk),
        //       .rst_n         (rst_n),
        //       .pickoff_points(baud_pickoff),
        //       .divided_clk   (uart_baud_x16)  // 16× oversampling clock
        //   );
        //
        //   // Test clock generation (multiple outputs for debug)
        //   clock_divider #(
        //       .N(8),              // 8 debug clocks
        //       .PO_WIDTH(8),
        //       .COUNTER_WIDTH(32)  // Support ultra-slow clocks
        //   ) u_test_clks (
        //       .clk           (ref_clk),
        //       .rst_n         (test_rst_n),
        //       .pickoff_points({8'd20, 8'd18, 8'd16, 8'd14, 8'd12, 8'd10, 8'd8, 8'd6}),
        //       .divided_clk   (test_clk_bus)
        //   );
        //
        //   // Runtime-programmable clock divider (APB-configurable)
        //   logic [7:0] cfg_pickoff_0, cfg_pickoff_1;
        //   always_ff @(posedge pclk) begin
        //       if (pwrite && paddr == ADDR_PICKOFF_0) cfg_pickoff_0 <= pwdata[7:0];
        //       if (pwrite && paddr == ADDR_PICKOFF_1) cfg_pickoff_1 <= pwdata[7:0];
        //   end
        //
        //   clock_divider #(
        //       .N(2),
        //       .PO_WIDTH(8),
        //       .COUNTER_WIDTH(24)
        //   ) u_cfg_clk_div (
        //       .clk           (core_clk),
        //       .rst_n         (core_rst_n),
        //       .pickoff_points({cfg_pickoff_1, cfg_pickoff_0}),
        //       .divided_clk   ({clk_out_1, clk_out_0})
        //   );
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **WARNING: NOT for functional clocks!** Use PLL/MMCM/clock manager instead
        //   - Divided clocks have phase offset relative to input clock
        //   - All divided clocks share same counter (phase-locked to each other)
        //   - Output duty cycle is always 50% (from counter bit toggle)
        //   - **Only power-of-2 divisions** - For arbitrary ratios, use different module
        //   - Counter resets to 0, causing all outputs to start low
        //   - **Timing hazard:** Using divided_clk as functional clock creates derived clock
        //   - Derived clocks complicate timing analysis and STA constraints
        //   - **Best practice:** Use for testbenches, debug, or non-critical timing
        //   - For production: Use dedicated clock synthesis primitives (PLL/MMCM)
        //   - pickoff_points can change runtime, but may cause glitches during transition
        //   - To avoid glitches when changing pickoff: assert rst_n, change config, deassert rst_n
        //   - **Resource usage:** COUNTER_WIDTH flip-flops + N output registers + N muxes
        //   - Synthesis: Counter is typically a simple binary up-counter (efficient)
        //   - **Critical path:** Counter increment → mux → output register
        //   - For low-jitter clocks, use PLL (this module has input jitter + quantization)
        //   - Counter wraps silently (no overflow flag)
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - counter_bin.sv - Simple binary counter (used internally here)
        //   - counter_freq_invariant.sv - Time-based counter with 1MHz tick
        //   - clock_pulse.sv - Configurable pulse generator
        //   - clock_gate_ctrl.sv - Clock gating for power management
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_clock_divider.py
        //   Run: pytest val/common/test_clock_divider.py -v
        //   Coverage: 91%
        //   Key Test Scenarios:
        //     - Single output (N=1) with various pickoff points
        //     - Multiple outputs (N=4) with different divisions
        //     - Out-of-range pickoff clamping
        //     - Runtime pickoff point changes
        //     - Reset behavior (all outputs low)
        //     - Division ratio verification (frequency measurement)
        //     - Edge case: pickoff=0 (divide by 2)
        //     - Edge case: pickoff=COUNTER_WIDTH-1 (slowest division)
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        module clock_divider #(
            parameter int N             = 4,  // Number of output clocks
            parameter int PO_WIDTH      = 8,  // Width of the Pick off registers
            parameter int COUNTER_WIDTH = 64  // Width of the counter
        ) (
 006075     input  logic                    clk,             // Input clock signal
 000207     input  logic                    rst_n,           // Active low reset signal
%000000     input  logic [(N*PO_WIDTH-1):0] pickoff_points,  // the pick off point config registers
 000144     output logic [           N-1:0] divided_clk      // Divided clock signals
        );
        
%000000     logic [COUNTER_WIDTH-1:0] r_divider_counters;  // Counter for all input clocks
        
            // Calculate the width needed to address all counter bits
            localparam int ADDR_WIDTH = $clog2(COUNTER_WIDTH);
        
            // Parameter validation: Verify PO_WIDTH can hold COUNTER_WIDTH value without truncation
            // PO_WIDTH must be > $clog2(COUNTER_WIDTH) to prevent truncation when comparing
            // w_pickoff_raw < w_counter_width_sized (lines 289-291)
 000023     initial begin
 000023         if (PO_WIDTH <= $clog2(COUNTER_WIDTH)) begin
                    $error("clock_divider: Invalid parameter combination!");
                    $error("  PO_WIDTH=%0d is too small for COUNTER_WIDTH=%0d", PO_WIDTH, COUNTER_WIDTH);
                    $error("  Required: PO_WIDTH > $clog2(COUNTER_WIDTH)");
                    $error("  Required: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1) = %0d", $clog2(COUNTER_WIDTH + 1));
                    $error("  This prevents truncation in pickoff point comparison.");
                    $fatal(1, "Simulation cannot continue with invalid parameters");
                end
            end
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (!rst_n) r_divider_counters <= 0;
                else r_divider_counters <= r_divider_counters + 1;
 000184     )
        
        
            genvar i;
            generate
 000088         for (i = 0; i < N; i++) begin : gen_clk_divider
 000088             int EndIdx = (i + 1) * PO_WIDTH - 1;
        
                    // Extract pickoff point and limit it to valid counter address range
                    logic [PO_WIDTH-1:0] w_pickoff_raw;
                    logic [ADDR_WIDTH-1:0] w_pickoff_addr;
                    logic [PO_WIDTH-1:0] w_counter_width_sized;
        
                    assign w_pickoff_raw = pickoff_points[EndIdx-:PO_WIDTH];
                    assign w_counter_width_sized = PO_WIDTH'(COUNTER_WIDTH);
                    assign w_pickoff_addr = (w_pickoff_raw < w_counter_width_sized) ?
                                            w_pickoff_raw[ADDR_WIDTH-1:0] :
                                            ADDR_WIDTH'(COUNTER_WIDTH - 1);
        
                    `ALWAYS_FF_RST(clk, rst_n,
                        if (!rst_n) divided_clk[i] <= 0;
                        else divided_clk[i] <= r_divider_counters[w_pickoff_addr];
 000704             )
        
                end
            endgenerate
        
        endmodule : clock_divider
        
