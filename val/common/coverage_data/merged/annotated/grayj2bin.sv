//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: grayj2bin
        // Purpose: //   Converts Johnson counter Gray code to binary representation. Johnson counters
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: grayj2bin
        //==============================================================================
        // Description:
        //   Converts Johnson counter Gray code to binary representation. Johnson counters
        //   produce a special form of Gray code where only one bit changes between states,
        //   making them ideal for asynchronous clock domain crossing. This module decodes
        //   the Johnson code back to standard binary for address generation.
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   JCW:
        //     Description: Johnson Counter Width (number of bits in Johnson code)
        //     Type: int
        //     Range: 2 to 128
        //     Default: 10
        //     Constraints: Typically equal to DEPTH for even-numbered FIFO depths
        //
        //   WIDTH:
        //     Description: Binary output width in bits
        //     Type: int
        //     Range: 1 to 32
        //     Default: 4
        //     Constraints: Must be $clog2(JCW) + 1 to represent full count range
        //
        //   INSTANCE_NAME:
        //     Description: Instance name for debug/waveform identification
        //     Type: string
        //     Default: ""
        //     Constraints: String identifier (debugging only)
        //
        //   Derived Parameters (localparam - computed automatically):
        //     N: Bit width for leading/trailing one position ($clog2(JCW))
        //     PAD_WIDTH: Zero-padding width for output alignment
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - Johnson counter creates 2*JCW unique states with JCW flip-flops
        //   - Single bit transition property ensures CDC safety
        //   - Decoding uses leading_one_trailing_one module for position detection
        //   - MSB of binary output indicates wrap-around (second half of sequence)
        //   - Used in fifo_async_div2 for pointer conversion
        //
        //------------------------------------------------------------------------------
        // FPGA-Specific Synthesis and Implementation Notes:
        //------------------------------------------------------------------------------
        //   **Synthesis on FPGAs:**
        //   - Johnson code to binary conversion is MORE complex than standard Gray code
        //   - Requires leading_one_trailing_one detection logic (priority encoders)
        //   - Resource usage significantly higher than gray2bin
        //   - Typical resource breakdown:
        //     * JCW=8:  ~20-30 LUTs (2x more than gray2bin)
        //     * JCW=16: ~50-70 LUTs (2x more than gray2bin)
        //     * JCW=32: ~120-160 LUTs (2x more than gray2bin)
        //   - No special primitives needed - pure combinational LUT logic
        //
        //   **When to Use Johnson Code vs Standard Gray Code:**
        //
        //   Use Johnson Counter (this module):
        //   ✅ When FIFO depth is NOT a power of 2
        //   ✅ When you need exactly 2*JCW states (odd depths)
        //   ✅ fifo_async_div2.sv uses this for flexible depths
        //   ✅ Lower resource count in FIFO (no extra address bit)
        //
        //   Use Standard Gray Code (gray2bin.sv):
        //   ✅ When FIFO depth IS a power of 2
        //   ✅ Simpler conversion logic (faster, smaller)
        //   ✅ fifo_async.sv uses this for power-of-2 depths
        //   ✅ Better understood / more common pattern
        //
        //   **Comparison Table:**
        //
        //   Feature                  | Johnson Code      | Standard Gray Code
        //   -------------------------|-------------------|-------------------
        //   States per FF            | 2 states/FF       | 2^N states for N FFs
        //   Conversion complexity    | Higher (encoders) | Lower (XOR tree)
        //   Resource usage (decoder) | ~2x gray2bin      | Baseline
        //   Timing (decoder)         | Slower            | Faster
        //   Typical FPGA usage       | Non-power-of-2    | Power-of-2 FIFOs
        //   Example module           | fifo_async_div2   | fifo_async
        //
        //   **Critical Timing Considerations:**
        //   - This module is combinational - output depends on leading_one_trailing_one
        //   - leading_one_trailing_one uses priority encoders → log2(JCW) LUT levels
        //   - Critical path: Johnson code input → priority encode → binary output
        //   - For JCW=16: Expect 4-5 LUT levels propagation delay
        //   - For JCW=32: Expect 5-6 LUT levels propagation delay
        //   - **FPGA Best Practice:** Register the binary output immediately!
        //
        //   Example (CORRECT for FPGA timing closure):
        //   ```systemverilog
        //   // BAD: Long combinational path from synchronizer to binary users
        //   grayj2bin #(.JCW(16)) u_decode (
        //       .gray(johnson_sync),    // From CDC synchronizer
        //       .binary(read_addr)      // Used for memory addressing - long path!
        //   );
        //
        //   // GOOD: Register binary output before use (breaks long path)
        //   logic [ADDR_WIDTH-1:0] read_addr_comb, read_addr_reg;
        //   grayj2bin #(.JCW(16)) u_decode (
        //       .gray(johnson_sync),
        //       .binary(read_addr_comb)
        //   );
        //   always_ff @(posedge clk) read_addr_reg <= read_addr_comb;  // Register!
        //   assign mem_addr = read_addr_reg;  // Clean timing to memory
        //   ```
        //
        //   **Why Register the Output:**
        //   - Priority encoders have long propagation delays (especially for wide JCW)
        //   - Memory address decoders are timing-critical
        //   - Combinational path: sync → priority encode → address decode = too long!
        //   - Registering adds 1 cycle latency but ensures timing closure
        //   - Most async FIFOs can tolerate this latency in pointer paths
        //
        //   **Timing Constraints (XDC/SDC):**
        //   ```tcl
        //   # After CDC synchronizer, set max delay on Johnson code path
        //   set_max_delay -datapath_only \
        //     -from [get_cells sync_johnson_reg[*]] \
        //     -to   [get_cells binary_addr_reg[*]] \
        //     [expr {$clk_period}]
        //
        //   # Optional: Multicycle if binary output is registered
        //   set_multicycle_path 2 -setup \
        //     -from [get_cells sync_johnson_reg[*]] \
        //     -to   [get_cells binary_addr_reg[*]]
        //   set_multicycle_path 1 -hold \
        //     -from [get_cells sync_johnson_reg[*]] \
        //     -to   [get_cells binary_addr_reg[*]]
        //   ```
        //
        //   **Resource Usage (Typical FPGA):**
        //   - JCW=4:  ~15-20 LUTs (small overhead)
        //   - JCW=8:  ~25-35 LUTs
        //   - JCW=16: ~55-75 LUTs
        //   - JCW=32: ~130-170 LUTs
        //   - No registers consumed (combinational only, unless registered output)
        //   - Negligible power impact
        //
        //   **Performance by FPGA Family:**
        //   - Xilinx 7-series (Artix-7, Kintex-7, Virtex-7):
        //     * JCW=16: ~2.5-3.5 ns propagation delay
        //     * Supports up to ~300 MHz with registered output
        //   - Xilinx UltraScale/UltraScale+:
        //     * JCW=16: ~1.8-2.5 ns propagation delay
        //     * Supports up to ~400 MHz with registered output
        //   - Intel Cyclone V:
        //     * JCW=16: ~3.0-4.0 ns propagation delay
        //     * Supports up to ~250 MHz with registered output
        //   - Intel Arria 10 / Stratix 10:
        //     * JCW=16: ~2.0-3.0 ns propagation delay
        //     * Supports up to ~350 MHz with registered output
        //
        //   **Synthesis Attributes (Optional):**
        //   - Generally not needed - logic is straightforward
        //   - If synthesis tool warns about optimization:
        //   ```systemverilog
        //   (* keep_hierarchy = "yes" *) module grayj2bin ...  // Xilinx: preserve hierarchy
        //   (* preserve *) wire [WIDTH-1:0] binary;             // Intel: preserve logic
        //   ```
        //
        //   **FIFO Pointer Synchronization (Primary Use Case):**
        //   - fifo_async_div2.sv uses Johnson counters for non-power-of-2 depths
        //   - Typical flow in async FIFO:
        //     1. Johnson counter increments in write clock domain (counter_johnson)
        //     2. Johnson code registered in source domain
        //     3. Johnson code synchronized to destination domain (2-FF sync)
        //     4. grayj2bin converts to binary (this module)
        //     5. Binary address used for memory operations
        //   - **Critical:** Johnson code must be stable before synchronization!
        //   - Always register Johnson counter output before sending across domains
        //
        //   **Comparison to Standard Gray Code FIFO:**
        //
        //   fifo_async (power-of-2 depths):
        //   - Uses counter_bingray → bin2gray → sync → gray2bin
        //   - Faster conversion (gray2bin is simpler)
        //   - Standard pattern, well understood
        //   - Requires power-of-2 depth
        //
        //   fifo_async_div2 (any depth):
        //   - Uses counter_johnson → sync → grayj2bin (this module)
        //   - Slower conversion (priority encoders)
        //   - Supports non-power-of-2 depths (e.g., depth=10, 12, 14)
        //   - More flexible but slightly higher resource usage
        //
        //   **When to Use Each FIFO Variant:**
        //   - Use fifo_async if depth can be power-of-2 (8, 16, 32, 64, etc.)
        //   - Use fifo_async_div2 if depth must be odd or non-power-of-2 (10, 12, 20, etc.)
        //   - For FPGA: fifo_async is slightly faster and smaller
        //   - For flexibility: fifo_async_div2 supports any depth
        //
        //   **Verification on FPGA:**
        //   - Use ILA (Xilinx) or SignalTap (Intel) to capture:
        //     * Johnson code input (from synchronizer)
        //     * Binary output
        //     * Verify conversion correctness
        //   - Check for glitches on binary output signals (should be clean if registered)
        //   - Verify timing closure in implementation reports
        //   - Monitor leading_one_trailing_one outputs for debug
        //
        //   **Common FPGA Mistakes:**
        //   1. ❌ Not registering binary output before use
        //      → Timing violations on memory address paths
        //   2. ❌ Using Johnson code for power-of-2 depths
        //      → Unnecessary complexity, use standard Gray code instead
        //   3. ❌ Forgetting that conversion is slower than gray2bin
        //      → Timing violations, especially for wide JCW
        //   4. ❌ Not synchronizing Johnson code before conversion
        //      → Metastability in priority encoders → corrupted addresses
        //   5. ❌ Assuming Johnson code is "free" timing-wise
        //      → Priority encoder delays add up, especially for wide buses
        //
        //   **When to Use Vendor IP Instead:**
        //   - For async FIFOs: Consider Xilinx FIFO Generator or Intel DCFIFO
        //   - Vendor IP includes:
        //     * Built-in pointer management (standard Gray or Johnson)
        //     * Optimized for specific FPGA architecture
        //     * Status flag generation
        //     * Better timing closure for deep FIFOs
        //   - Use custom grayj2bin when:
        //     * Building educational/portable design
        //     * Need fine control over CDC methodology
        //     * Vendor IP doesn't fit requirements (e.g., custom depth)
        //
        //   **Resource Usage Comparison (JCW=16):**
        //   - grayj2bin:        ~60 LUTs (priority encoders + mux logic)
        //   - gray2bin (WIDTH=4): ~8 LUTs (simple XOR tree)
        //   - Ratio: grayj2bin is ~7.5x larger than gray2bin for same address width
        //   - Trade-off: Flexibility (any depth) vs Resources (larger decoder)
        //
        //   **Performance:**
        //   - Propagation delay: ~2-4 ns on modern FPGAs (JCW=16, one LUT level per encode stage)
        //   - Not on critical path if output is registered
        //   - Scales logarithmically with JCW (priority encoder depth)
        //   - For JCW > 32: Consider pipelining the priority encoder for high-speed designs
        //
        //   **Advanced: Pipelining for High-Speed Designs (JCW > 32):**
        //   ```systemverilog
        //   // For very wide Johnson codes, pipeline the conversion
        //   logic [WIDTH-1:0] binary_stage1, binary_stage2;
        //
        //   // Stage 1: Priority encode
        //   always_ff @(posedge clk) begin
        //       if (!rst_n) begin
        //           binary_stage1 <= '0;
        //       end else begin
        //           // Insert priority encoder output here
        //           binary_stage1 <= {compute priority encode};
        //       end
        //   end
        //
        //   // Stage 2: Final binary output
        //   always_ff @(posedge clk) begin
        //       if (!rst_n) begin
        //           binary_stage2 <= '0;
        //       end else begin
        //           binary_stage2 <= binary_stage1;
        //       end
        //   end
        //   ```
        //   - Adds 2-cycle latency but enables >500 MHz operation
        //   - Only needed for JCW > 32 or very high-speed designs (>400 MHz)
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - counter_johnson.sv - Generates Johnson counter sequences
        //   - leading_one_trailing_one.sv - Position detection helper
        //   - fifo_async_div2.sv - Primary user of this converter
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_grayj2bin.py
        //   Run: pytest val/common/test_grayj2bin.py -v
        //
        //==============================================================================
        module grayj2bin #(
            parameter int    JCW = 10,
            parameter int    WIDTH = 4,
            parameter string INSTANCE_NAME = ""
        ) (
 005324     input  logic              clk,
 000036     input  logic              rst_n,
 000056     input  logic  [JCW-1:0]   gray,
 000056     output logic  [WIDTH-1:0] binary
        );
        
            localparam int N = $clog2(JCW);
            localparam int PAD_WIDTH = (WIDTH > N+1) ? WIDTH-N-1 : 0;
        
 000056     logic [N-1:0]     w_leading_one;
%000004     logic [N-1:0]     w_trailing_one;
%000000     logic [WIDTH-1:0] w_binary;
 000032     logic             w_all_zeroes;
 000026     logic             w_all_ones;
 000028     logic             w_valid;
        
            // Leading/trailing detection
            leading_one_trailing_one #(
                .WIDTH(JCW),
                .INSTANCE_NAME(INSTANCE_NAME)
            ) u_leading_one_trailing_one (
                .data              (gray),
                .leadingone        (w_leading_one),
                .leadingone_vector (),
                .trailingone       (w_trailing_one),
                .trailingone_vector(),
                .all_zeroes        (w_all_zeroes),
                .all_ones          (w_all_ones),
                .valid             (w_valid)
            );
        
            // Restore original working logic
 021524     always_comb begin
 000636         if (w_all_zeroes || w_all_ones) begin
 000636             w_binary = {WIDTH{1'b0}};
 008431         end else if (gray[JCW-1]) begin
                    // Second half: use leading one position directly
 008431             w_binary = {{(WIDTH-N){1'b0}}, w_trailing_one};
 010185         end else begin
                    // First half: use trailing one + 1
 010185             w_binary = {{(WIDTH-N){1'b0}}, (w_leading_one + 1'b1)};
                end
            end
        
            assign binary[WIDTH-1]   = gray[JCW-1];                 // MSB = wrap
            assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower binary
        
        endmodule : grayj2bin
        
