//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: fifo_async_div2
        // Purpose: //   Asynchronous FIFO with independent read and write clock domains. Uses
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: fifo_async_div2
        //==============================================================================
        // Description:
        //   Asynchronous FIFO with independent read and write clock domains. Uses
        //   Johnson counter (Gray code variant) for CDC-safe pointer synchronization.
        //   Optimized for depths that are even numbers. Provides almost-full and
        //   almost-empty flags for flow control.
        //
        // Features:
        //   - Independent read/write clock domains (full CDC support)
        //   - Johnson counter Gray code for pointer synchronization
        //   - Configurable almost-full/almost-empty thresholds
        //   - Optional registered output (mux or flop mode)
        //   - Parameterized data width and depth
        //   - Dual-port RAM implementation
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   REGISTERED:
        //     Description: Output register mode
        //     Type: int
        //     Range: 0 or 1
        //     Default: 0
        //     Constraints: 0 = Mux mode (combinational read), 1 = Flop mode (registered read)
        //
        //   DATA_WIDTH:
        //     Description: FIFO data path width in bits
        //     Type: int
        //     Range: 1 to 512
        //     Default: 8
        //     Constraints: Any positive integer
        //
        //   DEPTH:
        //     Description: FIFO depth (number of entries)
        //     Type: int
        //     Range: 2 to 65536 (must be even for div2 optimization)
        //     Default: 10
        //     Constraints: Must be even number for Johnson counter operation
        //
        //   N_FLOP_CROSS:
        //     Description: Number of synchronizer flops for CDC
        //     Type: int
        //     Range: 2 to 5
        //     Default: 2
        //     Constraints: 2 = minimum for metastability, 3+ for higher MTBF
        //
        //   ALMOST_WR_MARGIN:
        //     Description: Almost-full threshold (entries from full)
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: wr_almost_full asserts when (used >= DEPTH - ALMOST_WR_MARGIN)
        //
        //   ALMOST_RD_MARGIN:
        //     Description: Almost-empty threshold (entries from empty)
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: rd_almost_empty asserts when (used <= ALMOST_RD_MARGIN)
        //
        //   INSTANCE_NAME:
        //     Description: Instance name for debug/waveform identification
        //     Type: string
        //     Default: "DEADF1F0"
        //     Constraints: String identifier (debugging only)
        //
        //   Derived Parameters (localparam - computed automatically):
        //     DW: Alias for DATA_WIDTH
        //     D: Alias for DEPTH
        //     AW: Address width ($clog2(DEPTH))
        //     JCW: Johnson Counter Width (same as DEPTH)
        //     N: Alias for N_FLOP_CROSS
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Write Clock Domain:
        //     wr_clk:           Write clock
        //     wr_rst_n:         Write domain active-low reset
        //     write:            Write enable
        //     wr_data:          Write data input [DATA_WIDTH-1:0]
        //     wr_full:          FIFO full flag (do not write when asserted)
        //     wr_almost_full:   Almost-full warning flag
        //
        //   Read Clock Domain:
        //     rd_clk:           Read clock
        //     rd_rst_n:         Read domain active-low reset
        //     read:             Read enable
        //     rd_data:          Read data output [DATA_WIDTH-1:0]
        //     rd_empty:         FIFO empty flag (do not read when asserted)
        //     rd_almost_empty:  Almost-empty warning flag
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - DEPTH must be even for Johnson counter optimization
        //   - Johnson counters provide Gray code properties for CDC safety
        //   - N_FLOP_CROSS=2 is minimum; use 3+ for high-speed clock domain crossings
        //   - ALMOST_* margins enable proactive flow control
        //   - REGISTERED=1 adds one cycle read latency but improves timing
        //   - Write when (!wr_full && write), read when (!rd_empty && read)
        //   - Independent resets for write and read domains
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - fifo_async.sv - General async FIFO (any depth)
        //   - fifo_sync.sv - Synchronous FIFO (single clock domain)
        //   - counter_johnson.sv - Johnson counter (used internally)
        //   - grayj2bin.sv - Johnson-to-binary converter (used internally)
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_fifo_async_div2.py
        //   Run: pytest val/common/test_fifo_async_div2.py -v
        //
        //------------------------------------------------------------------------------
        // FPGA-Specific Synthesis and Implementation Notes:
        //------------------------------------------------------------------------------
        //   **Overview:**
        //   - This module is an alternative to fifo_async.sv for NON-power-of-2 depths
        //   - Uses Johnson counter Gray code instead of standard binary Gray code
        //   - Allows ANY even depth (e.g., DEPTH=6, 10, 12, 14, 18, 20, etc.)
        //   - Slightly higher resource usage than fifo_async but more flexible
        //
        //   **When to Use fifo_async_div2 vs fifo_async:**
        //
        //   Use fifo_async_div2 (this module) when:
        //   ✅ DEPTH is NOT a power of 2 (e.g., DEPTH=10, 12, 14, 18, 20)
        //   ✅ Need exact depth matching for system requirements
        //   ✅ Willing to accept ~20-30% higher resource usage for flexibility
        //
        //   Use fifo_async.sv when:
        //   ✅ DEPTH can be power of 2 (e.g., 8, 16, 32, 64, 128)
        //   ✅ Resource optimization is critical (smaller, faster)
        //   ✅ Standard async FIFO pattern (most common)
        //
        //   **Resource Comparison (DEPTH=16, DATA_WIDTH=8):**
        //
        //   Feature              | fifo_async (power-of-2) | fifo_async_div2 (any even)
        //   ---------------------|-------------------------|---------------------------
        //   Pointer counter      | counter_bingray (simple)| counter_johnson (larger)
        //   Pointer width        | $clog2(DEPTH) = 4 bits  | DEPTH = 16 bits (4x wider!)
        //   Gray converter       | gray2bin (XOR tree)     | grayj2bin (priority encoder)
        //   LUT usage (pointers) | ~15 LUTs                | ~60 LUTs (4x more)
        //   FF usage (pointers)  | ~30 FFs                 | ~100 FFs (3x more)
        //   Memory (r_mem)       | Same (DEPTH × DATA_WIDTH) | Same
        //   Timing (conversion)  | Faster (1 XOR level)    | Slower (log2 priority encode)
        //   Fmax (typical)       | ~500 MHz                | ~400 MHz
        //
        //   **Key Difference: Johnson Counter Width:**
        //   - fifo_async: Pointer width = $clog2(DEPTH) bits
        //     * DEPTH=16 → 4-bit pointers
        //   - fifo_async_div2: Pointer width = DEPTH bits (Johnson code)
        //     * DEPTH=16 → 16-bit pointers (4x wider!)
        //   - This width difference drives the resource overhead
        //
        //   **Memory Inference on FPGAs:**
        //   - Same as fifo_async.sv (DEPTH × DATA_WIDTH determines BRAM vs distributed RAM)
        //   - See fifo_async.sv FPGA documentation for detailed memory inference rules
        //
        //   **Xilinx FPGAs:**
        //   - DEPTH × DATA_WIDTH ≤ 64 bits → Distributed RAM (LUTs)
        //   - DEPTH × DATA_WIDTH > 64 bits → Block RAM (BRAM)
        //   - Example: DEPTH=10, DATA_WIDTH=8 → 80 bits → BRAM (18Kb block)
        //
        //   **Intel FPGAs:**
        //   - DEPTH × DATA_WIDTH ≤ 640 bits → MLAB (Memory LAB)
        //   - DEPTH × DATA_WIDTH > 640 bits → M20K (20Kb block)
        //   - Example: DEPTH=20, DATA_WIDTH=16 → 320 bits → MLAB
        //
        //   **MEM_STYLE Parameter:**
        //   - Same as fifo_async.sv
        //   - Values: FIFO_AUTO, FIFO_DISTRIBUTED, FIFO_BLOCK, FIFO_MLAB, FIFO_M20K
        //   - Use FIFO_AUTO for portable code (let synthesis tool decide)
        //
        //   **Critical Timing Considerations:**
        //   - Johnson code synchronization is SLOWER than standard Gray code
        //   - grayj2bin uses priority encoders (logarithmic depth)
        //   - For DEPTH=16: grayj2bin has ~4-5 LUT levels vs 1 LUT level for gray2bin
        //   - Expect ~20-25% lower Fmax compared to fifo_async.sv
        //
        //   **Timing Constraints (XDC for Xilinx):**
        //   ```tcl
        //   # Write pointer Johnson code crossing to read domain
        //   set_max_delay -datapath_only \
        //     -from [get_cells u_fifo/r_wr_ptr_gray_reg[*]] \
        //     -to   [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[0][*]] \
        //     [expr {2 * $rd_clk_period}]
        //
        //   # Read pointer Johnson code crossing to write domain
        //   set_max_delay -datapath_only \
        //     -from [get_cells u_fifo/r_rd_ptr_gray_reg[*]] \
        //     -to   [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[0][*]] \
        //     [expr {2 * $wr_clk_period}]
        //
        //   # Mark synchronizer chains as CDC paths
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[*][*]]
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[*][*]]
        //
        //   # Prevent SRL extraction for synchronizer FFs
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[*][*]]
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[*][*]]
        //   ```
        //
        //   **Timing Constraints (SDC for Intel Quartus):**
        //   ```tcl
        //   # Write pointer Johnson code CDC constraint
        //   set_max_delay -from [get_registers {*r_wr_ptr_gray_reg[*]}] \
        //                 -to   [get_registers {*u_sync_wr_ptr|r_sync_reg[0][*]}] \
        //                 [expr {2 * $rd_clk_period}]
        //
        //   # Read pointer Johnson code CDC constraint
        //   set_max_delay -from [get_registers {*r_rd_ptr_gray_reg[*]}] \
        //                 -to   [get_registers {*u_sync_rd_ptr|r_sync_reg[0][*]}] \
        //                 [expr {2 * $wr_clk_period}]
        //
        //   # Mark synchronizers
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to [get_registers {*u_sync_wr_ptr|r_sync_reg[*][*]}]
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to [get_registers {*u_sync_rd_ptr|r_sync_reg[*][*]}]
        //   ```
        //
        //   **Best Practices for FPGA Timing:**
        //   1. **Use N_FLOP_CROSS=3 for production** (even more critical than fifo_async)
        //   2. **Set REGISTERED=1 for high-speed designs** (helps with grayj2bin delay)
        //   3. **Be aware of pointer width penalty:**
        //      - DEPTH=10 → 10-bit Johnson pointers (vs 4-bit binary Gray)
        //      - Wider synchronizers = more FFs, more routing congestion
        //   4. **Pipeline grayj2bin output if timing-critical:**
        //      ```systemverilog
        //      // If grayj2bin path is too slow, add register stage
        //      logic [AW:0] rd_ptr_bin_reg;
        //      always_ff @(posedge rd_clk) rd_ptr_bin_reg <= w_rdom_wr_ptr_bin;
        //      assign rd_empty = (r_rd_ptr_bin == rd_ptr_bin_reg);  // +1 cycle latency
        //      ```
        //
        //   **Resource Usage (Typical FPGA):**
        //
        //   Configuration: DEPTH=10, DATA_WIDTH=8, N_FLOP_CROSS=3
        //   - Memory: 10×8 = 80 bits → 1 BRAM (18Kb) or ~20 LUTs (distributed)
        //   - Write pointer: 10 FFs (Johnson) + 4 FFs (binary) = 14 FFs
        //   - Read pointer: 14 FFs
        //   - Synchronizers: 2×(3 stages × 10 bits) = 60 FFs (vs 24 FFs for fifo_async)
        //   - grayj2bin converters: ~40 LUTs (vs ~8 LUTs for gray2bin)
        //   - Full/empty logic: ~20 LUTs
        //   - **Total: ~100 FFs, ~80 LUTs, 1 BRAM**
        //   - Compare to fifo_async (DEPTH=16): ~50 FFs, ~50 LUTs, 1 BRAM
        //
        //   Configuration: DEPTH=20, DATA_WIDTH=16, N_FLOP_CROSS=3
        //   - Memory: 20×16 = 320 bits → 1 BRAM or MLAB
        //   - Write pointer: 20 FFs (Johnson) + 5 FFs (binary) = 25 FFs
        //   - Read pointer: 25 FFs
        //   - Synchronizers: 2×(3 stages × 20 bits) = 120 FFs
        //   - grayj2bin converters: ~80 LUTs
        //   - **Total: ~200 FFs, ~120 LUTs, 1 BRAM/MLAB**
        //
        //   Configuration: DEPTH=6, DATA_WIDTH=8, N_FLOP_CROSS=2
        //   - Memory: 6×8 = 48 bits → Distributed RAM (~12 LUTs)
        //   - Write pointer: 6 FFs (Johnson) + 3 FFs (binary) = 9 FFs
        //   - Synchronizers: 2×(2 stages × 6 bits) = 24 FFs
        //   - grayj2bin: ~20 LUTs
        //   - **Total: ~60 FFs, ~60 LUTs, 0 BRAMs**
        //
        //   **Performance by FPGA Family:**
        //
        //   Xilinx 7-series (Artix-7, Kintex-7, Virtex-7):
        //   - BRAM-based: Fmax ~350 MHz (both clocks)
        //   - Distributed RAM: Fmax ~450 MHz
        //   - Bottleneck: grayj2bin priority encoder timing
        //   - REGISTERED=1 mode: Fmax ~400 MHz (BRAM), ~500 MHz (distributed)
        //
        //   Xilinx UltraScale/UltraScale+:
        //   - BRAM-based: Fmax ~450 MHz (both clocks)
        //   - Distributed RAM: Fmax ~550 MHz
        //   - REGISTERED=1 mode: Fmax ~500 MHz (BRAM), ~600 MHz (distributed)
        //
        //   Intel Cyclone V:
        //   - M20K/MLAB-based: Fmax ~250 MHz (both clocks)
        //   - Bottleneck: grayj2bin and synchronizer timing
        //
        //   Intel Arria 10 / Stratix 10:
        //   - M20K/MLAB-based: Fmax ~350 MHz (both clocks)
        //   - HyperFlex mode: Can push >450 MHz with retiming
        //
        //   **Comparison to fifo_async (same configuration):**
        //   - fifo_async_div2 is typically 20-25% slower Fmax
        //   - fifo_async_div2 uses 2-3x more logic resources
        //   - BUT: fifo_async_div2 supports non-power-of-2 depths!
        //
        //   **MTBF Calculations:**
        //   - Same as fifo_async.sv (Johnson code has single-bit-change property)
        //   - N_FLOP_CROSS=2: MTBF ~10^6 hours
        //   - N_FLOP_CROSS=3: MTBF ~10^12 hours (recommended for production)
        //   - Johnson code is as safe as standard Gray code for CDC
        //
        //   **When to Use Vendor FIFO IP Instead:**
        //
        //   Use Xilinx FIFO Generator or Intel DCFIFO when:
        //   ✅ DEPTH > 512 (vendor IP better optimized for large FIFOs)
        //   ✅ Need built-in ECC (error correction)
        //   ✅ Need data count outputs
        //   ✅ Need FWFT (first-word fall-through) mode
        //   ✅ Maximum performance required
        //
        //   Use this custom fifo_async_div2 when:
        //   ✅ Need portable code (Xilinx, Intel, Lattice, etc.)
        //   ✅ Need non-power-of-2 depth (e.g., DEPTH=10, 12, 14)
        //   ✅ DEPTH ≤ 128 (custom FIFO is simpler)
        //   ✅ Educational or research project
        //   ✅ Want to avoid vendor lock-in
        //
        //   **Comparison: Custom fifo_async_div2 vs Vendor IP:**
        //
        //   Feature                  | fifo_async_div2 | Xilinx FIFO Gen | Intel DCFIFO
        //   -------------------------|-----------------|-----------------|-------------
        //   Non-power-of-2 depths    | ✅ Yes (even)    | ✅ Yes           | ✅ Yes
        //   Resource overhead        | Higher (~2-3x)  | Optimized       | Optimized
        //   Fmax (typical)           | ~350 MHz        | ~450 MHz        | ~350 MHz
        //   Portability              | ✅ Portable      | ❌ Xilinx only   | ❌ Intel only
        //   ECC support              | ❌ No            | ✅ Optional      | ✅ Optional
        //   Data count output        | ❌ No            | ✅ Yes           | ✅ Yes
        //   FWFT mode                | ❌ No            | ✅ Yes           | ✅ Yes
        //   Customizability          | ✅ Full source   | ⚠️ Parameters   | ⚠️ Parameters
        //
        //   **Verification on FPGA:**
        //   - Use ILA (Xilinx) or SignalTap (Intel) to capture:
        //     * Johnson counter outputs (r_wr_ptr_gray, r_rd_ptr_gray)
        //     * Binary pointer outputs (r_wr_ptr_bin, r_rd_ptr_bin)
        //     * Synchronized pointers in opposite domains
        //     * Full/empty flags
        //   - Verify Johnson code single-bit-change property
        //   - Check for timing violations in implementation reports
        //   - Monitor grayj2bin conversion correctness
        //
        //   **Common FPGA Mistakes:**
        //   1. ❌ **Using odd DEPTH**
        //      → This module requires EVEN depth (e.g., 10, 12, 14, not 11, 13, 15)
        //      → Johnson counter div2 optimization requires even depths
        //
        //   2. ❌ **Using power-of-2 depth unnecessarily**
        //      → If DEPTH can be power-of-2, use fifo_async.sv instead!
        //      → fifo_async is faster, smaller, simpler for power-of-2 depths
        //
        //   3. ❌ **Not constraining Johnson code CDC paths**
        //      → Wider pointers = more critical for timing constraints
        //      → Always use set_max_delay for Johnson code synchronizers!
        //
        //   4. ❌ **Underestimating timing impact of grayj2bin**
        //      → grayj2bin is SLOWER than gray2bin (priority encoder vs XOR)
        //      → May need REGISTERED=1 or pipelined flag logic for high-speed designs
        //
        //   5. ❌ **Not accounting for increased synchronizer width**
        //      → DEPTH=20 → 20-bit synchronizers (vs 5-bit for power-of-2 equivalent)
        //      → More FFs, more routing, more congestion
        //
        //   6. ❌ **Wasting resources on small depths**
        //      → DEPTH=6 → 6-bit Johnson pointers (vs 3-bit binary Gray)
        //      → Consider if depth can be rounded to power-of-2 (8 instead of 6)
        //
        //   7. ❌ **Forgetting independent reset domains**
        //      → Same as fifo_async: wr_rst_n and rd_rst_n can assert independently
        //
        //   8. ❌ **Bypassing Johnson code for "optimization"**
        //      → Johnson code is NON-NEGOTIABLE for async FIFO CDC!
        //      → Direct binary sync will corrupt pointers
        //
        //   **Design Trade-offs:**
        //
        //   Flexibility vs Resources:
        //   - fifo_async_div2: ANY even depth, but ~2-3x more logic
        //   - fifo_async: Power-of-2 only, but smaller and faster
        //
        //   When to Accept the Overhead:
        //   - System requires exact FIFO depth (e.g., protocol specifies DEPTH=10)
        //   - Rounding to power-of-2 wastes too much memory
        //   - Resource overhead is acceptable (plenty of FPGA resources available)
        //
        //   When to Avoid:
        //   - DEPTH can be power-of-2 without system impact
        //   - Resource-constrained design (small FPGA)
        //   - Maximum performance required (>400 MHz)
        //
        //   **Advanced: Optimizing grayj2bin Critical Path:**
        //   - For very high-speed designs (>400 MHz), pipeline grayj2bin:
        //   ```systemverilog
        //   // Stage 1: Priority encode (registered)
        //   logic [AW:0] ptr_bin_stage1;
        //   always_ff @(posedge rd_clk) begin
        //       if (!rd_rst_n) ptr_bin_stage1 <= '0;
        //       else ptr_bin_stage1 <= grayj2bin_output;  // Register conversion output
        //   end
        //
        //   // Stage 2: Empty flag logic
        //   logic rd_empty_reg;
        //   always_ff @(posedge rd_clk) begin
        //       if (!rd_rst_n) rd_empty_reg <= 1'b1;
        //       else rd_empty_reg <= (r_rd_ptr_bin == ptr_bin_stage1);
        //   end
        //   ```
        //   - Adds 2 cycles latency but enables >500 MHz operation
        //
        //   **Synthesis Optimization Flags:**
        //
        //   Xilinx Vivado (same as fifo_async.sv):
        //   ```tcl
        //   # Force memory style
        //   set_property RAM_STYLE BLOCK [get_cells u_fifo/r_mem_reg]
        //
        //   # Prevent synchronizer optimization
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_*/r_sync_reg*]
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_*/r_sync_reg*]
        //   ```
        //
        //   Intel Quartus (same as fifo_async.sv):
        //   ```tcl
        //   # Force memory style
        //   set_instance_assignment -name RAMSTYLE M20K -to u_fifo|r_mem
        //
        //   # Mark synchronizers
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to u_fifo|u_sync_*|r_sync_reg*
        //   ```
        //
        //   **Performance:**
        //   - Typical Fmax: 350-450 MHz on modern FPGAs (20-25% slower than fifo_async)
        //   - Write throughput: 1 entry per wr_clk cycle (when not full)
        //   - Read throughput: 1 entry per rd_clk cycle (when not empty)
        //   - Latency: Write-to-read visibility = N_FLOP_CROSS rd_clk cycles
        //   - Pointer update latency: N_FLOP_CROSS cycles (cross-domain sync)
        //
        //==============================================================================
        
        `include "fifo_defs.svh"
        `include "reset_defs.svh"
        
        
        module fifo_async_div2 #(
            // One-knob memory style selector (enum comes from your fifo_defs.svh / package)
            parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
        
            parameter int    REGISTERED        = 0,   // 0 = mux mode (comb read), 1 = flop mode (registered read)
            parameter int    DATA_WIDTH        = 8,
            parameter int    DEPTH             = 10,
            parameter int    N_FLOP_CROSS      = 2,
            parameter int    ALMOST_WR_MARGIN  = 1,
            parameter int    ALMOST_RD_MARGIN  = 1,
            parameter string INSTANCE_NAME     = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
        ) (
            // clocks and resets
 008210     input  logic wr_clk,
 000036                 wr_rst_n,
 008544                 rd_clk,
 000036                 rd_rst_n,
        
            // wr_clk domain
 000696     input  logic                    write,
%000000     input  logic [DATA_WIDTH-1:0]   wr_data,
 000014     output logic                    wr_full,
 000024     output logic                    wr_almost_full,
        
            // rd_clk domain
 000650     input  logic                    read,
%000000     output logic [DATA_WIDTH-1:0]   rd_data,
 000584     output logic                    rd_empty,
 000078     output logic                    rd_almost_empty
        );
        
            // -----------------------------------------------------------------------
            // Derived params / locals
            // -----------------------------------------------------------------------
            localparam int DW  = DATA_WIDTH;
            localparam int D   = DEPTH;
            localparam int AW  = $clog2(DEPTH);
            localparam int JCW = D;                 // Johnson counter width (one-hot-ish)
            localparam int N   = N_FLOP_CROSS;
        
            // Write/read addresses (lower bits of binary pointers)
 000112     logic [AW-1:0] r_wr_addr, r_rd_addr;
        
            // Johnson/Gray domain pointers
 000056     logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray;
 000056     logic [JCW-1:0] r_rd_ptr_gray, r_rdom_wr_ptr_gray;
        
            // Binary pointers (+1 MSB for wrap info)
 000056     logic [AW:0] r_wr_ptr_bin, r_rd_ptr_bin;
 000056     logic [AW:0] w_wdom_rd_ptr_bin, w_rdom_wr_ptr_bin;
 000068     logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
        
            // Common read data, driven inside memory generate branch
%000000     logic [DW-1:0] w_rd_data;
        
            // -----------------------------------------------------------------------
            // Binary pointer counters (wr/rd domains)
            // -----------------------------------------------------------------------
            counter_bin #(
                .MAX   (D),
                .WIDTH (AW + 1)
            ) wr_ptr_counter_bin (
                .clk              (wr_clk),
                .rst_n            (wr_rst_n),
                .enable           (write && !wr_full),
                .counter_bin_next (w_wr_ptr_bin_next),
                .counter_bin_curr (r_wr_ptr_bin)
            );
        
            counter_bin #(
                .MAX   (D),
                .WIDTH (AW + 1)
            ) rd_ptr_counter_bin (
                .clk              (rd_clk),
                .rst_n            (rd_rst_n),
                .enable           (read && !rd_empty),
                .counter_bin_next (w_rd_ptr_bin_next),
                .counter_bin_curr (r_rd_ptr_bin)
            );
        
            // -----------------------------------------------------------------------
            // Johnson/Gray counters (wr/rd domains)
            // -----------------------------------------------------------------------
            counter_johnson #(
                .WIDTH (JCW)
            ) wr_ptr_counter_gray (
                .clk          (wr_clk),
                .rst_n        (wr_rst_n),
                .enable       (write && !wr_full),
                .counter_gray (r_wr_ptr_gray)
            );
        
            counter_johnson #(
                .WIDTH (JCW)
            ) rd_ptr_counter_gray (
                .clk          (rd_clk),
                .rst_n        (rd_rst_n),
                .enable       (read && !rd_empty),
                .counter_gray (r_rd_ptr_gray)
            );
        
            // -----------------------------------------------------------------------
            // CDC of Johnson/Gray pointers and conversion to binary
            // -----------------------------------------------------------------------
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (N),
                .WIDTH      (JCW)
            ) rd_ptr_gray_cross_inst (
                .q     (r_wdom_rd_ptr_gray),
                .d     (r_rd_ptr_gray),
                .clk   (wr_clk),
                .rst_n (wr_rst_n)
            );
        
            grayj2bin #(
                .JCW           (JCW),
                .WIDTH         (AW + 1),
                .INSTANCE_NAME ("rd_ptr_johnson2bin_inst")
            ) rd_ptr_gray2bin_inst (
                .binary (w_wdom_rd_ptr_bin),
                .gray   (r_wdom_rd_ptr_gray),
                .clk    (wr_clk),
                .rst_n  (wr_rst_n)
            );
        
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (N),
                .WIDTH      (JCW)
            ) wr_ptr_gray_cross_inst (
                .q     (r_rdom_wr_ptr_gray),
                .d     (r_wr_ptr_gray),
                .clk   (rd_clk),
                .rst_n (rd_rst_n)
            );
        
            grayj2bin #(
                .JCW           (JCW),
                .WIDTH         (AW + 1),
                .INSTANCE_NAME ("wr_ptr_gray2bin_inst")
            ) wr_ptr_gray2bin_inst (
                .binary (w_rdom_wr_ptr_bin),
                .gray   (r_rdom_wr_ptr_gray),
                .clk    (rd_clk),
                .rst_n  (rd_rst_n)
            );
        
            // -----------------------------------------------------------------------
            // Address extraction
            // -----------------------------------------------------------------------
            assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
            assign r_rd_addr = r_rd_ptr_bin[AW-1:0];
        
            // -----------------------------------------------------------------------
            // Flag/control logic (shared)
            // -----------------------------------------------------------------------
            fifo_control #(
                .DEPTH             (D),
                .ADDR_WIDTH        (AW),
                .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
                .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
                .REGISTERED        (REGISTERED)
            ) fifo_control_inst (
                .wr_clk           (wr_clk),
                .wr_rst_n         (wr_rst_n),
                .rd_clk           (rd_clk),
                .rd_rst_n         (rd_rst_n),
        
                .wr_ptr_bin       (w_wr_ptr_bin_next),
                .wdom_rd_ptr_bin  (w_wdom_rd_ptr_bin),
                .rd_ptr_bin       (w_rd_ptr_bin_next),
                .rdom_wr_ptr_bin  (w_rdom_wr_ptr_bin),
        
                .count            (),
                .wr_full          (wr_full),
                .wr_almost_full   (wr_almost_full),
                .rd_empty         (rd_empty),
                .rd_almost_empty  (rd_almost_empty)
            );
        
            // -----------------------------------------------------------------------
            // Memory implementation (scoped per MEM_STYLE)
            //  * SRL/AUTO: allow combinational read when REGISTERED==0
            //  * BRAM:     use synchronous read on rd_clk (true dual-port BRAM)
            //              ⇒ effective +1 cycle read latency (even if REGISTERED==0)
            // -----------------------------------------------------------------------
            generate
                if (MEM_STYLE == FIFO_SRL) begin : gen_srl
                    `ifdef XILINX
                        (* shreg_extract = "yes", ram_style = "distributed" *)
                    `elsif INTEL
                        /* synthesis ramstyle = "MLAB" */
                    `endif
                    logic [DATA_WIDTH-1:0] mem [DEPTH];
        
                    // Write port (wr_clk)
                    always_ff @(posedge wr_clk) begin
                        if (write && !wr_full) begin
                            mem[r_wr_addr] <= wr_data;
                        end
                    end
        
                    // Read port
                    if (REGISTERED != 0) begin : g_flop
                        `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                            if (!rd_rst_n) w_rd_data <= '0;
                            else           w_rd_data <= mem[r_rd_addr];
                        )
        
                    end else begin : g_mux
                        always_comb w_rd_data = mem[r_rd_addr];
                    end
        
                    // synopsys translate_off
                    logic [(DW*DEPTH)-1:0] flat_mem_srl;
                    genvar i_srl;
                    for (i_srl = 0; i_srl < DEPTH; i_srl++) begin : gen_flatten_srl
                        assign flat_mem_srl[i_srl*DW+:DW] = mem[i_srl];
                    end
                    // synopsys translate_on
                end
                else if (MEM_STYLE == FIFO_BRAM) begin : gen_bram
                    `ifdef XILINX
                        (* ram_style = "block" *)
                    `elsif INTEL
                        /* synthesis ramstyle = "M20K" */
                    `endif
                    logic [DATA_WIDTH-1:0] mem [DEPTH];
        
                    // Write port (wr_clk)
                    always_ff @(posedge wr_clk) begin
                        if (write && !wr_full) begin
                            mem[r_wr_addr] <= wr_data;
                        end
                    end
        
                    // Synchronous read port (rd_clk) to infer true dual-port BRAM
                    `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                        if (!rd_rst_n) w_rd_data <= '0;
                        else           w_rd_data <= mem[r_rd_addr];
                    )
        
        
                    // synopsys translate_off
                    logic [(DW*DEPTH)-1:0] flat_mem_bram;
                    genvar i_bram;
                    for (i_bram = 0; i_bram < DEPTH; i_bram++) begin : gen_flatten_bram
                        assign flat_mem_bram[i_bram*DW+:DW] = mem[i_bram];
                    end
                    // synopsys translate_on
        
                    // Optional notice if user expected mux behavior
                    initial begin
                        if (REGISTERED == 0) begin
                            $display("NOTE: %s BRAM style uses synchronous read; +1 cycle latency in rd domain.",
                                    INSTANCE_NAME);
                        end
                    end
                end
                else begin : gen_auto
                    // Let tool decide (LUTRAM vs BRAM). Allow comb read when REGISTERED==0.
                    logic [DATA_WIDTH-1:0] mem [DEPTH];
        
                    // Write port (wr_clk)
 004107             always_ff @(posedge wr_clk) begin
 000348                 if (write && !wr_full) begin
 000348                     mem[r_wr_addr] <= wr_data;
                        end
                    end
        
                    if (REGISTERED != 0) begin : g_flop
                        `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                            if (!rd_rst_n) w_rd_data <= '0;
                            else           w_rd_data <= mem[r_rd_addr];
 000164                 )
        
                    end else begin : g_mux
%000002                 always_comb w_rd_data = mem[r_rd_addr];
                    end
        
                    // synopsys translate_off
                    logic [(DW*DEPTH)-1:0] flat_mem_auto;
                    genvar i_auto;
                    for (i_auto = 0; i_auto < DEPTH; i_auto++) begin : gen_flatten_auto
                        assign flat_mem_auto[i_auto*DW+:DW] = mem[i_auto];
                    end
                    // synopsys translate_on
                end
            endgenerate
        
            // -----------------------------------------------------------------------
            // Output connect (common)
            // -----------------------------------------------------------------------
            assign rd_data = w_rd_data;
        
            // -----------------------------------------------------------------------
            // Simulation-only error checks
            // -----------------------------------------------------------------------
            // synopsys translate_off
 004107     always_ff @(posedge wr_clk) begin
%000000         if (write && wr_full) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
                end
            end
        
 004273     always_ff @(posedge rd_clk) begin
%000000         if (read && rd_empty) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             if (REGISTERED == 1)
%000000                 $display("Error: %s read while fifo empty (flop mode), %t", INSTANCE_NAME, $time);
                    else
%000000                 $display("Error: %s read while fifo empty (mux mode), %t", INSTANCE_NAME, $time);
                end
            end
            // synopsys translate_on
        
        endmodule : fifo_async_div2
        
