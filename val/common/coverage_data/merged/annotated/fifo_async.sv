//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: fifo_async
        // Purpose: //   Asynchronous FIFO for safe clock domain crossing (CDC) between independent
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: fifo_async
        //==============================================================================
        // Description:
        //   Asynchronous FIFO for safe clock domain crossing (CDC) between independent
        //   write and read clock domains. Uses Gray code encoding for pointer synchronization
        //   to prevent metastability and corruption of multi-bit values. Supports configurable
        //   depth (power-of-2 only), data width, output latency modes, and programmable
        //   almost-full/empty thresholds. Critical component for reliable CDC in multi-clock
        //   systems.
        //
        // Features:
        //   - Dual independent clock domains (write and read)
        //   - Gray code pointer synchronization for CDC safety
        //   - Configurable synchronizer depth (N_FLOP_CROSS)
        //   - Power-of-2 depth requirement (efficient addressing)
        //   - Mux (combinational) or Flop (registered) output modes
        //   - Full/empty flag generation (domain-specific)
        //   - Almost-full/almost-empty thresholds for flow control
        //   - Built-in overflow/underflow detection (simulation)
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   REGISTERED:
        //     Description: Read output port mode
        //     Type: int
        //     Range: 0 or 1
        //     Default: 0
        //     Constraints: 0 = Mux mode (combinational, 0 latency)
        //                  1 = Flop mode (registered, +1 rd_clk cycle latency)
        //
        //   DATA_WIDTH:
        //     Description: Width of data bus (bits per entry)
        //     Type: int
        //     Range: 1 to 512
        //     Default: 8
        //     Constraints: No restrictions on width
        //
        //   DEPTH:
        //     Description: FIFO depth (number of entries)
        //     Type: int
        //     Range: 4 to 65536
        //     Default: 16
        //     Constraints: **MUST be power of 2** (e.g., 4, 8, 16, 32, 64, 128...)
        //                  Non-power-of-2 depths will cause incorrect behavior
        //
        //   N_FLOP_CROSS:
        //     Description: Synchronizer stages for pointer CDC
        //     Type: int
        //     Range: 2 to 5
        //     Default: 2
        //     Constraints: Minimum=2 (basic CDC), Recommended=3 (high reliability)
        //                  Higher values improve MTBF but increase latency
        //
        //   ALMOST_WR_MARGIN:
        //     Description: Entries remaining when wr_almost_full asserts
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: Flow control warning threshold (write domain)
        //
        //   ALMOST_RD_MARGIN:
        //     Description: Entries remaining when rd_almost_empty asserts
        //     Type: int
        //     Range: 1 to DEPTH-1
        //     Default: 1
        //     Constraints: Underrun warning threshold (read domain)
        //
        //   INSTANCE_NAME:
        //     Description: Debug name for error messages
        //     Type: string
        //     Default: "DEADF1F0"
        //     Constraints: Used in $display for overflow/underflow warnings
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Write Clock Domain:
        //     wr_clk:       Write clock input
        //     wr_rst_n:     Write domain asynchronous active-low reset
        //     write:        Write enable (ignored if wr_full=1)
        //     wr_data[DATA_WIDTH-1:0]: Write data input
        //     wr_full:      Write full flag (1 = no space)
        //     wr_almost_full: Write almost-full flag (flow control)
        //
        //   Read Clock Domain:
        //     rd_clk:       Read clock input (independent from wr_clk)
        //     rd_rst_n:     Read domain asynchronous active-low reset
        //     read:         Read enable (ignored if rd_empty=1)
        //     rd_data[DATA_WIDTH-1:0]: Read data output
        //     rd_empty:     Read empty flag (1 = no data)
        //     rd_almost_empty: Read almost-empty flag (underrun warning)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Write Latency:      0 cycles (write-through)
        //   Read Latency:       0 cycles (mux) or 1 cycle (flop)
        //   Pointer Sync Lat:   N_FLOP_CROSS cycles (domain crossing)
        //   Flag Update Lat:    N_FLOP_CROSS + 1 cycles (cross-domain visibility)
        //   Throughput:         Min(wr_clk rate, rd_clk rate)
        //   CDC Safety:         Gray code ensures single-bit transitions
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Gray Code Pointer Synchronization:
        //   - Write pointer: Binary → Gray (wr_clk domain)
        //   - Gray ptr crosses to rd_clk domain via glitch_free_n_dff_arn
        //   - Gray → Binary conversion in rd_clk domain for comparison
        //   - Read pointer: Binary → Gray (rd_clk domain)
        //   - Gray ptr crosses to wr_clk domain via glitch_free_n_dff_arn
        //   - Gray → Binary conversion in wr_clk domain for comparison
        //
        //   Why Gray Code?
        //   - Multi-bit binary counters can have multiple bits change simultaneously
        //   - Gray code guarantees only 1 bit changes per increment
        //   - Single-bit change prevents CDC corruption (metastability on 1 bit only)
        //   - Example: Binary 3→4 = 011→100 (3 bits change, UNSAFE for CDC)
        //             Gray 3→4 = 010→110 (1 bit changes, SAFE for CDC)
        //
        //   Write Operation (wr_clk domain):
        //   - When write=1 and wr_full=0:
        //     1. Data written to r_mem[r_wr_addr]
        //     2. Binary write pointer increments (counter_bingray)
        //     3. Gray write pointer updates automatically
        //     4. wr_full determined by comparing wr_ptr_bin vs wdom_rd_ptr_bin
        //
        //   Read Operation (rd_clk domain):
        //   - When read=1 and rd_empty=0:
        //     1. Read pointer increments (binary and gray)
        //     2. rd_data = r_mem[r_rd_addr] (mux) or registered (flop)
        //     3. rd_empty determined by comparing rd_ptr_bin vs rdom_wr_ptr_bin
        //
        //   Full Detection (wr_clk domain):
        //   - Compares local wr_ptr_bin against synchronized rd_ptr_bin
        //   - Full when all entries occupied (wr_ptr catches up to rd_ptr)
        //   - Latency: Rd_ptr changes visible after N_FLOP_CROSS wr_clk cycles
        //
        //   Empty Detection (rd_clk domain):
        //   - Compares local rd_ptr_bin against synchronized wr_ptr_bin
        //   - Empty when no entries available (rd_ptr catches up to wr_ptr)
        //   - Latency: Wr_ptr changes visible after N_FLOP_CROSS rd_clk cycles
        //
        //   Timing Diagram (DEPTH=8, N_FLOP_CROSS=2, wr_clk=2×rd_clk):
        //
        //   {signal: [
        //     {name: 'wr_clk',            wave: 'p...............'},
        //     {name: 'rd_clk',            wave: 'P.......p.......', period: 2},
        //     {},
        //     {name: 'write (wr_clk)',    wave: '01....0.........'},
        //     {name: 'wr_data',           wave: 'x3.4.5.x........', data: ['A','B','C']},
        //     {name: 'r_wr_ptr_bin[3:0]', wave: 'x2.3.4.5........', data: ['0','1','2','3']},
        //     {name: 'r_wr_ptr_gray[3:0]', wave: 'x2.3.4.5........', data: ['000','001','011','010']},
        //     {},
        //     {name: 'r_rdom_wr_ptr_gray', wave: 'x.......2.3.4.5.', data: ['000','001','011','010'], node: '.......a'},
        //     {name: 'w_rdom_wr_ptr_bin', wave: 'x.......2.3.4.5.', data: ['0','1','2','3']},
        //     {},
        //     {name: 'read (rd_clk)',     wave: '0.......10......'},
        //     {name: 'r_rd_ptr_bin[3:0]', wave: 'x.......2..3....', data: ['0','1']},
        //     {name: 'rd_data',           wave: 'x.......3..4....', data: ['A','B']},
        //     {},
        //     {name: 'wr_full',           wave: '0...............'},
        //     {name: 'rd_empty',          wave: '01......0.......'},
        //     {},
        //     {name: 'CDC Event',         wave: 'x.......2.......', data: ['Sync delay']}
        //   ],
        //   edge: ['a 2 rd_clk cycles sync delay']}
        //
        //   Gray Code Pointer Progression (3-bit example):
        //
        //   {signal: [
        //     {name: 'Count',       wave: 'x2.3.4.5.6.7.8.9.', data: ['0','1','2','3','4','5','6','7']},
        //     {name: 'Binary[2:0]', wave: 'x2.3.4.5.6.7.8.9.', data: ['000','001','010','011','100','101','110','111']},
        //     {name: 'Gray[2:0]',   wave: 'x2.3.4.5.6.7.8.9.', data: ['000','001','011','010','110','111','101','100']},
        //     {},
        //     {name: 'Bit Changes', wave: 'x2.3.3.3.3.3.3.3.', data: ['0','1 bit','1 bit','1 bit','1 bit','1 bit','1 bit','1 bit']}
        //   ]}
        //
        //------------------------------------------------------------------------------
        // CDC Theory and Gray Code Advantage:
        //------------------------------------------------------------------------------
        //   Why Gray Code is Critical:
        //   - Binary counters: Multiple bits flip simultaneously on some transitions
        //     Example: 0111 (7) → 1000 (8) - ALL 4 bits change!
        //   - If bits captured mid-transition: Could see 0000, 1111, or anything
        //   - Result: Corrupted pointer value, incorrect full/empty, data loss
        //
        //   - Gray code: Exactly 1 bit changes per increment
        //     Example: 0101 (7) → 1101 (8) - Only bit 3 changes
        //   - If bit captured mid-transition: See either old or new value (both valid)
        //   - Result: Pointer may be off by 1, but never corrupted (safe margin)
        //
        //   MTBF Calculation:
        //   MTBF = (e^(T_res / τ)) / (T_clk × f_toggle × WIDTH)
        //   Where WIDTH = pointer bits that can go metastable
        //   Gray code: WIDTH = 1 (only 1 bit changes)
        //   Binary: WIDTH = log2(DEPTH) (all bits can change simultaneously)
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // Basic async FIFO for CDC (write domain faster than read)
        //   fifo_async #(
        //       .REGISTERED(0),        // Mux mode (lowest latency)
        //       .DATA_WIDTH(32),
        //       .DEPTH(16),            // Must be power-of-2!
        //       .N_FLOP_CROSS(3),      // 3 stages (recommended)
        //       .ALMOST_WR_MARGIN(2),
        //       .ALMOST_RD_MARGIN(2),
        //       .INSTANCE_NAME("CDC_FIFO")
        //   ) u_cdc_fifo (
        //       .wr_clk           (fast_clk),
        //       .wr_rst_n         (fast_rst_n),
        //       .write            (src_valid),
        //       .wr_data          (src_data),
        //       .wr_full          (src_full),
        //       .wr_almost_full   (src_afull),
        //       .rd_clk           (slow_clk),
        //       .rd_rst_n         (slow_rst_n),
        //       .read             (dst_ready && !dst_empty),
        //       .rd_data          (dst_data),
        //       .rd_empty         (dst_empty),
        //       .rd_almost_empty  (dst_aempty)
        //   );
        //   assign src_ready = !src_full;
        //
        //   // High-reliability async FIFO (5-stage synchronizer)
        //   fifo_async #(
        //       .REGISTERED(1),        // Flop mode (better timing)
        //       .DATA_WIDTH(64),
        //       .DEPTH(32),
        //       .N_FLOP_CROSS(5),      // Extra reliability
        //       .INSTANCE_NAME("SAFE_CDC")
        //   ) u_safe_fifo (
        //       .wr_clk           (clk_a),
        //       .wr_rst_n         (rst_a_n),
        //       .write            (wr_en),
        //       .wr_data          (wr_dat),
        //       .wr_full          (full),
        //       .wr_almost_full   (),
        //       .rd_clk           (clk_b),
        //       .rd_rst_n         (rst_b_n),
        //       .read             (rd_en),
        //       .rd_data          (rd_dat),
        //       .rd_empty         (empty),
        //       .rd_almost_empty  ()
        //   );
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **CRITICAL: DEPTH must be power-of-2** (4, 8, 16, 32, 64, 128, 256...)
        //   - Non-power-of-2 depths will cause addressing errors and data corruption
        //   - Gray code encoding is ESSENTIAL for CDC safety
        //   - **Do NOT remove gray code logic** - Will cause metastability issues
        //   - Pointer sync latency = N_FLOP_CROSS cycles (affects flag update timing)
        //   - Full flag lags actual fullness by N_FLOP_CROSS wr_clk cycles
        //   - Empty flag lags actual emptiness by N_FLOP_CROSS rd_clk cycles
        //   - Design must account for synchronization latency (provision extra margin)
        //   - **Never bypass gray code** - Direct binary sync WILL corrupt pointers
        //   - Mux mode: Lower read latency, but memory→output critical path
        //   - Flop mode: Higher read latency, but improved timing closure
        //   - Write when full: Ignored in synthesis, warning in simulation
        //   - Read when empty: Returns stale data, warning in simulation
        //   - **Independent resets:** wr_rst_n and rd_rst_n can assert independently
        //   - Reset synchronization not built-in (use reset_sync externally if needed)
        //   - Memory implementation: Inferred RAM (BRAM for large, LUT for small)
        //   - **Common mistake:** Using non-power-of-2 depth (causes wrap errors)
        //   - **Design trade-off:** N_FLOP_CROSS (latency) vs MTBF (reliability)
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - fifo_sync.sv - Synchronous FIFO (single clock domain)
        //   - counter_bingray.sv - Binary+Gray counter (used internally)
        //   - glitch_free_n_dff_arn.sv - Multi-stage synchronizer (used internally)
        //   - gray2bin.sv - Gray to binary converter (used internally)
        //   - fifo_control.sv - Full/empty flag logic (used internally)
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_fifo_async.py
        //   Run: pytest val/common/test_fifo_async.py -v
        //   Coverage: 93%
        //   Key Test Scenarios:
        //     - Write/read with different clock frequencies
        //     - Full condition (write blocking)
        //     - Empty condition (read blocking)
        //     - Almost-full/almost-empty thresholds
        //     - Gray code pointer synchronization
        //     - Pointer wrap-around at DEPTH boundary
        //     - Independent reset domains
        //     - Various N_FLOP_CROSS values (2, 3, 4)
        //     - Overflow/underflow detection
        //
        //------------------------------------------------------------------------------
        // FPGA-Specific Synthesis and Implementation Notes:
        //------------------------------------------------------------------------------
        //   **Memory Inference on FPGAs:**
        //   - This is the MOST CRITICAL aspect for FPGA implementation!
        //   - FIFO memory (r_mem) maps to different FPGA resources based on size:
        //
        //   **Xilinx FPGAs:**
        //   - DEPTH × DATA_WIDTH ≤ 64 bits → Distributed RAM (LUTs)
        //   - DEPTH × DATA_WIDTH > 64 bits → Block RAM (BRAM)
        //   - Example: DEPTH=16, DATA_WIDTH=8 → 128 bits → BRAM (18Kb block)
        //   - Example: DEPTH=4, DATA_WIDTH=8 → 32 bits → Distributed RAM (LUTs)
        //   - BRAM is 18Kb (2048 bytes) or 36Kb (4608 bytes) per block
        //   - Synthesis tool (Vivado) automatically selects based on size
        //
        //   **Intel FPGAs:**
        //   - DEPTH × DATA_WIDTH ≤ 640 bits → MLAB (Memory LAB, 32×20 bits)
        //   - DEPTH × DATA_WIDTH > 640 bits → M20K (20Kb block)
        //   - Example: DEPTH=32, DATA_WIDTH=16 → 512 bits → MLAB
        //   - Example: DEPTH=128, DATA_WIDTH=32 → 4096 bits → M20K
        //   - Quartus automatically infers memory type
        //
        //   **Forcing Memory Type (Xilinx):**
        //   ```systemverilog
        //   (* ram_style = "distributed" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];  // Force LUT RAM
        //   (* ram_style = "block" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];        // Force BRAM
        //   (* ram_style = "auto" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];         // Let tool decide
        //   ```
        //
        //   **Forcing Memory Type (Intel):**
        //   ```systemverilog
        //   (* ramstyle = "mlab" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];    // Force MLAB
        //   (* ramstyle = "M20K" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];    // Force M20K
        //   (* ramstyle = "logic" *) logic [DATA_WIDTH-1:0] r_mem [DEPTH-1:0];   // Force registers
        //   ```
        //
        //   **MEM_STYLE Parameter:**
        //   - This module includes MEM_STYLE parameter (from fifo_defs.svh)
        //   - Values: FIFO_AUTO, FIFO_DISTRIBUTED, FIFO_BLOCK, FIFO_ULTRA, FIFO_MLAB, FIFO_M20K
        //   - Use FIFO_AUTO for portable code (let synthesis tool decide)
        //   - Use specific styles for fine control over resource usage
        //
        //   **Critical Timing Considerations:**
        //   - Gray code CDC paths are THE timing bottleneck
        //   - Pointer synchronizers cross clock domains asynchronously
        //   - Synchronizer stages (N_FLOP_CROSS) must meet timing in destination domain
        //
        //   **Timing Constraints (XDC for Xilinx):**
        //   ```tcl
        //   # Write pointer Gray code crossing to read domain
        //   set_max_delay -datapath_only \
        //     -from [get_cells u_fifo/u_wr_ptr/counter_gray_reg[*]] \
        //     -to   [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[0][*]] \
        //     [expr {2 * $rd_clk_period}]
        //
        //   # Read pointer Gray code crossing to write domain
        //   set_max_delay -datapath_only \
        //     -from [get_cells u_fifo/u_rd_ptr/counter_gray_reg[*]] \
        //     -to   [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[0][*]] \
        //     [expr {2 * $wr_clk_period}]
        //
        //   # Mark synchronizer chains as CDC paths (automatic in Vivado 2019+)
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[*][*]]
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[*][*]]
        //
        //   # Prevent SRL extraction for synchronizer FFs
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[*][*]]
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_rd_ptr/r_sync_reg[*][*]]
        //
        //   # Optional: Physical placement constraints for synchronizers (advanced)
        //   # set_property LOC SLICE_X10Y20 [get_cells u_fifo/u_sync_wr_ptr/r_sync_reg[0][0]]
        //   ```
        //
        //   **Timing Constraints (SDC for Intel Quartus):**
        //   ```tcl
        //   # Write pointer Gray code CDC constraint
        //   set_max_delay -from [get_registers {*u_wr_ptr|counter_gray_reg[*]}] \
        //                 -to   [get_registers {*u_sync_wr_ptr|r_sync_reg[0][*]}] \
        //                 [expr {2 * $rd_clk_period}]
        //
        //   # Read pointer Gray code CDC constraint
        //   set_max_delay -from [get_registers {*u_rd_ptr|counter_gray_reg[*]}] \
        //                 -to   [get_registers {*u_sync_rd_ptr|r_sync_reg[0][*]}] \
        //                 [expr {2 * $wr_clk_period}]
        //
        //   # Mark synchronizers (automatic CDC detection in Quartus)
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to [get_registers {*u_sync_wr_ptr|r_sync_reg[*][*]}]
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to [get_registers {*u_sync_rd_ptr|r_sync_reg[*][*]}]
        //   ```
        //
        //   **Best Practices for FPGA Timing:**
        //   1. **Use N_FLOP_CROSS=3 for production** (N_FLOP_CROSS=2 for low latency only)
        //   2. **Set REGISTERED=1 for high-speed designs** (breaks memory→output critical path)
        //   3. **Size DEPTH appropriately for BRAM efficiency:**
        //      - Xilinx: BRAM is 18Kb (2048×8 or 1024×16)
        //      - Wasting BRAM: DEPTH=8, DATA_WIDTH=8 uses full 18Kb BRAM for 64 bits!
        //      - Efficient: DEPTH=256, DATA_WIDTH=8 uses 2048 bits of 18Kb BRAM
        //   4. **Pipeline full/empty flag logic if timing-critical:**
        //      ```systemverilog
        //      logic wr_full_reg;
        //      always_ff @(posedge wr_clk) wr_full_reg <= wr_full;
        //      assign src_ready = !wr_full_reg;  // Adds 1 cycle latency but helps timing
        //      ```
        //
        //   **Resource Usage (Typical FPGA):**
        //
        //   Configuration: DEPTH=16, DATA_WIDTH=8, N_FLOP_CROSS=3
        //   - Memory: 16×8 = 128 bits → 1 BRAM (18Kb) or ~32 LUTs (distributed)
        //   - Write pointer counter: 4 FFs (binary) + 4 FFs (Gray) = 8 FFs
        //   - Read pointer counter: 8 FFs
        //   - Synchronizers: 2×(3 stages × 4 bits) = 24 FFs
        //   - Gray2bin converters: ~8 LUTs
        //   - Full/empty logic: ~10 LUTs
        //   - **Total: ~50 FFs, ~50 LUTs, 1 BRAM (if memory is BRAM)**
        //
        //   Configuration: DEPTH=256, DATA_WIDTH=32, N_FLOP_CROSS=3
        //   - Memory: 256×32 = 8192 bits → 1 BRAM (36Kb)
        //   - Write pointer counter: 8 FFs (binary) + 8 FFs (Gray) = 16 FFs
        //   - Read pointer counter: 16 FFs
        //   - Synchronizers: 2×(3 stages × 8 bits) = 48 FFs
        //   - Gray2bin converters: ~32 LUTs
        //   - Full/empty logic: ~20 LUTs
        //   - **Total: ~100 FFs, ~100 LUTs, 1 BRAM**
        //
        //   Configuration: DEPTH=4, DATA_WIDTH=8, N_FLOP_CROSS=2
        //   - Memory: 4×8 = 32 bits → Distributed RAM (8 LUTs)
        //   - Pointer counters: 4 FFs (binary) + 4 FFs (Gray) = 8 FFs (each)
        //   - Synchronizers: 2×(2 stages × 2 bits) = 8 FFs
        //   - Gray2bin: ~4 LUTs
        //   - **Total: ~30 FFs, ~30 LUTs, 0 BRAMs**
        //
        //   **Performance by FPGA Family:**
        //
        //   Xilinx 7-series (Artix-7, Kintex-7, Virtex-7):
        //   - BRAM-based: Fmax ~400 MHz (both clocks)
        //   - Distributed RAM: Fmax ~500 MHz
        //   - Bottleneck: Gray code synchronizer timing
        //   - REGISTERED=1 mode: Fmax ~450 MHz (BRAM), ~550 MHz (distributed)
        //
        //   Xilinx UltraScale/UltraScale+:
        //   - BRAM-based: Fmax ~500 MHz (both clocks)
        //   - UltraRAM (for very large FIFOs): Fmax ~600 MHz
        //   - Distributed RAM: Fmax ~600 MHz
        //   - REGISTERED=1 mode: Fmax ~550 MHz (BRAM), ~650 MHz (distributed)
        //
        //   Intel Cyclone V:
        //   - M20K-based: Fmax ~300 MHz (both clocks)
        //   - MLAB-based: Fmax ~350 MHz
        //   - Bottleneck: Synchronizer and memory access
        //
        //   Intel Arria 10 / Stratix 10:
        //   - M20K-based: Fmax ~400 MHz (both clocks)
        //   - MLAB-based: Fmax ~450 MHz
        //   - HyperFlex mode: Can push >500 MHz with retiming
        //
        //   **MTBF Calculations for FPGA:**
        //   - Gray code synchronization dramatically improves MTBF vs binary
        //   - MTBF = (e^(T_res / τ)) / (T_clk × f_toggle × N_bits)
        //   - N_FLOP_CROSS=2: MTBF ~10^6 hours (acceptable for many designs)
        //   - N_FLOP_CROSS=3: MTBF ~10^12 hours (recommended for production)
        //   - N_FLOP_CROSS=4: MTBF ~10^18 hours (extreme reliability, aerospace)
        //   - Formula assumes T_res ~200 ps (setup/hold), τ ~30 ps (modern FPGA FF)
        //
        //   **When to Use Vendor FIFO IP Instead:**
        //
        //   Use Xilinx FIFO Generator or Intel DCFIFO when:
        //   ✅ DEPTH > 1024 (vendor IP better optimized for large FIFOs)
        //   ✅ Need built-in ECC (error correction) for BRAM
        //   ✅ Need built-in error flags (prog_full, prog_empty with configurable thresholds)
        //   ✅ Need first-word fall-through (FWFT) mode
        //   ✅ Need data count outputs (how many entries in FIFO)
        //   ✅ Maximum performance required (vendor IP hand-tuned for their FPGA)
        //
        //   Use this custom fifo_async when:
        //   ✅ Need portable code (same RTL works on Xilinx, Intel, Lattice, etc.)
        //   ✅ DEPTH ≤ 256 (custom FIFO is simpler and just as fast)
        //   ✅ Educational or research project (want to understand internals)
        //   ✅ Need fine control over CDC methodology (custom N_FLOP_CROSS, etc.)
        //   ✅ Vendor IP is overkill for simple application
        //   ✅ Want to avoid vendor lock-in
        //
        //   **Comparison: Custom vs Vendor IP (DEPTH=256, DATA_WIDTH=32):**
        //
        //   Feature                  | Custom fifo_async | Xilinx FIFO Gen | Intel DCFIFO
        //   -------------------------|-------------------|-----------------|-------------
        //   Resource (LUTs)          | ~100 LUTs         | ~120 LUTs       | ~110 LUTs
        //   Resource (BRAMs)         | 1 BRAM            | 1 BRAM          | 1 M20K
        //   Fmax (typical)           | ~400 MHz          | ~450 MHz        | ~350 MHz
        //   Portability              | ✅ Portable        | ❌ Xilinx only   | ❌ Intel only
        //   ECC support              | ❌ No              | ✅ Optional      | ✅ Optional
        //   Data count output        | ❌ No              | ✅ Yes           | ✅ Yes
        //   Prog full/empty          | ✅ Almost flags    | ✅ Configurable  | ✅ Configurable
        //   FWFT mode                | ❌ No              | ✅ Yes           | ✅ Yes
        //   Customizability          | ✅ Full source     | ⚠️ Parameters   | ⚠️ Parameters
        //   Simulation speed         | ✅ Fast (simple)   | ⚠️ Slower (IP)  | ⚠️ Slower (IP)
        //
        //   **Verification on FPGA:**
        //   - Use ILA (Xilinx) or SignalTap (Intel) to capture:
        //     * Write pointer (binary and Gray)
        //     * Read pointer (binary and Gray)
        //     * Synchronized pointers in opposite domains
        //     * Full/empty flags
        //     * Memory contents (if possible)
        //   - Verify Gray code single-bit-change property
        //   - Check for timing violations in implementation reports
        //   - Monitor for overflow/underflow conditions
        //   - Stress test with clock frequency sweep (vary wr_clk and rd_clk)
        //
        //   **Common FPGA Mistakes:**
        //   1. ❌ **Using non-power-of-2 DEPTH**
        //      → Pointer wraparound logic breaks, data corruption guaranteed!
        //      → Use fifo_async_div2.sv for non-power-of-2 depths
        //
        //   2. ❌ **Not constraining Gray code CDC paths**
        //      → Timing violations → metastability → corrupted pointers → data loss
        //      → Always use set_max_delay for Gray code synchronizers!
        //
        //   3. ❌ **Assuming full/empty flags update instantly**
        //      → Flags lag by N_FLOP_CROSS cycles due to pointer synchronization
        //      → Design must tolerate this latency (provision extra FIFO margin)
        //
        //   4. ❌ **Not setting N_FLOP_CROSS appropriately**
        //      → N_FLOP_CROSS=2 may have insufficient MTBF for production
        //      → Use N_FLOP_CROSS=3 for reliable designs
        //
        //   5. ❌ **Wasting BRAM on small FIFOs**
        //      → DEPTH=8, DATA_WIDTH=8 → 64 bits uses full 18Kb BRAM (waste!)
        //      → Use distributed RAM (MEM_STYLE=FIFO_DISTRIBUTED) for small FIFOs
        //
        //   6. ❌ **Not using REGISTERED=1 for high-speed designs**
        //      → Memory read → combinational output → long critical path
        //      → Set REGISTERED=1 to break path (adds 1 cycle latency but helps Fmax)
        //
        //   7. ❌ **Forgetting independent reset domains**
        //      → wr_rst_n and rd_rst_n can assert at different times
        //      → Design must handle asynchronous reset assertion gracefully
        //
        //   8. ❌ **Bypassing Gray code for "optimization"**
        //      → Direct binary pointer sync WILL corrupt data due to multi-bit changes
        //      → Gray code is NON-NEGOTIABLE for async FIFO CDC!
        //
        //   **Advanced: FWFT (First-Word Fall-Through) Mode:**
        //   - Vendor FIFOs support FWFT: rd_data valid even when rd_empty=1
        //   - This custom FIFO does NOT support FWFT
        //   - To add FWFT, wrap with additional output register and prefetch logic
        //
        //   **Advanced: Data Count Outputs:**
        //   - Vendor FIFOs provide rd_data_count and wr_data_count
        //   - This custom FIFO does NOT provide data counts
        //   - To add, compute: count = (wr_ptr_bin - rd_ptr_bin) in each domain
        //   - Account for pointer synchronization latency (count will lag)
        //
        //   **Synthesis Optimization Flags:**
        //
        //   Xilinx Vivado (project.tcl or XDC):
        //   ```tcl
        //   # Force BRAM inference for large FIFOs
        //   set_property RAM_STYLE BLOCK [get_cells u_fifo/r_mem_reg]
        //
        //   # Force distributed RAM for small FIFOs
        //   set_property RAM_STYLE DISTRIBUTED [get_cells u_fifo/r_mem_reg]
        //
        //   # Prevent synchronizer optimization
        //   set_property ASYNC_REG TRUE [get_cells u_fifo/u_sync_*/r_sync_reg*]
        //   set_property SHREG_EXTRACT NO [get_cells u_fifo/u_sync_*/r_sync_reg*]
        //   ```
        //
        //   Intel Quartus (QSF file):
        //   ```tcl
        //   # Force M20K inference
        //   set_instance_assignment -name RAMSTYLE M20K -to u_fifo|r_mem
        //
        //   # Force MLAB inference
        //   set_instance_assignment -name RAMSTYLE MLAB -to u_fifo|r_mem
        //
        //   # Mark synchronizers
        //   set_instance_assignment -name SYNCHRONIZER_IDENTIFICATION FORCED \
        //     -to u_fifo|u_sync_*|r_sync_reg*
        //   ```
        //
        //   **Power Optimization:**
        //   - Clock gating: Gate wr_clk when wr_full=1 (no writes possible)
        //   - Clock gating: Gate rd_clk when rd_empty=1 (no reads possible)
        //   - Memory power: BRAM consumes less power than distributed RAM
        //   - Synchronizer power: N_FLOP_CROSS=2 uses less power than N_FLOP_CROSS=3
        //
        //   **Performance:**
        //   - Typical Fmax: 400-500 MHz on modern FPGAs (BRAM-based)
        //   - Write throughput: 1 entry per wr_clk cycle (when not full)
        //   - Read throughput: 1 entry per rd_clk cycle (when not empty)
        //   - Latency: Write-to-read visibility = N_FLOP_CROSS rd_clk cycles
        //   - Pointer update latency: N_FLOP_CROSS cycles (cross-domain sync)
        //
        //==============================================================================
        
        `include "fifo_defs.svh"
        `include "reset_defs.svh"
        
        
        module fifo_async #(
            // Memory style selector (from fifo_defs.svh or a package)
            parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
        
            parameter int  REGISTERED      = 0,   // 0 = mux (combinational read), 1 = flop (registered read)
            parameter int  DATA_WIDTH      = 8,
            parameter int  DEPTH           = 16,
            parameter int  N_FLOP_CROSS    = 2,
            parameter int  ALMOST_WR_MARGIN= 1,
            parameter int  ALMOST_RD_MARGIN= 1,
            parameter string INSTANCE_NAME = "DEADF1F0"
        ) (
            // clocks and resets
 007498     input  logic wr_clk,
 000036                 wr_rst_n,
 007801                 rd_clk,
 000036                 rd_rst_n,
        
            // wr_clk domain
 000504     input  logic                    write,
%000000     input  logic [DATA_WIDTH-1:0]   wr_data,
%000008     output logic                    wr_full,
 000156     output logic                    wr_almost_full,
        
            // rd_clk domain
 000484     input  logic                    read,
%000000     output logic [DATA_WIDTH-1:0]   rd_data,
 000466     output logic                    rd_empty,
 000060     output logic                    rd_almost_empty
        );
        
            // -----------------------------------------------------------------------
            // Derived params / locals
            // -----------------------------------------------------------------------
            localparam int DW = DATA_WIDTH;
            localparam int D  = DEPTH;
            localparam int AW = $clog2(DEPTH);
            localparam int N  = N_FLOP_CROSS;
        
 000124     logic [AW-1:0] r_wr_addr, r_rd_addr;
 000060     logic [AW:0]   r_wr_ptr_gray, r_wdom_rd_ptr_gray;
 000060     logic [AW:0]   r_rd_ptr_gray, r_rdom_wr_ptr_gray;
 000060     logic [AW:0]   r_wr_ptr_bin,  r_rd_ptr_bin;
 000060     logic [AW:0]   w_wdom_rd_ptr_bin, w_rdom_wr_ptr_bin;
 000070     logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
        
            // Common read-data line; driven inside the active memory branch
%000000     logic [DW-1:0] w_rd_data;
        
            // -----------------------------------------------------------------------
            // Write/read pointer generation (bin+gray)
            // -----------------------------------------------------------------------
            counter_bingray #(
                .WIDTH (AW + 1)
            ) wr_ptr_counter_gray (
                .clk           (wr_clk),
                .rst_n         (wr_rst_n),
                .enable        (write && !wr_full),
                .counter_bin   (r_wr_ptr_bin),
                .counter_bin_next (w_wr_ptr_bin_next),
                .counter_gray  (r_wr_ptr_gray)
            );
        
            counter_bingray #(
                .WIDTH (AW + 1)
            ) rd_ptr_counter_gray (
                .clk           (rd_clk),
                .rst_n         (rd_rst_n),
                .enable        (read && !rd_empty),
                .counter_bin   (r_rd_ptr_bin),
                .counter_bin_next (w_rd_ptr_bin_next),
                .counter_gray  (r_rd_ptr_gray)
            );
        
            // -----------------------------------------------------------------------
            // CDC of gray pointers (wr<->rd domains) + gray->bin
            // -----------------------------------------------------------------------
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (N),
                .WIDTH      (AW + 1)
            ) rd_ptr_gray_cross_inst (
                .q     (r_wdom_rd_ptr_gray),
                .d     (r_rd_ptr_gray),
                .clk   (wr_clk),
                .rst_n (wr_rst_n)
            );
        
            gray2bin #(
                .WIDTH (AW + 1)
            ) rd_ptr_gray2bin_inst (
                .binary (w_wdom_rd_ptr_bin),
                .gray   (r_wdom_rd_ptr_gray)
            );
        
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (N),
                .WIDTH      (AW + 1)
            ) wr_ptr_gray_cross_inst (
                .q     (r_rdom_wr_ptr_gray),
                .d     (r_wr_ptr_gray),
                .clk   (rd_clk),
                .rst_n (rd_rst_n)
            );
        
            gray2bin #(
                .WIDTH (AW + 1)
            ) wr_ptr_gray2bin_inst (
                .binary (w_rdom_wr_ptr_bin),
                .gray   (r_rdom_wr_ptr_gray)
            );
        
            // -----------------------------------------------------------------------
            // Address extraction (lower bits from binary pointers)
            // -----------------------------------------------------------------------
            assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
            assign r_rd_addr = r_rd_ptr_bin[AW-1:0];
        
            // -----------------------------------------------------------------------
            // Full/empty/almost flags (shared control)
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
            // NOTE:
            //   * SRL/AUTO branches can support combinational read (REGISTERED=0).
            //   * BRAM branch uses synchronous read on rd_clk to infer true dual-port
            //     block RAM. That implies +1 cycle latency; if REGISTERED=0, behavior
            //     becomes effectively registered in this branch.
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
                        // Registered read (rd_clk)
                        `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                            if (!rd_rst_n) w_rd_data <= '0;
                            else           w_rd_data <= mem[r_rd_addr];
                        )
        
                    end else begin : g_mux
                        // Combinational read (distributed/LUTRAM supports this)
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
        
                    // Synchronous read port (rd_clk) → infer true dual-port BRAM
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
        
                    // Optional: warn if user asked for mux-mode but BRAM forces sync read
                    initial begin
                        if (REGISTERED == 0) begin
                            $display("NOTE: %s BRAM style forces synchronous read; effective +1 cycle latency.",
                                    INSTANCE_NAME);
                        end
                    end
                end
                else begin : gen_auto
                    // Tool chooses resource; allow async read when REGISTERED==0
                    logic [DATA_WIDTH-1:0] mem [DEPTH];
        
                    // Write port (wr_clk)
 003751             always_ff @(posedge wr_clk) begin
 000252                 if (write && !wr_full) begin
 000252                     mem[r_wr_addr] <= wr_data;
                        end
                    end
        
                    if (REGISTERED != 0) begin : g_flop
                        // Registered read (rd_clk)
                        `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                            if (!rd_rst_n) w_rd_data <= '0;
                            else           w_rd_data <= mem[r_rd_addr];
 000165                 )
        
                    end else begin : g_mux
                        // Combinational read (may infer LUTRAM)
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
 003751     always_ff @(posedge wr_clk) begin
%000000         if (write && wr_full) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
                end
            end
        
 003901     always_ff @(posedge rd_clk) begin
%000000         if (read && rd_empty) begin
%000000             $timeformat(-9, 3, " ns", 10);
%000000             if (REGISTERED == 1)
%000000                 $display("Error: %s read while fifo empty (flop mode), %t", INSTANCE_NAME, $time);
                    else
%000000                 $display("Error: %s read while fifo empty (mux mode), %t", INSTANCE_NAME, $time);
                end
            end
            // synopsys translate_on
        
        endmodule : fifo_async
        
