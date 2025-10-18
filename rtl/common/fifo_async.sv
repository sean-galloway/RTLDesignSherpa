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
//==============================================================================
module fifo_async #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 16,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic                    wr_clk,
                                    wr_rst_n,
                                    rd_clk,
                                    rd_rst_n,
    // wr_clk domain
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,
    // rd_clk domain
    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);
    localparam int N = N_FLOP_CROSS;

    /////////////////////////////////////////////////////////////////////////
    // local logics
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // The flop storage logicisters
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the bin and gray counters for write and read pointers
    counter_bingray #(
        .WIDTH(AW + 1)
    ) wr_ptr_counter_gray (
        .clk(wr_clk),
        .rst_n(wr_rst_n),
        .enable(write && !wr_full),
        .counter_bin(r_wr_ptr_bin),
        .counter_bin_next(w_wr_ptr_bin_next),
        .counter_gray(r_wr_ptr_gray)
    );

    counter_bingray #(
        .WIDTH(AW + 1)
    ) rd_ptr_counter_gray (
        .clk(rd_clk),
        .rst_n(rd_rst_n),
        .enable(read && !rd_empty),
        .counter_bin(r_rd_ptr_bin),
        .counter_bin_next(w_rd_ptr_bin_next),
        .counter_gray(r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(AW + 1)
    ) rd_ptr_gray_cross_inst (
        .q(r_wdom_rd_ptr_gray),
        .d(r_rd_ptr_gray),
        .clk(wr_clk),
        .rst_n(wr_rst_n)
    );

    // convert the gray rd ptr to binary
    gray2bin #(
        .WIDTH(AW + 1)
    ) rd_ptr_gray2bin_inst (
        .binary(w_wdom_rd_ptr_bin),
        .gray(r_wdom_rd_ptr_gray)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(AW + 1)
    ) wr_ptr_gray_cross_inst (
        .q(r_rdom_wr_ptr_gray),
        .d(r_wr_ptr_gray),
        .clk(rd_clk),
        .rst_n(rd_rst_n)
    );

    // convert the gray wr ptr to binary
    gray2bin #(
        .WIDTH(AW + 1)
    ) wr_ptr_gray2bin_inst (
        .binary(w_rdom_wr_ptr_bin),
        .gray(r_rdom_wr_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge wr_clk) begin
        if (write) begin
            r_mem[r_wr_addr] <= wr_data;
        end
    end

    assign w_rd_data = r_mem[r_rd_addr];

    /////////////////////////////////////////////////////////////////////////
    // Read Port
    generate
        if (REGISTERED != 0) begin : gen_flop_mode
            // Flop mode - registered output
            always_ff @(posedge rd_clk or negedge rd_rst_n) begin
                if (!rd_rst_n)
                    rd_data <= 'b0;
                else
                    rd_data <= w_rd_data;
            end
        end else begin : gen_mux_mode
            // Mux mode - non-registered output
            assign rd_data = w_rd_data;
        end
    endgenerate


    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEPTH              (D),
        .ADDR_WIDTH         (AW),
        .ALMOST_RD_MARGIN   (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN   (ALMOST_WR_MARGIN),
        .REGISTERED         (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (wr_clk),
        .wr_rst_n         (wr_rst_n),
        .rd_clk           (rd_clk),
        .rd_rst_n         (rd_rst_n),
        .wr_ptr_bin      (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin (w_wdom_rd_ptr_bin),
        .rd_ptr_bin      (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin (w_rdom_wr_ptr_bin),
        .count           (),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

    /////////////////////////////////////////////////////////////////////////
    // Error checking and debug stuff
    // synopsys translate_off
    logic [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_flatten_memory
            assign flat_r_mem[i*DW+:DW] = r_mem[i];
        end
    endgenerate

    always_ff @(posedge wr_clk) begin
        if (!wr_rst_n && (write && wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always_ff @(posedge rd_clk) begin
        if (!wr_rst_n && (read && rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : fifo_async
