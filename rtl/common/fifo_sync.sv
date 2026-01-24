// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: fifo_sync
// Purpose: //   Parameterized synchronous FIFO (First-In-First-Out) buffer for single clock
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: fifo_sync
//==============================================================================
// Description:
//   Parameterized synchronous FIFO (First-In-First-Out) buffer for single clock
//   domain data buffering. Supports configurable depth, data width, and output
//   latency modes. Provides full/empty flags and configurable almost-full/almost-empty
//   thresholds for flow control. Uses binary counters with MSB inversion for
//   efficient full/empty detection. Ideal for rate matching, data packetization,
//   and pipeline decoupling.
//
// Features:
//   - Arbitrary depth (power-of-2 optimized but supports any depth)
//   - Configurable data width (1 to 512+ bits)
//   - Two output modes: Mux (combinational) or Flop (registered)
//   - Full/empty flag generation
//   - Almost-full/almost-empty thresholds (programmable margins)
//   - Write-through operation (no bubble cycles)
//   - Built-in overflow/underflow detection (simulation only)
//   - Efficient counter_bin implementation for pointers
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   REGISTERED:
//     Description: Output port mode selection
//     Type: int
//     Range: 0 or 1
//     Default: 0
//     Constraints: 0 = Mux mode (combinational rd_data, 0 latency)
//                  1 = Flop mode (registered rd_data, +1 cycle latency)
//                  Mux mode: Lower latency, critical timing path
//                  Flop mode: Higher latency, improved timing closure
//
//   DATA_WIDTH:
//     Description: Width of data bus (bits per entry)
//     Type: int
//     Range: 1 to 512
//     Default: 4
//     Constraints: Resource usage scales linearly with DATA_WIDTH
//
//   DEPTH:
//     Description: FIFO depth (number of entries)
//     Type: int
//     Range: 2 to 65536
//     Default: 4
//     Constraints: Actual depth = DEPTH (not restricted to power-of-2)
//                  Address width = $clog2(DEPTH)
//
//   ALMOST_WR_MARGIN:
//     Description: Entries remaining when almost_full asserts
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//     Constraints: wr_almost_full asserts when (DEPTH - count) ≤ MARGIN
//
//   ALMOST_RD_MARGIN:
//     Description: Entries remaining when almost_empty asserts
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//     Constraints: rd_almost_empty asserts when count ≤ MARGIN
//
//   INSTANCE_NAME:
//     Description: Debug name for error messages
//     Type: string
//     Default: "DEADF1F0"
//     Constraints: Used in $display for overflow/underflow warnings
//
//   Derived Parameters (localparam - computed automatically):
//     DW: Alias for DATA_WIDTH (convenience for internal declarations)
//     D: Alias for DEPTH (convenience for internal declarations)
//     AW: Address width ($clog2(DEPTH))
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:              Clock input (single clock domain)
//     rst_n:            Asynchronous active-low reset
//     write:            Write enable (ignored if wr_full=1)
//     wr_data[DATA_WIDTH-1:0]: Write data input
//     read:             Read enable (ignored if rd_empty=1)
//
//   Outputs:
//     wr_full:          Write full flag (1 = no space remaining)
//     wr_almost_full:   Write almost-full flag (flow control warning)
//     rd_empty:         Read empty flag (1 = no data available)
//     rd_almost_empty:  Read almost-empty flag (underrun warning)
//     rd_data[DATA_WIDTH-1:0]: Read data output (latency depends on REGISTERED)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Write Latency:      0 cycles (write-through, data visible next cycle)
//   Read Latency:       0 cycles (mux mode) or 1 cycle (flop mode)
//   Flag Latency:       0 cycles (combinational from pointers)
//   Throughput:         1 read + 1 write per cycle (simultaneous RW supported)
//   Critical Path (Mux): Memory read → rd_data (long path)
//   Critical Path (Flop): Memory read → FF (shorter path)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Pointer Management:
//   - Write pointer (r_wr_ptr_bin): Increments on write when not full
//   - Read pointer (r_rd_ptr_bin): Increments on read when not empty
//   - Pointers use counter_bin module with MSB inversion for wrap detection
//   - Address extraction: addr = ptr[AW-1:0] (lower bits)
//
//   Full/Empty Detection:
//   - Handled by fifo_control module
//   - Full: wr_ptr catches up to rd_ptr (all entries filled)
//   - Empty: rd_ptr catches up to wr_ptr (all entries read)
//   - Almost flags: Configurable thresholds for proactive flow control
//
//   Write Operation:
//   - When write=1 and wr_full=0:
//     1. Data written to mem[r_wr_addr]
//     2. Write pointer increments
//     3. Flags update based on new count
//   - When write=1 and wr_full=1:
//     * Write ignored, overflow warning (simulation)
//
//   Read Operation (Mux Mode, REGISTERED=0):
//   - When read=1 and rd_empty=0:
//     1. Read pointer increments
//     2. rd_data = mem[new r_rd_addr] (combinational)
//     3. Flags update based on new count
//   - Read latency: 0 cycles (data available same cycle)
//
//   Read Operation (Flop Mode, REGISTERED=1):
//   - When read=1 and rd_empty=0:
//     1. Read pointer increments
//     2. rd_data <= mem[r_rd_addr] (registered, +1 cycle)
//     3. Flags update based on new count
//   - Read latency: 1 cycle (data registered for timing)
//
//   Simultaneous Read/Write:
//   - Supported when FIFO is neither full nor empty
//   - Count remains constant (one in, one out)
//   - Useful for streaming applications
//
//   Timing Diagram (DEPTH=4, DATA_WIDTH=8, REGISTERED=0 mux mode):
//
//   {signal: [
//     {name: 'clk',              wave: 'p...............'},
//     {name: 'rst_n',            wave: '01..............'},
//     {},
//     {name: 'write',            wave: '0.1...10........'},
//     {name: 'wr_data[7:0]',     wave: 'x.3...4.x.......', data: ['A0','A1']},
//     {name: 'read',             wave: '0......1...0....'},
//     {},
//     {name: 'r_wr_ptr_bin[2:0]', wave: 'x.2.3.4.4.......', data: ['0','1','2','2']},
//     {name: 'r_rd_ptr_bin[2:0]', wave: 'x.2.....2.3.4...', data: ['0','0','1','2']},
//     {name: 'count',            wave: 'x.2.3.4.3.2.1...', data: ['0','1','2','1','0','0']},
//     {},
//     {name: 'wr_full',          wave: '0...............'},
//     {name: 'rd_empty',         wave: '01.......0......'},
//     {name: 'rd_data[7:0]',     wave: 'x.......3.4.x...', data: ['A0','A1']},
//     {},
//     {name: 'Event',            wave: 'x.2.3.4.5.6.7...', data: ['Wr A0','Wr A1','Wr A1','Rd A0','Rd A1','Empty']}
//   ]}
//
//   Full/Almost-Full Scenario (DEPTH=4, ALMOST_WR_MARGIN=1):
//
//   {signal: [
//     {name: 'clk',              wave: 'p.............'},
//     {name: 'write',            wave: '01.......0....'},
//     {name: 'wr_data',          wave: 'x3.4.5.6.x....', data: ['D0','D1','D2','D3']},
//     {},
//     {name: 'count',            wave: 'x2.3.4.5.5....', data: ['0','1','2','3','4']},
//     {name: 'wr_almost_full',   wave: '0.....1.......'},
//     {name: 'wr_full',          wave: '0.......1.....'},
//     {},
//     {name: 'Event',            wave: 'x2.3...4.5....', data: ['Wr D0','Wr D2','Alm Full','FULL']}
//   ]}
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Basic synchronous FIFO for data buffering (mux mode)
//   fifo_sync #(
//       .REGISTERED(0),        // Mux mode (0 latency)
//       .DATA_WIDTH(32),       // 32-bit data
//       .DEPTH(16),            // 16-entry FIFO
//       .ALMOST_WR_MARGIN(2),  // Almost-full at 14 entries
//       .ALMOST_RD_MARGIN(2),  // Almost-empty at 2 entries
//       .INSTANCE_NAME("PKT_FIFO")
//   ) u_pkt_fifo (
//       .clk              (clk),
//       .rst_n            (rst_n),
//       .write            (pkt_valid),
//       .wr_data          (pkt_data),
//       .wr_full          (fifo_full),
//       .wr_almost_full   (fifo_afull),
//       .read             (downstream_ready && !fifo_empty),
//       .rd_data          (fifo_out),
//       .rd_empty         (fifo_empty),
//       .rd_almost_empty  (fifo_aempty)
//   );
//   assign pkt_ready = !fifo_full;  // Backpressure
//
//   // Registered output FIFO for timing closure (flop mode)
//   fifo_sync #(
//       .REGISTERED(1),        // Flop mode (+1 cycle latency)
//       .DATA_WIDTH(64),
//       .DEPTH(32),
//       .INSTANCE_NAME("PIPELINE_FIFO")
//   ) u_pipe_fifo (
//       .clk              (core_clk),
//       .rst_n            (rst_n),
//       .write            (stage1_valid),
//       .wr_data          (stage1_data),
//       .wr_full          (stage1_stall),
//       .wr_almost_full   (),  // Not used
//       .read             (stage2_ready),
//       .rd_data          (stage2_data),
//       .rd_empty         (stage2_empty),
//       .rd_almost_empty  ()   // Not used
//   );
//
//   // Flow control with almost-full threshold
//   fifo_sync #(
//       .REGISTERED(0),
//       .DATA_WIDTH(128),
//       .DEPTH(64),
//       .ALMOST_WR_MARGIN(8),  // Trigger backpressure early
//       .ALMOST_RD_MARGIN(8)
//   ) u_flow_fifo (
//       .clk              (clk),
//       .rst_n            (rst_n),
//       .write            (src_valid && !fifo_afull),  // Stop at almost-full
//       .wr_data          (src_data),
//       .wr_full          (fifo_full),
//       .wr_almost_full   (fifo_afull),
//       .read             (dst_ready && !fifo_empty),
//       .rd_data          (dst_data),
//       .rd_empty         (fifo_empty),
//       .rd_almost_empty  (fifo_aempty)
//   );
//   assign src_ready = !fifo_afull;  // Proactive backpressure
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Single clock domain only** - Use fifo_async for CDC
//   - Simultaneous read/write supported (count constant)
//   - **Mux mode (REGISTERED=0):** Lower latency, but memory-to-output critical path
//   - **Flop mode (REGISTERED=1):** Higher latency, but breaks timing path
//   - Write when full is IGNORED (not an error in synthesis, warning in sim)
//   - Read when empty is IGNORED (returns stale data, warning in sim)
//   - Almost flags are combinational (update same cycle as pointer change)
//   - **DEPTH does not need to be power-of-2** - Arbitrary depths supported
//   - Address wrapping handled by counter_bin module (MSB inversion)
//   - **Memory implementation:** Inferred RAM (synthesizer chooses BRAM/LUT)
//   - For small FIFOs: Likely synthesizes to registers/LUTs
//   - For large FIFOs: Likely synthesizes to block RAM
//   - flat_mem is debug-only (synthesis ignored via translate_off)
//   - INSTANCE_NAME used for error messages (helps debug multi-FIFO designs)
//   - **Resource usage:** DEPTH × DATA_WIDTH bits of memory + control logic
//   - **Critical path (mux):** mem read → mux → rd_data (can be long)
//   - **Critical path (flop):** mem read → FF (shorter, better for timing)
//   - No built-in reset synchronization (use reset_sync externally if needed)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - fifo_async.sv - Asynchronous FIFO for clock domain crossing
//   - fifo_control.sv - Full/empty flag generation logic (used internally)
//   - counter_bin.sv - Binary counter for read/write pointers (used internally)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_fifo_sync.py
//   Run: pytest val/common/test_fifo_sync.py -v
//   Coverage: 96%
//   Key Test Scenarios:
//     - Basic write/read operations
//     - Full condition (write blocking)
//     - Empty condition (read blocking)
//     - Almost-full/almost-empty thresholds
//     - Simultaneous read/write
//     - Wraparound behavior
//     - Mux mode (REGISTERED=0) vs Flop mode (REGISTERED=1)
//     - Overflow/underflow detection
//
//==============================================================================

`include "fifo_defs.svh"
`include "reset_defs.svh"


module fifo_sync
#(
    parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
    parameter int    REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int    DATA_WIDTH = 4,
    parameter int    DEPTH = 4,
    parameter int    ALMOST_WR_MARGIN = 1,
    parameter int    ALMOST_RD_MARGIN = 1,
    parameter string INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic                    clk,
                                    rst_n,
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,
    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    // -----------------------------------------------------------------------
    // Derived parameters / locals
    // -----------------------------------------------------------------------
    localparam int DW = DATA_WIDTH;
    localparam int D  = DEPTH;
    localparam int AW = $clog2(DEPTH);

    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // Common read-data wire driven inside the active MEM_STYLE branch
    logic [DW-1:0] w_rd_data;

    // -----------------------------------------------------------------------
    // Write/Read pointers
    // -----------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) write_pointer_inst (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (write && !wr_full),
        .counter_bin_curr (r_wr_ptr_bin),
        .counter_bin_next (w_wr_ptr_bin_next)
    );

    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) read_pointer_inst (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (read && !rd_empty),
        .counter_bin_curr (r_rd_ptr_bin),
        .counter_bin_next (w_rd_ptr_bin_next)
    );

    // -----------------------------------------------------------------------
    // Flag/control logic
    // -----------------------------------------------------------------------
    fifo_control #(
        .DEPTH            (D),
        .ADDR_WIDTH       (AW),
        .ALMOST_RD_MARGIN (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN (ALMOST_WR_MARGIN),
        .REGISTERED       (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (clk),
        .wr_rst_n         (rst_n),
        .rd_clk           (clk),
        .rd_rst_n         (rst_n),
        .wr_ptr_bin       (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin  (w_rd_ptr_bin_next),
        .rd_ptr_bin       (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin  (w_wr_ptr_bin_next),
        .count            (),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

    // -----------------------------------------------------------------------
    // Address extraction
    // -----------------------------------------------------------------------
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    // -----------------------------------------------------------------------
    // Memory implementation (scoped per MEM_STYLE)
    // Ensure all mem accesses live inside the same generate branch.
    // -----------------------------------------------------------------------
    generate
        if (MEM_STYLE == FIFO_SRL) begin : gen_srl
            `ifdef XILINX
                (* shreg_extract = "yes", ram_style = "distributed" *)
            `elsif INTEL
                /* synthesis ramstyle = "MLAB" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge clk) begin
                if (write && !wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path
            if (REGISTERED != 0) begin : g_flop
                `ALWAYS_FF_RST(clk, rst_n,
                    if (!rst_n) w_rd_data <= '0;
                    else        w_rd_data <= mem[r_rd_addr];
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

            // Write path
            always_ff @(posedge clk) begin
                if (write && !wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path
            if (REGISTERED != 0) begin : g_flop
                `ALWAYS_FF_RST(clk, rst_n,
                    if (!rst_n) w_rd_data <= '0;
                    else        w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_bram;
            genvar i_bram;
            for (i_bram = 0; i_bram < DEPTH; i_bram++) begin : gen_flatten_bram
                assign flat_mem_bram[i_bram*DW+:DW] = mem[i_bram];
            end
            // synopsys translate_on
        end
        else begin : gen_auto
            // No vendor hint; allow tool to infer LUT/BRAM
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge clk) begin
                if (write && !wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path
            if (REGISTERED != 0) begin : g_flop
                `ALWAYS_FF_RST(clk, rst_n,
                    if (!rst_n) w_rd_data <= '0;
                    else        w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
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
    // Simulation-only: Instance report (grep for FIFO_INSTANCE)
    // -----------------------------------------------------------------------
    // synopsys translate_off
    initial begin
        $display("FIFO_INSTANCE: fifo_sync %m %s W=%0d D=%0d MEM=%s REG=%0d", INSTANCE_NAME, DW, D, MEM_STYLE.name(), REGISTERED);
    end
    // synopsys translate_on

    // -----------------------------------------------------------------------
    // Simulation-only error checks
    // -----------------------------------------------------------------------
    // synopsys translate_off
    always_ff @(posedge clk) begin
        if (write && wr_full) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always_ff @(posedge clk) begin
        if (read && rd_empty) begin
            $timeformat(-9, 3, " ns", 10);
            if (REGISTERED == 1)
                $display("Error: %s read while fifo empty (flop mode), %t", INSTANCE_NAME, $time);
            else
                $display("Error: %s read while fifo empty (mux mode), %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : fifo_sync
