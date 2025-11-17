`timescale 1ns / 1ps

//==============================================================================
// Module: simple_rom
//==============================================================================
// Description:
//   Simple read-only memory (ROM) with synchronous read access and optional
//   initialization from file. Designed for FPGA block RAM inference.
//
// Parameters:
//   ADDR_WIDTH - Address width in bits (default: 10, for 1024 entries)
//   DATA_WIDTH - Data width in bits (default: 32)
//   INIT_FILE  - Path to initialization file (hex format), use "none" for no init
//
// Interfaces:
//   clk  - Clock input
//   en   - Read enable (optional, can tie high for always-on)
//   addr - Read address
//   data - Read data output (registered)
//
// Notes:
//   - Single-cycle read latency (synchronous)
//   - FPGA block RAM inference with vendor-specific attributes
//   - No reset signal (ROM contents persist, only output register affected by enable)
//   - Array uses modern syntax [DEPTH] per repository standards
//
//==============================================================================

module simple_rom #(
    parameter int ADDR_WIDTH = 10,              // Address width (1024 entries default)
    parameter int DATA_WIDTH = 32,              // Data width
    parameter string INIT_FILE = "none"         // Memory initialization file (hex format)
) (
    input  logic                    clk,        // Clock
    input  logic                    en,         // Read enable
    input  logic [ADDR_WIDTH-1:0]   addr,       // Read address
    output logic [DATA_WIDTH-1:0]   data        // Read data (registered)
);

    //==========================================================================
    // Local Parameters
    //==========================================================================

    localparam int ROM_DEPTH = 2**ADDR_WIDTH;

    //==========================================================================
    // ROM Storage with FPGA Synthesis Attributes
    //==========================================================================

    // FPGA block RAM inference - vendor-specific attributes
    `ifdef XILINX
        (* rom_style = "block" *)  // Xilinx: Force block RAM
    `elsif INTEL
        /* synthesis ramstyle = "M20K" */  // Intel/Altera: Use M20K blocks
    `endif
    logic [DATA_WIDTH-1:0] rom_mem [ROM_DEPTH];  // Modern array syntax

    //==========================================================================
    // ROM Initialization
    //==========================================================================

    initial begin
        if (INIT_FILE != "none" && INIT_FILE != "") begin
            $readmemh(INIT_FILE, rom_mem);
            $display("[%t] ROM: Loaded initialization file '%s' (%0d entries)",
                     $time, INIT_FILE, ROM_DEPTH);
        end else begin
            // Initialize to zeros if no file specified
            for (int i = 0; i < ROM_DEPTH; i++) begin
                rom_mem[i] = '0;
            end
            $display("[%t] ROM: Initialized to zeros (%0d entries)", $time, ROM_DEPTH);
        end
    end

    //==========================================================================
    // Synchronous Read Logic (Required for BRAM Inference)
    //==========================================================================

    // Note: No reset signal for ROM - contents are persistent
    // Only the output register is controlled by enable
    always_ff @(posedge clk) begin
        if (en) begin
            data <= rom_mem[addr];
        end
        // When en=0, data holds previous value (register inference)
    end

endmodule : simple_rom
