/**
* ============================================================================
* HPET Configuration Registers - Fixed Address Space (2-8 Timers)
* ============================================================================
*
* DESCRIPTION:
*   HPET configuration registers that support 2-8 timers with fixed 12-bit
*   address space for consistent programming interface across all configurations.
*
* FEATURES:
*   - Supports 2-8 timers (parameterizable)
*   - Fixed 12-bit address space (4KB)
*   - Traditional memory-mapped register layout
*   - 64-bit counter and comparator support
*   - Split LO/HI register access for 64-bit values
*   - Unused timer addresses safely return 0
*
* ADDRESS LAYOUT:
*   0x000-0x0FF: Global registers
*   0x100-0x1FF: Timer registers (32 bytes per timer)
*   0x200-0xFFF: Reserved for future expansion
*
* USAGE EXAMPLES:
*   // 2-timer RISC-V microcontroller version:
*   hpet_config_regs #(.VENDOR_ID(1), .REVISION_ID(1), .NUM_TIMERS(2)) hpet_regs_2t;
*
*   // 3-timer standard HPET version:
*   hpet_config_regs #(.VENDOR_ID(1), .REVISION_ID(2), .NUM_TIMERS(3)) hpet_regs_3t;
*
*   // 8-timer full HPET version:
*   hpet_config_regs #(.VENDOR_ID(1), .REVISION_ID(3), .NUM_TIMERS(8)) hpet_regs_8t;
* ============================================================================
*/

`timescale 1ns / 1ps

module hpet_config_regs #(
    parameter int VENDOR_ID = 1,         // Vendor ID for HPET_ID register
    parameter int REVISION_ID = 1,       // Revision ID for HPET_ID register
    parameter int NUM_TIMERS = 2         // Number of timers (2-8 supported)
)(
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic                    clk,
    input  logic                    rst_n,

    // ========================================================================
    // Command/Response Interface (from CDC)
    // ========================================================================
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,
    input  logic [11:0]             cmd_paddr,     // Fixed 12-bit addressing
    input  logic [31:0]             cmd_pwdata,     // Fixed 32-bit data
    input  logic [3:0]              cmd_pstrb,

    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [31:0]             rsp_prdata,     // Fixed 32-bit data
    output logic                    rsp_pslverr,

    // ========================================================================
    // HPET Core Interface
    // ========================================================================
    // Global Control
    output logic                    hpet_enable,
    output logic                    legacy_replacement,

    // Main Counter Control (64-bit counter)
    output logic                    counter_write,
    output logic [63:0]             counter_wdata,
    input  logic [63:0]             counter_rdata,

    // Timer Configuration
    output logic [NUM_TIMERS-1:0]   timer_enable,
    output logic [NUM_TIMERS-1:0]   timer_int_enable,
    output logic [NUM_TIMERS-1:0]   timer_type,
    output logic [NUM_TIMERS-1:0]   timer_size,
    output logic [NUM_TIMERS-1:0]   timer_value_set,

    // Timer Comparators (64-bit comparators)
    output logic [NUM_TIMERS-1:0]   timer_comp_write,
    output logic [63:0]             timer_comp_wdata,
    output logic                    timer_comp_write_high,  // 1=high half, 0=low half
    input  logic [63:0]             timer_comp_rdata [NUM_TIMERS],

    // Interrupt Status
    input  logic [NUM_TIMERS-1:0]   timer_int_status,
    output logic [NUM_TIMERS-1:0]   timer_int_clear
);

    // ============================================================================
    // PARAMETER VALIDATION
    // ============================================================================

    initial begin
        if (NUM_TIMERS < 2 || NUM_TIMERS > 8) begin
            $fatal(1, "ERROR: NUM_TIMERS=%0d is out of supported range (2-8)", NUM_TIMERS);
        end

        // Counter width is fixed at 64 bits for HPET

        $display("HPET Config: Vendor=0x%02X, Rev=0x%02X, %0d timers, 12-bit addressing (4096 bytes), 64-bit counter",
                VENDOR_ID, REVISION_ID, NUM_TIMERS);
    end

    // ============================================================================
    // REGISTER ADDRESS MAP - Fixed Addresses
    // ============================================================================
    // Global registers
    localparam reg [11:0] HPET_ID         = 12'h000;
    localparam reg [11:0] HPET_CONFIG     = 12'h004;
    localparam reg [11:0] HPET_STATUS     = 12'h008;

    // Counter registers
    localparam reg [11:0] HPET_COUNTER_LO = 12'h010;
    localparam reg [11:0] HPET_COUNTER_HI = 12'h014;

    // Timer register base addresses
    localparam reg [11:0] TIMER0_BASE     = 12'h100;
    localparam int TIMER_SPACING          = 32;  // 32 bytes per timer

    // ============================================================================
    // CONFIGURATION REGISTERS
    // ============================================================================
    logic r_hpet_enable;
    logic r_legacy_replacement;
    logic [NUM_TIMERS-1:0] r_timer_enable;
    logic [NUM_TIMERS-1:0] r_timer_int_enable;
    logic [NUM_TIMERS-1:0] r_timer_type;
    logic [NUM_TIMERS-1:0] r_timer_size;
    logic [NUM_TIMERS-1:0] r_timer_value_set;

    // ============================================================================
    // COMMAND PROCESSING
    // ============================================================================
    logic w_cmd_access;
    logic w_cmd_write;
    logic w_cmd_read;

    assign w_cmd_access = cmd_valid && cmd_ready;
    assign w_cmd_write = w_cmd_access && cmd_pwrite;
    assign w_cmd_read = w_cmd_access && !cmd_pwrite;

    // Always ready for single-cycle access
    assign cmd_ready = 1'b1;

    // ============================================================================
    // RESPONSE GENERATION
    // ============================================================================
    logic r_rsp_valid;
    logic [31:0] r_rsp_data;  // Fixed 32-bit data

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_rsp_valid <= 1'b0;
            r_rsp_data <= '0;
        end else begin
            r_rsp_valid <= w_cmd_access;
            if (w_cmd_read) begin
                r_rsp_data <= w_read_data;
            end else begin
                r_rsp_data <= '0;
            end
        end
    end

    assign rsp_valid = r_rsp_valid;
    assign rsp_prdata = r_rsp_data;
    assign rsp_pslverr = 1'b0;

    // ============================================================================
    // TIMER REGISTER DECODE
    // ============================================================================
    logic [NUM_TIMERS-1:0] w_timer_config_write;
    logic [NUM_TIMERS-1:0] w_timer_comp_write_int;
    logic [31:0] w_timer_read_data [NUM_TIMERS];  // Fixed 32-bit data

    // Timer write enable generation using loop
    always_comb begin
        w_timer_config_write = '0;
        w_timer_comp_write_int = '0;

        if (w_cmd_write) begin
            for (int i = 0; i < NUM_TIMERS; i++) begin
                // Calculate this timer's base address directly in comparisons
                
                // Check for config register write
                if (cmd_paddr == (TIMER0_BASE + 12'(i * TIMER_SPACING))) begin
                    w_timer_config_write[i] = 1'b1;
                end
                
                // Check for comparator writes (low or high)
                if (cmd_paddr == (TIMER0_BASE + 12'(i * TIMER_SPACING) + 12'h4) || 
                    cmd_paddr == (TIMER0_BASE + 12'(i * TIMER_SPACING) + 12'h8)) begin
                    w_timer_comp_write_int[i] = 1'b1;
                end
            end
        end
    end

    generate
        genvar g;
        for (g = 0; g < NUM_TIMERS; g++) begin : gen_timer_decode
            // Calculate this timer's register addresses
            localparam [11:0] T_BASE = TIMER0_BASE + 12'(g * TIMER_SPACING);
            localparam [11:0] T_CONFIG_ADDR = T_BASE + 12'h0;
            localparam [11:0] T_COMP_LO_ADDR = T_BASE + 12'h4;
            localparam [11:0] T_COMP_HI_ADDR = T_BASE + 12'h8;
            localparam [11:0] T_RESERVED_ADDR = T_BASE + 12'hC;

            // Read data generation
            always_comb begin
                w_timer_read_data[g] = '0;

                casez (cmd_paddr)
                    T_CONFIG_ADDR: begin
                        w_timer_read_data[g] = {25'h0, r_timer_value_set[g], r_timer_size[g],
                                            r_timer_type[g], r_timer_int_enable[g],
                                            r_timer_enable[g], 2'b00};
                    end

                    T_COMP_LO_ADDR: begin
                        w_timer_read_data[g] = timer_comp_rdata[g][31:0];
                    end

                    T_COMP_HI_ADDR: begin
                        w_timer_read_data[g] = timer_comp_rdata[g][63:32];
                    end

                    T_RESERVED_ADDR: begin
                        w_timer_read_data[g] = 32'h0;
                    end

                    default: begin
                        w_timer_read_data[g] = 32'h0;
                    end
                endcase
            end
        end
    endgenerate

    // ============================================================================
    // READ DATA MULTIPLEXER
    // ============================================================================
    logic [31:0] w_read_data;  // Fixed 32-bit data

    always_comb begin
        w_read_data = '0;

        casez (cmd_paddr)
            HPET_ID: begin
                // ID register with parameterized vendor and revision
                w_read_data = {8'(VENDOR_ID),            // Vendor ID [31:24]
                            8'(REVISION_ID),           // Rev ID [23:16]
                            5'h0,                      // Reserved [15:13]
                            3'(NUM_TIMERS-1),          // Number of timers - 1 [12:8]
                            1'b1,                      // 64-bit counter capable
                            1'b0,                      // Reserved
                            1'b1,                      // Legacy replacement capable
                            5'h0};                     // Reserved
            end

            HPET_CONFIG: begin
                w_read_data = {30'h0, r_legacy_replacement, r_hpet_enable};
            end

            HPET_STATUS: begin
                w_read_data = {{(32-NUM_TIMERS){1'b0}}, timer_int_status};
            end

            HPET_COUNTER_LO: begin
                w_read_data = counter_rdata[31:0];
            end

            HPET_COUNTER_HI: begin
                w_read_data = counter_rdata[63:32];
            end

            default: begin
                // Check timer addresses explicitly
                w_read_data = '0;

                // Select the appropriate timer's read data based on address
                for (int k = 0; k < NUM_TIMERS; k++) begin
                    if (cmd_paddr >= (TIMER0_BASE + 12'(k * TIMER_SPACING)) && 
                        cmd_paddr < (TIMER0_BASE + 12'(k * TIMER_SPACING) + 12'h20)) begin
                        w_read_data = w_timer_read_data[k];
                    end
                end
            end
        endcase
    end

    // ============================================================================
    // WRITE REGISTER LOGIC
    // ============================================================================
    logic w_counter_write_int;
    logic [NUM_TIMERS-1:0] w_int_clear;

    assign w_counter_write_int = w_cmd_write && ((cmd_paddr == HPET_COUNTER_LO) || (cmd_paddr == HPET_COUNTER_HI));
    assign w_int_clear = (w_cmd_write && (cmd_paddr == HPET_STATUS)) ? cmd_pwdata[NUM_TIMERS-1:0] : '0;

    // Configuration registers
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_hpet_enable <= 1'b0;
            r_legacy_replacement <= 1'b0;
            r_timer_enable <= '0;
            r_timer_int_enable <= '0;
            r_timer_type <= '0;
            r_timer_size <= '0;
            r_timer_value_set <= '0;
        end else begin
            // Global configuration
            if (w_cmd_write && (cmd_paddr == HPET_CONFIG)) begin
                r_hpet_enable <= cmd_pwdata[0];
                r_legacy_replacement <= cmd_pwdata[1];
            end

            // Timer configurations
            for (int t = 0; t < NUM_TIMERS; t++) begin
                if (w_timer_config_write[t]) begin
                    r_timer_enable[t] <= cmd_pwdata[2];
                    r_timer_int_enable[t] <= cmd_pwdata[3];
                    r_timer_type[t] <= cmd_pwdata[4];
                    r_timer_size[t] <= cmd_pwdata[5];
                    r_timer_value_set[t] <= cmd_pwdata[6];
                end
            end
        end
    end

    // ============================================================================
    // COUNTER AND COMPARATOR WRITE DATA HANDLING
    // ============================================================================
    logic [63:0] w_counter_write_data;
    logic [63:0] w_comp_write_data;

    // Latched counter write values for proper 64-bit writes
    logic [31:0] r_counter_write_lo;
    logic [31:0] r_counter_write_hi;
    logic r_counter_lo_written;
    logic r_counter_hi_written;

    // Latch counter write values
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter_write_lo <= '0;
            r_counter_write_hi <= '0;
            r_counter_lo_written <= 1'b0;
            r_counter_hi_written <= 1'b0;
        end else begin
            // Clear flags after counter write
            if (w_counter_write_int) begin
                r_counter_lo_written <= 1'b0;
                r_counter_hi_written <= 1'b0;
            end else begin
                // Latch low write
                if (w_cmd_write && (cmd_paddr == HPET_COUNTER_LO)) begin
                    r_counter_write_lo <= cmd_pwdata;
                    r_counter_lo_written <= 1'b1;
                end
                // Latch high write
                if (w_cmd_write && (cmd_paddr == HPET_COUNTER_HI)) begin
                    r_counter_write_hi <= cmd_pwdata;
                    r_counter_hi_written <= 1'b1;
                end
            end
        end
    end

    // Counter write data assembly (64-bit counter with 32-bit LO/HI access)
    always_comb begin
        if (cmd_paddr == HPET_COUNTER_LO) begin
            // When writing low, use latched high value if available, else current
            if (r_counter_hi_written) begin
                w_counter_write_data = {r_counter_write_hi, cmd_pwdata};
            end else begin
                w_counter_write_data = {counter_rdata[63:32], cmd_pwdata};
            end
        end else if (cmd_paddr == HPET_COUNTER_HI) begin
            // When writing high, use latched low value if available, else current
            if (r_counter_lo_written) begin
                w_counter_write_data = {cmd_pwdata, r_counter_write_lo};
            end else begin
                w_counter_write_data = {cmd_pwdata, counter_rdata[31:0]};
            end
        end else begin
            w_counter_write_data = counter_rdata;
        end
    end

    // Comparator write data assembly
    logic w_comp_write_is_high;

    always_comb begin
        w_comp_write_data = '0;
        w_comp_write_is_high = 1'b0;

        // Check all timer comparator addresses using loop
        for (int j = 0; j < NUM_TIMERS; j++) begin
            if (cmd_paddr == (TIMER0_BASE + 12'(j * TIMER_SPACING) + 12'h4)) begin
                // Writing to comparator low
                w_comp_write_data = {32'h0, cmd_pwdata};
                w_comp_write_is_high = 1'b0;
            end else if (cmd_paddr == (TIMER0_BASE + 12'(j * TIMER_SPACING) + 12'h8)) begin
                // Writing to comparator high
                w_comp_write_data = {cmd_pwdata, 32'h0};
                w_comp_write_is_high = 1'b1;
            end
        end
    end

    // ============================================================================
    // OUTPUT ASSIGNMENTS
    // ============================================================================
    assign hpet_enable = r_hpet_enable;
    assign legacy_replacement = r_legacy_replacement;
    assign timer_enable = r_timer_enable;
    assign timer_int_enable = r_timer_int_enable;
    assign timer_type = r_timer_type;
    assign timer_size = r_timer_size;
    assign timer_value_set = r_timer_value_set;

    assign timer_comp_write = w_timer_comp_write_int;
    assign counter_write = w_counter_write_int;

    assign counter_wdata = w_counter_write_data;
    assign timer_comp_wdata = w_comp_write_data;
    assign timer_comp_write_high = w_comp_write_is_high;
    assign timer_int_clear = w_int_clear;

endmodule : hpet_config_regs
