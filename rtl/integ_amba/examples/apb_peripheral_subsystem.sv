// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_peripheral_subsystem
// Purpose: Apb Peripheral Subsystem module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_peripheral_subsystem #(
    parameter int ADDR_WIDTH = 16,   // 64KB address space
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = 4,

    // Monitor parameters
    parameter int MAX_TRANSACTIONS = 4,  // Simple peripherals, small value OK
    parameter int UNIT_ID = 0,

    // Agent IDs for each peripheral
    parameter logic [7:0] AGENT_ID_REGFILE = 8'h50,
    parameter logic [7:0] AGENT_ID_TIMER   = 8'h51,
    parameter logic [7:0] AGENT_ID_GPIO    = 8'h52
) (
    input  logic pclk,
    input  logic presetn,

    // =============================================================================
    // Single APB Master Interface (from CPU or bridge)
    // =============================================================================
    input  logic                  apb_psel,
    input  logic                  apb_penable,
    input  logic                  apb_pwrite,
    input  logic [2:0]            apb_pprot,
    input  logic [ADDR_WIDTH-1:0] apb_paddr,
    input  logic [DATA_WIDTH-1:0] apb_pwdata,
    input  logic [STRB_WIDTH-1:0] apb_pstrb,
    output logic                  apb_pready,
    output logic [DATA_WIDTH-1:0] apb_prdata,
    output logic                  apb_pslverr,

    // =============================================================================
    // Aggregated Monitor Output
    // =============================================================================
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output logic [63:0] monbus_data,

    // =============================================================================
    // Configuration
    // =============================================================================
    input logic cfg_error_enable,
    input logic cfg_compl_enable
);

    // =============================================================================
    // Address Decoding
    // =============================================================================
    // Address map:
    //   0x0000-0x0FFF: Register File (16 × 32-bit registers)
    //   0x1000-0x1FFF: Timer (control, count, compare registers)
    //   0x2000-0x2FFF: GPIO (data, direction, interrupt registers)

    localparam logic [ADDR_WIDTH-1:0] REGFILE_BASE = 16'h0000;
    localparam logic [ADDR_WIDTH-1:0] REGFILE_MASK = 16'hF000;
    localparam logic [ADDR_WIDTH-1:0] TIMER_BASE   = 16'h1000;
    localparam logic [ADDR_WIDTH-1:0] TIMER_MASK   = 16'hF000;
    localparam logic [ADDR_WIDTH-1:0] GPIO_BASE    = 16'h2000;
    localparam logic [ADDR_WIDTH-1:0] GPIO_MASK    = 16'hF000;

    logic sel_regfile, sel_timer, sel_gpio;

    assign sel_regfile = apb_psel && ((apb_paddr & REGFILE_MASK) == REGFILE_BASE);
    assign sel_timer   = apb_psel && ((apb_paddr & TIMER_MASK)   == TIMER_BASE);
    assign sel_gpio    = apb_psel && ((apb_paddr & GPIO_MASK)    == GPIO_BASE);

    // =============================================================================
    // Peripheral Interfaces
    // =============================================================================

    // Register File
    logic                  regfile_psel;
    logic                  regfile_penable;
    logic                  regfile_pwrite;
    logic [ADDR_WIDTH-1:0] regfile_paddr;
    logic [DATA_WIDTH-1:0] regfile_pwdata;
    logic [STRB_WIDTH-1:0] regfile_pstrb;
    logic                  regfile_pready;
    logic [DATA_WIDTH-1:0] regfile_prdata;
    logic                  regfile_pslverr;

    // Timer
    logic                  timer_psel;
    logic                  timer_penable;
    logic                  timer_pwrite;
    logic [ADDR_WIDTH-1:0] timer_paddr;
    logic [DATA_WIDTH-1:0] timer_pwdata;
    logic [STRB_WIDTH-1:0] timer_pstrb;
    logic                  timer_pready;
    logic [DATA_WIDTH-1:0] timer_prdata;
    logic                  timer_pslverr;

    // GPIO
    logic                  gpio_psel;
    logic                  gpio_penable;
    logic                  gpio_pwrite;
    logic [ADDR_WIDTH-1:0] gpio_paddr;
    logic [DATA_WIDTH-1:0] gpio_pwdata;
    logic [STRB_WIDTH-1:0] gpio_pstrb;
    logic                  gpio_pready;
    logic [DATA_WIDTH-1:0] gpio_prdata;
    logic                  gpio_pslverr;

    // Route master signals to selected peripheral
    assign regfile_psel    = sel_regfile;
    assign timer_psel      = sel_timer;
    assign gpio_psel       = sel_gpio;

    assign regfile_penable = apb_penable && sel_regfile;
    assign timer_penable   = apb_penable && sel_timer;
    assign gpio_penable    = apb_penable && sel_gpio;

    assign regfile_pwrite  = apb_pwrite;
    assign timer_pwrite    = apb_pwrite;
    assign gpio_pwrite     = apb_pwrite;

    assign regfile_paddr   = apb_paddr;
    assign timer_paddr     = apb_paddr;
    assign gpio_paddr      = apb_paddr;

    assign regfile_pwdata  = apb_pwdata;
    assign timer_pwdata    = apb_pwdata;
    assign gpio_pwdata     = apb_pwdata;

    assign regfile_pstrb   = apb_pstrb;
    assign timer_pstrb     = apb_pstrb;
    assign gpio_pstrb      = apb_pstrb;

    // Response muxing
    always_comb begin
        apb_pready  = 1'b0;
        apb_prdata  = '0;
        apb_pslverr = 1'b0;

        if (sel_regfile) begin
            apb_pready  = regfile_pready;
            apb_prdata  = regfile_prdata;
            apb_pslverr = regfile_pslverr;
        end else if (sel_timer) begin
            apb_pready  = timer_pready;
            apb_prdata  = timer_prdata;
            apb_pslverr = timer_pslverr;
        end else if (sel_gpio) begin
            apb_pready  = gpio_pready;
            apb_prdata  = gpio_prdata;
            apb_pslverr = gpio_pslverr;
        end else if (apb_psel) begin
            // Decode error - invalid address
            apb_pready  = 1'b1;
            apb_pslverr = 1'b1;
        end
    end

    // =============================================================================
    // Peripheral 1: Register File (Simple APB Slave)
    // =============================================================================
    // 16 × 32-bit registers at 0x0000-0x003C

    logic [15:0][31:0] registers;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            registers <= '0;
        end else if (regfile_psel && regfile_penable && regfile_pwrite) begin
            // Write operation
            logic [3:0] reg_addr;
            reg_addr = regfile_paddr[5:2];  // Word-aligned
            if (reg_addr < 16) begin
                for (int i = 0; i < 4; i++) begin
                    if (regfile_pstrb[i]) begin
                        registers[reg_addr][i*8 +: 8] <= regfile_pwdata[i*8 +: 8];
                    end
                end
            end
        end
    end

    assign regfile_pready  = 1'b1;  // Always ready
    assign regfile_prdata  = (regfile_paddr[5:2] < 16) ? registers[regfile_paddr[5:2]] : '0;
    assign regfile_pslverr = 1'b0;  // No errors

    // =============================================================================
    // Peripheral 2: Timer (Stub - for demonstration)
    // =============================================================================

    assign timer_pready  = 1'b1;
    assign timer_prdata  = 32'hDEAD_BEEF;  // Stub data
    assign timer_pslverr = 1'b0;

    // =============================================================================
    // Peripheral 3: GPIO (Stub - for demonstration)
    // =============================================================================

    assign gpio_pready  = 1'b1;
    assign gpio_prdata  = 32'hCAFE_BABE;  // Stub data
    assign gpio_pslverr = 1'b0;

    // =============================================================================
    // Monitor Bus Signals (3 monitors: one per peripheral)
    // =============================================================================

    localparam int NUM_MONITORS = 3;

    logic [NUM_MONITORS-1:0]        mon_valid;
    logic [NUM_MONITORS-1:0]        mon_ready;
    logic [NUM_MONITORS-1:0][63:0]  mon_data;

    // =============================================================================
    // Monitor 0: Register File
    // =============================================================================

    apb_monitor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .UNIT_ID(UNIT_ID),
        .AGENT_ID(AGENT_ID_REGFILE)
    ) u_regfile_mon (
        .pclk              (pclk),
        .presetn           (presetn),
        .psel              (regfile_psel),
        .penable           (regfile_penable),
        .pwrite            (regfile_pwrite),
        .paddr             (regfile_paddr),
        .pwdata            (regfile_pwdata),
        .pready            (regfile_pready),
        .prdata            (regfile_prdata),
        .pslverr           (regfile_pslverr),
        .monbus_pkt_valid  (mon_valid[0]),
        .monbus_pkt_ready  (mon_ready[0]),
        .monbus_pkt_data   (mon_data[0]),
        .cfg_error_enable  (cfg_error_enable),
        .cfg_compl_enable  (cfg_compl_enable),
        .cfg_timeout_enable(1'b0),  // Simple peripheral, no timeouts
        .cfg_perf_enable   (1'b0)
    );

    // =============================================================================
    // Monitor 1: Timer
    // =============================================================================

    apb_monitor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .UNIT_ID(UNIT_ID),
        .AGENT_ID(AGENT_ID_TIMER)
    ) u_timer_mon (
        .pclk              (pclk),
        .presetn           (presetn),
        .psel              (timer_psel),
        .penable           (timer_penable),
        .pwrite            (timer_pwrite),
        .paddr             (timer_paddr),
        .pwdata            (timer_pwdata),
        .pready            (timer_pready),
        .prdata            (timer_prdata),
        .pslverr           (timer_pslverr),
        .monbus_pkt_valid  (mon_valid[1]),
        .monbus_pkt_ready  (mon_ready[1]),
        .monbus_pkt_data   (mon_data[1]),
        .cfg_error_enable  (cfg_error_enable),
        .cfg_compl_enable  (cfg_compl_enable),
        .cfg_timeout_enable(1'b0),
        .cfg_perf_enable   (1'b0)
    );

    // =============================================================================
    // Monitor 2: GPIO
    // =============================================================================

    apb_monitor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .UNIT_ID(UNIT_ID),
        .AGENT_ID(AGENT_ID_GPIO)
    ) u_gpio_mon (
        .pclk              (pclk),
        .presetn           (presetn),
        .psel              (gpio_psel),
        .penable           (gpio_penable),
        .pwrite            (gpio_pwrite),
        .paddr             (gpio_paddr),
        .pwdata            (gpio_pwdata),
        .pready            (gpio_pready),
        .prdata            (gpio_prdata),
        .pslverr           (gpio_pslverr),
        .monbus_pkt_valid  (mon_valid[2]),
        .monbus_pkt_ready  (mon_ready[2]),
        .monbus_pkt_data   (mon_data[2]),
        .cfg_error_enable  (cfg_error_enable),
        .cfg_compl_enable  (cfg_compl_enable),
        .cfg_timeout_enable(1'b0),
        .cfg_perf_enable   (1'b0)
    );

    // =============================================================================
    // Monitor Bus Arbiter (Simple Round-Robin)
    // =============================================================================

    arbiter_round_robin #(
        .N(NUM_MONITORS),
        .REG_OUTPUT(1)
    ) u_mon_arbiter (
        .i_clk     (pclk),
        .i_rst_n   (presetn),
        .i_request (mon_valid),
        .o_grant   (mon_ready),
        .o_valid   (monbus_valid)
    );

    // Data muxing
    logic [1:0] grant_id;
    always_comb begin
        grant_id = '0;
        for (int i = 0; i < NUM_MONITORS; i++) begin
            if (mon_ready[i]) grant_id = i[1:0];
        end
    end
    assign monbus_data = mon_data[grant_id];

endmodule : apb_peripheral_subsystem
