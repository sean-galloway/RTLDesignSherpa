// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Cocotb TB wrapper around the FULL cdc_demo harness: the real uart_axil_bridge
// + cdc_demo_harness + four cdc_counter_domain instances. A cocotb
// UARTMaster/Monitor drives the IDENTICAL ASCII W/R byte stream the host program
// sends to silicon, so sim and FPGA are equivalent at the UART wire.
//
// What is NOT here (and why): cdc_demo_top's clock tree — MMCME2_BASE,
// BUFGMUX_CTRL, IBUF, BUFG — does not simulate in plain Verilator. That tree is
// the "analog" part; exactly as ddr2's sim swaps a7ddrphy for a DFI model, here
// the per-counter ctr_clk[i] are DRIVEN AS INPUTS from the cocotb test at
// co-prime periods (behavioral async clocks). Everything above the clock — the
// bridge RTL, the CSR decode, the CDC datapaths — is the real thing.
//
// Baud: UART_CLKS_PER_BIT is lowered for sim (16) so a command is thousands, not
// ~868*N, sim clocks. Bit-timing only; the byte stream is unchanged.

`timescale 1ns / 1ps

module cdc_demo_uart_tb_top #(
    parameter int UART_CLKS_PER_BIT = 16,   // lowered baud for sim
    parameter int NUM_COUNTERS      = 4,
    parameter int VAL_WIDTH         = 16,
    parameter int PRESS_WIDTH       = 16
) (
    input  logic aclk,
    input  logic aresetn,
    // UART pins the cocotb UARTMaster/Monitor attach to
    input  logic i_uart_rx,
    output logic o_uart_tx,
    // Per-counter source clocks — driven from the cocotb test (co-prime periods)
    input  logic i_ctr_clk0,
    input  logic i_ctr_clk1,
    input  logic i_ctr_clk2,
    input  logic i_ctr_clk3
);

    //=========================================================================
    // UART <-> AXIL bridge (the equivalence boundary — real RTL)
    //=========================================================================
    logic [31:0] axil_awaddr;   logic [2:0] axil_awprot;
    logic        axil_awvalid,  axil_awready;
    logic [31:0] axil_wdata;    logic [3:0] axil_wstrb;
    logic        axil_wvalid,   axil_wready;
    logic [1:0]  axil_bresp;    logic       axil_bvalid, axil_bready;
    logic [31:0] axil_araddr;   logic [2:0] axil_arprot;
    logic        axil_arvalid,  axil_arready;
    logic [31:0] axil_rdata;    logic [1:0] axil_rresp;
    logic        axil_rvalid,   axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (UART_CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_uart_rx       (i_uart_rx),
        .o_uart_tx       (o_uart_tx),
        .m_axil_awaddr   (axil_awaddr),  .m_axil_awprot  (axil_awprot),
        .m_axil_awvalid  (axil_awvalid), .m_axil_awready (axil_awready),
        .m_axil_wdata    (axil_wdata),   .m_axil_wstrb   (axil_wstrb),
        .m_axil_wvalid   (axil_wvalid),  .m_axil_wready  (axil_wready),
        .m_axil_bresp    (axil_bresp),   .m_axil_bvalid  (axil_bvalid),
        .m_axil_bready   (axil_bready),
        .m_axil_araddr   (axil_araddr),  .m_axil_arprot  (axil_arprot),
        .m_axil_arvalid  (axil_arvalid), .m_axil_arready (axil_arready),
        .m_axil_rdata    (axil_rdata),   .m_axil_rresp   (axil_rresp),
        .m_axil_rvalid   (axil_rvalid),  .m_axil_rready  (axil_rready)
    );

    logic w_uart_rx_act, w_uart_tx_act;
    assign w_uart_rx_act = axil_awvalid || axil_arvalid;
    assign w_uart_tx_act = axil_rvalid  || axil_bvalid;

    //=========================================================================
    // Harness CSR + per-counter fan-out (real RTL)
    //=========================================================================
    logic [NUM_COUNTERS-1:0][31:0]            w_cfg_divisor;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0]   w_cfg_init;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0]   w_cfg_increment;
    logic [NUM_COUNTERS-1:0]                  w_cfg_load_pulse;
    logic [NUM_COUNTERS-1:0]                  w_cfg_host_press_pulse;
    logic [NUM_COUNTERS-1:0][2:0]             w_cfg_cdc_mode;
    logic [NUM_COUNTERS-1:0]                  w_cfg_auto_inc;
    logic                                     w_cfg_freeze_all;
    logic                                     w_cfg_ignore_btn;

    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0]   w_status_value;
    logic [NUM_COUNTERS-1:0][PRESS_WIDTH-1:0] w_status_press_count;
    logic [NUM_COUNTERS-1:0][31:0]            w_status_clk_ticks;
    logic [NUM_COUNTERS-1:0]                  w_status_alive_event;
    logic [1:0]                               w_disp_select;
    logic                                     w_soft_reset;

    cdc_demo_harness #(
        .NUM_COUNTERS (NUM_COUNTERS),
        .VAL_WIDTH    (VAL_WIDTH),
        .PRESS_WIDTH  (PRESS_WIDTH),
        .PICKOFF_MAX  (4)
    ) u_harness (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr (axil_awaddr),  .s_axil_awprot (axil_awprot),
        .s_axil_awvalid(axil_awvalid), .s_axil_awready(axil_awready),
        .s_axil_wdata  (axil_wdata),   .s_axil_wstrb  (axil_wstrb),
        .s_axil_wvalid (axil_wvalid),  .s_axil_wready (axil_wready),
        .s_axil_bresp  (axil_bresp),   .s_axil_bvalid (axil_bvalid),
        .s_axil_bready (axil_bready),
        .s_axil_araddr (axil_araddr),  .s_axil_arprot (axil_arprot),
        .s_axil_arvalid(axil_arvalid), .s_axil_arready(axil_arready),
        .s_axil_rdata  (axil_rdata),   .s_axil_rresp  (axil_rresp),
        .s_axil_rvalid (axil_rvalid),  .s_axil_rready (axil_rready),
        .o_cfg_divisor          (w_cfg_divisor),
        .o_cfg_init             (w_cfg_init),
        .o_cfg_increment        (w_cfg_increment),
        .o_cfg_load_pulse       (w_cfg_load_pulse),
        .o_cfg_host_press_pulse (w_cfg_host_press_pulse),
        .o_cfg_cdc_mode         (w_cfg_cdc_mode),
        .o_cfg_auto_inc         (w_cfg_auto_inc),
        .o_cfg_freeze_all       (w_cfg_freeze_all),
        .o_cfg_ignore_btn       (w_cfg_ignore_btn),
        .i_status_value         (w_status_value),
        .i_status_press_count   (w_status_press_count),
        .i_status_clk_ticks     (w_status_clk_ticks),
        .i_status_alive_event   (w_status_alive_event),
        .o_disp_select          (w_disp_select),
        .o_soft_reset           (w_soft_reset),
        .i_uart_rx_activity     (w_uart_rx_act),
        .i_uart_tx_activity     (w_uart_tx_act),
        // Buttons unused in sim — host-press only.
        .i_btn_target_ctr        (2'b00),
        .i_btn_pickoff_inc_pulse (1'b0),
        .i_btn_pickoff_dec_pulse (1'b0),
        .i_btn_cdc_cycle_pulse   (1'b0),
        .i_btn_host_press_pulse  (1'b0),
        .i_btn_auto_inc_level    (1'b0),
        .i_btn_auto_inc_mask     ({NUM_COUNTERS{1'b0}})
    );

    //=========================================================================
    // Four counter domains — ctr_clk driven from the cocotb test (async).
    //=========================================================================
    logic [NUM_COUNTERS-1:0] w_ctr_clk;
    assign w_ctr_clk = {i_ctr_clk3, i_ctr_clk2, i_ctr_clk1, i_ctr_clk0};

    genvar gi;
    generate
        for (gi = 0; gi < NUM_COUNTERS; gi = gi + 1) begin : g_ctr
            cdc_counter_domain #(
                .VAL_WIDTH   (VAL_WIDTH),
                .PRESS_WIDTH (PRESS_WIDTH),
                .TICK_WIDTH  (32)
            ) u_ctr (
                .sys_clk                (aclk),
                .sys_rstn               (aresetn),
                .ctr_clk                (w_ctr_clk[gi]),
                .i_cfg_init             (w_cfg_init[gi]),
                .i_cfg_increment        (w_cfg_increment[gi]),
                .i_cfg_load_pulse       (w_cfg_load_pulse[gi]),
                .i_cfg_host_press_pulse (w_cfg_host_press_pulse[gi]),
                .i_cfg_freeze           (w_cfg_freeze_all),
                .i_cfg_ignore_btn       (w_cfg_ignore_btn),
                .i_cfg_cdc_mode         (w_cfg_cdc_mode[gi]),
                .i_cfg_auto_inc         (w_cfg_auto_inc[gi]),
                .i_btn                  (1'b0),
                .o_value                (w_status_value[gi]),
                .o_press_count          (w_status_press_count[gi]),
                .o_clk_ticks            (w_status_clk_ticks[gi]),
                .o_alive_event          (w_status_alive_event[gi])
            );
        end
    endgenerate

    // Silence unused-net warnings for the open harness outputs.
    wire unused = |{w_cfg_divisor, w_disp_select, w_soft_reset};

endmodule : cdc_demo_uart_tb_top
