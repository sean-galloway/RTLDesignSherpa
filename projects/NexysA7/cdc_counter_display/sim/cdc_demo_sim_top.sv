// SPDX-License-Identifier: MIT
//
// cdc_demo_sim_top.sv — sim-only top wiring cdc_demo_harness to one
// cdc_counter_domain for cocotb smoke tests. The AXIL slave is exposed
// at the top level so cocotb can drive it directly (no UART bridge).

`timescale 1ns / 1ps

module cdc_demo_sim_top #(
    parameter int NUM_COUNTERS = 1,    // sim uses a single counter
    parameter int VAL_WIDTH    = 16,
    parameter int PRESS_WIDTH  = 16
) (
    input  logic        aclk,
    input  logic        aresetn,

    // AXIL slave (cocotb drives these)
    input  logic [31:0] s_axil_awaddr,
    input  logic [2:0]  s_axil_awprot,
    input  logic        s_axil_awvalid,
    output logic        s_axil_awready,
    input  logic [31:0] s_axil_wdata,
    input  logic [3:0]  s_axil_wstrb,
    input  logic        s_axil_wvalid,
    output logic        s_axil_wready,
    output logic [1:0]  s_axil_bresp,
    output logic        s_axil_bvalid,
    input  logic        s_axil_bready,
    input  logic [31:0] s_axil_araddr,
    input  logic [2:0]  s_axil_arprot,
    input  logic        s_axil_arvalid,
    output logic        s_axil_arready,
    output logic [31:0] s_axil_rdata,
    output logic [1:0]  s_axil_rresp,
    output logic        s_axil_rvalid,
    input  logic        s_axil_rready,

    // Tied off to 0 for sim — no physical button
    input  logic        i_btn
);

    logic [NUM_COUNTERS-1:0][31:0]         w_cfg_divisor;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] w_cfg_init;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] w_cfg_increment;
    logic [NUM_COUNTERS-1:0]               w_cfg_load_pulse;
    logic [NUM_COUNTERS-1:0]               w_cfg_host_press_pulse;
    logic [NUM_COUNTERS-1:0][2:0]          w_cfg_cdc_mode;
    logic [NUM_COUNTERS-1:0]               w_cfg_auto_inc;
    logic                                  w_cfg_freeze_all;
    logic                                  w_cfg_ignore_btn;

    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0]   w_status_value;
    logic [NUM_COUNTERS-1:0][PRESS_WIDTH-1:0] w_status_press_count;
    logic [NUM_COUNTERS-1:0][31:0]            w_status_clk_ticks;
    logic [NUM_COUNTERS-1:0]                  w_status_alive_event;
    logic [1:0] w_disp_select;
    logic       w_soft_reset;

    cdc_demo_harness #(
        .NUM_COUNTERS (NUM_COUNTERS),
        .VAL_WIDTH    (VAL_WIDTH),
        .PRESS_WIDTH  (PRESS_WIDTH)
    ) u_harness (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr (s_axil_awaddr), .s_axil_awprot (s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata  (s_axil_wdata),   .s_axil_wstrb  (s_axil_wstrb),
        .s_axil_wvalid (s_axil_wvalid),  .s_axil_wready (s_axil_wready),
        .s_axil_bresp  (s_axil_bresp),   .s_axil_bvalid (s_axil_bvalid),
        .s_axil_bready (s_axil_bready),
        .s_axil_araddr (s_axil_araddr),  .s_axil_arprot (s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata  (s_axil_rdata),   .s_axil_rresp  (s_axil_rresp),
        .s_axil_rvalid (s_axil_rvalid),  .s_axil_rready (s_axil_rready),
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
        .i_uart_rx_activity     (1'b0),
        .i_uart_tx_activity     (1'b0),
        // Board-button live controls — tied off for sim
        .i_btn_target_ctr       (2'b00),
        .i_btn_pickoff_inc_pulse(1'b0),
        .i_btn_pickoff_dec_pulse(1'b0),
        .i_btn_cdc_cycle_pulse  (1'b0),
        .i_btn_host_press_pulse (1'b0),
        .i_btn_auto_inc_level   (1'b0),
        .i_btn_auto_inc_mask    ({NUM_COUNTERS{1'b0}})
    );

    cdc_counter_domain #(
        .VAL_WIDTH   (VAL_WIDTH),
        .PRESS_WIDTH (PRESS_WIDTH),
        .TICK_WIDTH  (32)
    ) u_ctr (
        .sys_clk                  (aclk),
        .sys_rstn                 (aresetn),
        .i_cfg_divisor            (w_cfg_divisor[0]),
        .i_cfg_init               (w_cfg_init[0]),
        .i_cfg_increment          (w_cfg_increment[0]),
        .i_cfg_load_pulse         (w_cfg_load_pulse[0]),
        .i_cfg_host_press_pulse   (w_cfg_host_press_pulse[0]),
        .i_cfg_freeze             (w_cfg_freeze_all),
        .i_cfg_ignore_btn         (w_cfg_ignore_btn),
        .i_cfg_cdc_mode           (w_cfg_cdc_mode[0]),
        .i_cfg_auto_inc           (w_cfg_auto_inc[0]),
        .i_btn                    (i_btn),
        .o_value                  (w_status_value[0]),
        .o_press_count            (w_status_press_count[0]),
        .o_clk_ticks              (w_status_clk_ticks[0]),
        .o_alive_event            (w_status_alive_event[0])
    );

endmodule
