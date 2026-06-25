// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: cdc_demo_top
// Purpose: Board-level top for the CDC counter demo (phase 2, v3).
//
//          v3 changes vs v2:
//            - Source clocks for the 4 counters now come from an MMCM
//              with 4 co-prime divisors -- truly asynchronous to each
//              other (no shared edge alignment).
//            - Per counter, a tree of 4 BUFGMUX_CTRL instances selects
//              one of 5 source clocks at runtime:
//                idx 0..3: MMCM outputs at 72.7 / 27.6 / 11.9 / 6.25 MHz
//                idx 4:    sys_clk-derived "slow" clock from a per-counter
//                          clock_divider (DIV_PICKOFF, 0..31 selectable)
//                          — keeps the "visible 6 Hz counting" demo alive
//              Switching is glitchless (BUFGMUX_CTRL guarantee).
//            - Harness CSR DIVISOR field is reinterpreted:
//                bits [2:0] = CLOCK_SELECT (0..4, others map to NO-CDC behavior)
//                bits [12:8] = DIV_PICKOFF (5 bits for the divided-clock branch)
//
// Display layout (left → right):
//   AN[7:6] = CDC mode (hex 00..04)
//   AN[5:4] = pickoff/clock-select indicator
//   AN[3:0] = 16-bit value
//
// Controls — see docs/RUNBOOK.md for the full operator guide.

`timescale 1ns / 1ps

module cdc_demo_top (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,     // BTNR / active-low reset

    input  logic        UART_TXD_IN,    // FTDI → FPGA  (pin C4)
    output logic        UART_RXD_OUT,   // FPGA → FTDI  (pin D4)

    input  logic        btnC,           // inject press for selected counter
    input  logic        btnU,           // step CLOCK_SELECT UP   (faster MMCM output)
    input  logic        btnD,           // step CLOCK_SELECT DOWN (slower MMCM output)
    input  logic        btnL,           // cycle CDC mode

    input  logic [15:0] SW,             // SW[1:0]=ctr select, SW[15]=AUTO_INC level

    output logic [7:0]  LED,

    output logic [7:0]  AN,
    output logic [6:0]  SEG,
    output logic        DP
);

    // ----------------------------------------------------------------
    // System clock + reset
    // ----------------------------------------------------------------
    logic sys_clk;
    logic sys_rstn;
    logic w_soft_reset;
    logic sys_clk_pad;

    // Buffer the input pin onto the global clock network.
    IBUF u_sys_ibuf (.I(CLK100MHZ), .O(sys_clk_pad));
    BUFG u_sys_bufg (.I(sys_clk_pad), .O(sys_clk));

    (* ASYNC_REG = "TRUE" *) logic r_rstn_sync0, r_rstn_sync1;
    always_ff @(posedge sys_clk or negedge CPU_RESETN) begin
        if (!CPU_RESETN) begin
            r_rstn_sync0 <= 1'b0;
            r_rstn_sync1 <= 1'b0;
        end else begin
            r_rstn_sync0 <= 1'b1;
            r_rstn_sync1 <= r_rstn_sync0;
        end
    end
    assign sys_rstn = r_rstn_sync1 && !w_soft_reset;

    // ----------------------------------------------------------------
    // MMCM — 4 co-prime divided outputs from a 100 MHz reference.
    //
    //   CLKFBOUT_MULT_F = 8.0  → VCO = 800 MHz  (valid range 600..1600)
    //   DIVCLK_DIVIDE   = 1
    //   CLKOUT0_DIVIDE  = 11   → 72.7 MHz   (idx 0, fastest)
    //   CLKOUT1_DIVIDE  = 29   → 27.6 MHz   (idx 1)
    //   CLKOUT2_DIVIDE  = 67   → 11.9 MHz   (idx 2)
    //   CLKOUT3_DIVIDE  = 128  →  6.25 MHz  (idx 3, slowest MMCM output)
    //
    // Divisors {11, 29, 67, 128} are pairwise co-prime (11/29/67 are
    // prime, 128 = 2^7 is co-prime to each odd prime). No two outputs
    // share an edge alignment more often than LCM(11*29*67*128)
    // cycles. For practical purposes: truly asynchronous.
    // ----------------------------------------------------------------
    logic mmcm_locked;
    logic mmcm_fb;
    logic clk_mmcm_72m;     // CLKOUT0 = 72.7 MHz
    logic clk_mmcm_27m;     // CLKOUT1 = 27.6 MHz
    logic clk_mmcm_12m;     // CLKOUT2 = 11.9 MHz
    logic clk_mmcm_6m;      // CLKOUT3 =  6.25 MHz
    logic clk_mmcm_72m_raw, clk_mmcm_27m_raw, clk_mmcm_12m_raw, clk_mmcm_6m_raw;

    // MMCM reset from the raw board reset (NOT the soft-reset path —
    // softrst shouldn't drop the MMCM and force a re-lock).
    logic sys_rstn_raw_for_mmcm;
    assign sys_rstn_raw_for_mmcm = r_rstn_sync1;

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKFBOUT_MULT_F   (8.0),         // VCO = 100 * 8 = 800 MHz
        .CLKFBOUT_PHASE    (0.0),
        .CLKIN1_PERIOD     (10.0),        // 100 MHz period in ns
        .DIVCLK_DIVIDE     (1),
        .REF_JITTER1       (0.010),
        .STARTUP_WAIT      ("FALSE"),
        .CLKOUT0_DIVIDE_F  (11.0),        // 72.73 MHz
        .CLKOUT1_DIVIDE    (29),          // 27.59 MHz
        .CLKOUT2_DIVIDE    (67),          // 11.94 MHz
        .CLKOUT3_DIVIDE    (128),         //  6.25 MHz
        .CLKOUT0_DUTY_CYCLE(0.5), .CLKOUT0_PHASE(0.0),
        .CLKOUT1_DUTY_CYCLE(0.5), .CLKOUT1_PHASE(0.0),
        .CLKOUT2_DUTY_CYCLE(0.5), .CLKOUT2_PHASE(0.0),
        .CLKOUT3_DUTY_CYCLE(0.5), .CLKOUT3_PHASE(0.0)
    ) u_mmcm (
        .CLKIN1     (sys_clk),
        .CLKFBIN    (mmcm_fb),
        .CLKFBOUT   (mmcm_fb),
        .CLKOUT0    (clk_mmcm_72m_raw),
        .CLKOUT1    (clk_mmcm_27m_raw),
        .CLKOUT2    (clk_mmcm_12m_raw),
        .CLKOUT3    (clk_mmcm_6m_raw),
        .CLKOUT4    (), .CLKOUT5    (), .CLKOUT6    (),
        .CLKFBOUTB  (),
        .CLKOUT0B   (), .CLKOUT1B   (), .CLKOUT2B   (), .CLKOUT3B   (),
        .LOCKED     (mmcm_locked),
        .PWRDWN     (1'b0),
        .RST        (!sys_rstn_raw_for_mmcm)
    );

    // BUFGs onto the MMCM outputs so they reach the BUFGMUX_CTRL inputs
    // on global clock routing.
    BUFG u_bufg_72m (.I(clk_mmcm_72m_raw), .O(clk_mmcm_72m));
    BUFG u_bufg_27m (.I(clk_mmcm_27m_raw), .O(clk_mmcm_27m));
    BUFG u_bufg_12m (.I(clk_mmcm_12m_raw), .O(clk_mmcm_12m));
    BUFG u_bufg_6m  (.I(clk_mmcm_6m_raw),  .O(clk_mmcm_6m));

    // ----------------------------------------------------------------
    // UART <-> AXIL bridge
    // ----------------------------------------------------------------
    logic [31:0] axil_awaddr;
    logic [2:0]  axil_awprot;
    logic        axil_awvalid, axil_awready;
    logic [31:0] axil_wdata;
    logic [3:0]  axil_wstrb;
    logic        axil_wvalid,  axil_wready;
    logic [1:0]  axil_bresp;
    logic        axil_bvalid,  axil_bready;
    logic [31:0] axil_araddr;
    logic [2:0]  axil_arprot;
    logic        axil_arvalid, axil_arready;
    logic [31:0] axil_rdata;
    logic [1:0]  axil_rresp;
    logic        axil_rvalid,  axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (868)
    ) u_uart_bridge (
        .aclk            (sys_clk),
        .aresetn         (sys_rstn),
        .i_uart_rx       (UART_TXD_IN),
        .o_uart_tx       (UART_RXD_OUT),
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

    // ----------------------------------------------------------------
    // Button debounce + edge detect (sys_clk)
    // ----------------------------------------------------------------
    logic [3:0] btn_raw;
    assign btn_raw = {btnL, btnD, btnU, btnC};

    (* ASYNC_REG = "TRUE" *) logic [3:0] r_btn_sync0;
    (* ASYNC_REG = "TRUE" *) logic [3:0] r_btn_sync1;
    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) begin r_btn_sync0 <= 4'h0; r_btn_sync1 <= 4'h0; end
        else           begin r_btn_sync0 <= btn_raw; r_btn_sync1 <= r_btn_sync0; end
    end

    logic [3:0] r_btn_stable;
    logic [3:0] r_btn_prev;
    logic [20:0] r_debounce_cnt [4];
    logic [3:0]  w_btn_pressed;

    genvar bi;
    generate
        for (bi = 0; bi < 4; bi = bi + 1) begin : g_db
            always_ff @(posedge sys_clk or negedge sys_rstn) begin
                if (!sys_rstn) begin
                    r_btn_stable[bi]    <= 1'b0;
                    r_btn_prev[bi]      <= 1'b0;
                    r_debounce_cnt[bi]  <= 21'd0;
                end else begin
                    r_btn_prev[bi] <= r_btn_stable[bi];
                    if (r_btn_sync1[bi] != r_btn_stable[bi]) begin
                        if (r_debounce_cnt[bi] == 21'h1FFFFF) begin
                            r_btn_stable[bi]   <= r_btn_sync1[bi];
                            r_debounce_cnt[bi] <= 21'd0;
                        end else begin
                            r_debounce_cnt[bi] <= r_debounce_cnt[bi] + 1'b1;
                        end
                    end else begin
                        r_debounce_cnt[bi] <= 21'd0;
                    end
                end
            end
            assign w_btn_pressed[bi] = r_btn_stable[bi] && !r_btn_prev[bi];
        end
    endgenerate

    // {btnL, btnD, btnU, btnC} → indices 3,2,1,0
    logic w_btn_press_pulse;     // BTNC
    logic w_btn_clksel_up;       // BTNU — toward faster (clock_select decreasing, 0=fastest)
    logic w_btn_clksel_down;     // BTND — toward slower
    logic w_btn_cdc_cycle;       // BTNL
    assign w_btn_press_pulse = w_btn_pressed[0];
    assign w_btn_clksel_up   = w_btn_pressed[1];
    assign w_btn_clksel_down = w_btn_pressed[2];
    assign w_btn_cdc_cycle   = w_btn_pressed[3];

    // ----------------------------------------------------------------
    // Switches → harness
    // ----------------------------------------------------------------
    logic [1:0]                 w_sel_ctr;
    logic                       w_auto_inc_level;
    logic [3:0]                 w_auto_inc_mask;

    assign w_sel_ctr        = SW[1:0];
    assign w_auto_inc_level = SW[15];
    always_comb begin
        w_auto_inc_mask = 4'h0;
        w_auto_inc_mask[w_sel_ctr] = 1'b1;
    end

    // ----------------------------------------------------------------
    // Harness CSR
    // ----------------------------------------------------------------
    localparam int NUM_COUNTERS  = 4;
    localparam int VAL_WIDTH     = 16;
    localparam int PRESS_WIDTH   = 16;

    logic [NUM_COUNTERS-1:0][31:0]            w_cfg_divisor;     // packed: [2:0]=CLOCK_SELECT, [12:8]=DIV_PICKOFF
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
    logic [1:0]                               w_disp_select_csr;

    cdc_demo_harness #(
        .NUM_COUNTERS (NUM_COUNTERS),
        .VAL_WIDTH    (VAL_WIDTH),
        .PRESS_WIDTH  (PRESS_WIDTH),
        .PICKOFF_MAX  (4)              // CLOCK_SELECT clamped to 0..4 (5 inputs)
    ) u_harness (
        .aclk(sys_clk), .aresetn(sys_rstn),
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
        .o_disp_select          (w_disp_select_csr),
        .o_soft_reset           (w_soft_reset),
        .i_uart_rx_activity     (w_uart_rx_act),
        .i_uart_tx_activity     (w_uart_tx_act),
        // BTNU = clksel down (toward faster, lower idx); BTND = clksel up (toward slower)
        .i_btn_target_ctr       (w_sel_ctr),
        .i_btn_pickoff_inc_pulse(w_btn_clksel_down),
        .i_btn_pickoff_dec_pulse(w_btn_clksel_up),
        .i_btn_cdc_cycle_pulse  (w_btn_cdc_cycle),
        .i_btn_host_press_pulse (w_btn_press_pulse),
        .i_btn_auto_inc_level   (w_auto_inc_level),
        .i_btn_auto_inc_mask    (w_auto_inc_mask)
    );

    // ----------------------------------------------------------------
    // Per-counter divided clock (sys_clk-derived, runtime PICKOFF)
    //
    // This is the "slow demo" input (CLOCK_SELECT=4). DIV_PICKOFF lives
    // in the upper byte of cfg_divisor.
    // ----------------------------------------------------------------
    logic [NUM_COUNTERS-1:0] w_clk_div_raw;
    logic [NUM_COUNTERS-1:0] w_clk_div_bufg;

    genvar dvi;
    generate
        for (dvi = 0; dvi < NUM_COUNTERS; dvi = dvi + 1) begin : g_div
            clock_divider #(
                .N             (1),
                .PO_WIDTH      (8),
                .COUNTER_WIDTH (32)
            ) u_clkdiv (
                .clk            (sys_clk),
                .rst_n          (sys_rstn),
                .pickoff_points (w_cfg_divisor[dvi][12:8]),
                .divided_clk    (w_clk_div_raw[dvi])
            );
            BUFG u_clkdiv_bufg (.I(w_clk_div_raw[dvi]), .O(w_clk_div_bufg[dvi]));
        end
    endgenerate

    // ----------------------------------------------------------------
    // Per-counter clock mux tree (4× BUFGMUX_CTRL → ctr_clk[i])
    //
    //   Inputs (idx, freq):
    //     0 = clk_mmcm_72m  (72.7 MHz)
    //     1 = clk_mmcm_27m  (27.6 MHz)
    //     2 = clk_mmcm_12m  (11.9 MHz)
    //     3 = clk_mmcm_6m   ( 6.25 MHz)
    //     4 = w_clk_div_bufg[i]  (sys_clk-derived, runtime PICKOFF)
    //
    //   Selector: cfg_divisor[i][2:0] (CLOCK_SELECT). 5..7 fall through
    //   to CLOCK_SELECT=4 (divided clock).
    //
    //   Mux tree (binary, with 8th input = dup of input 4):
    //     L0: M0 = BUFGMUX(72m, 27m), sel = sel[0]
    //         M1 = BUFGMUX(12m, 6m),  sel = sel[0]
    //         M2 = BUFGMUX(div, div), sel = sel[0] (pass-through, BUFG would be cheaper
    //              but we keep symmetry; synth may optimize)
    //         M3 = BUFGMUX(div, div), sel = sel[0]
    //     L1: M4 = BUFGMUX(M0, M1), sel = sel[1]
    //         M5 = BUFGMUX(M2, M3), sel = sel[1]
    //     L2: ctr_clk = BUFGMUX(M4, M5), sel = sel[2]
    //
    //   So sel=000..011 -> MMCM outputs 0..3; sel=100..111 -> divided clock.
    // ----------------------------------------------------------------
    logic [NUM_COUNTERS-1:0] w_ctr_clk;

    genvar mi;
    generate
        for (mi = 0; mi < NUM_COUNTERS; mi = mi + 1) begin : g_clkmux
            logic [2:0] sel;
            assign sel = w_cfg_divisor[mi][2:0];

            logic m0, m1, m2, m3, m4, m5;

            BUFGMUX_CTRL u_m0 (.I0(clk_mmcm_72m), .I1(clk_mmcm_27m), .S(sel[0]), .O(m0));
            BUFGMUX_CTRL u_m1 (.I0(clk_mmcm_12m), .I1(clk_mmcm_6m),  .S(sel[0]), .O(m1));
            BUFGMUX_CTRL u_m2 (.I0(w_clk_div_bufg[mi]), .I1(w_clk_div_bufg[mi]), .S(sel[0]), .O(m2));
            BUFGMUX_CTRL u_m3 (.I0(w_clk_div_bufg[mi]), .I1(w_clk_div_bufg[mi]), .S(sel[0]), .O(m3));

            BUFGMUX_CTRL u_m4 (.I0(m0), .I1(m1), .S(sel[1]), .O(m4));
            BUFGMUX_CTRL u_m5 (.I0(m2), .I1(m3), .S(sel[1]), .O(m5));

            BUFGMUX_CTRL u_mO (.I0(m4), .I1(m5), .S(sel[2]), .O(w_ctr_clk[mi]));
        end
    endgenerate

    // ----------------------------------------------------------------
    // 4 × counter domains (no internal clock divider any more — ctr_clk
    // is driven from the BUFGMUX tree above)
    // ----------------------------------------------------------------
    genvar gi;
    generate
        for (gi = 0; gi < NUM_COUNTERS; gi = gi + 1) begin : g_ctr
            cdc_counter_domain #(
                .VAL_WIDTH   (VAL_WIDTH),
                .PRESS_WIDTH (PRESS_WIDTH),
                .TICK_WIDTH  (32)
            ) u_ctr (
                .sys_clk                  (sys_clk),
                .sys_rstn                 (sys_rstn),
                .ctr_clk                  (w_ctr_clk[gi]),
                .i_cfg_init               (w_cfg_init[gi]),
                .i_cfg_increment          (w_cfg_increment[gi]),
                .i_cfg_load_pulse         (w_cfg_load_pulse[gi]),
                .i_cfg_host_press_pulse   (w_cfg_host_press_pulse[gi]),
                .i_cfg_freeze             (w_cfg_freeze_all),
                .i_cfg_ignore_btn         (w_cfg_ignore_btn),
                .i_cfg_cdc_mode           (w_cfg_cdc_mode[gi]),
                .i_cfg_auto_inc           (w_cfg_auto_inc[gi]),
                .i_btn                    (1'b0),
                .o_value                  (w_status_value[gi]),
                .o_press_count            (w_status_press_count[gi]),
                .o_clk_ticks              (w_status_clk_ticks[gi]),
                .o_alive_event            (w_status_alive_event[gi])
            );
        end
    endgenerate

    // ----------------------------------------------------------------
    // Display
    // ----------------------------------------------------------------
    logic [1:0]            w_disp_select;
    logic [VAL_WIDTH-1:0]  w_disp_value;
    logic [7:0]            w_disp_pickoff;
    logic [2:0]            w_disp_cdc_mode;

    assign w_disp_select  = w_sel_ctr;
    assign w_disp_value   = w_status_value[w_disp_select];
    // Show CLOCK_SELECT (low 4 bits) in the pickoff slot. When in
    // "divided clock" mode (sel == 4), show the DIV_PICKOFF in the upper
    // nibble so the user can see which divided rate they're at.
    always_comb begin
        if (w_cfg_divisor[w_disp_select][2:0] == 3'd4) begin
            w_disp_pickoff = {w_cfg_divisor[w_disp_select][11:8], 4'h4};
        end else begin
            w_disp_pickoff = {4'h0, 1'b0, w_cfg_divisor[w_disp_select][2:0]};
        end
    end
    assign w_disp_cdc_mode = w_cfg_cdc_mode[w_disp_select];

    cdc_demo_seg8 u_seg7 (
        .sys_clk    (sys_clk),
        .sys_rstn   (sys_rstn),
        .i_value    (w_disp_value),
        .i_pickoff  (w_disp_pickoff),
        .i_cdc_mode (w_disp_cdc_mode),
        .o_AN       (AN),
        .o_SEG      (SEG),
        .o_DP       (DP)
    );

    // ----------------------------------------------------------------
    // LEDs (same scheme as v2)
    // ----------------------------------------------------------------
    logic        w_sel_alive_event;
    assign w_sel_alive_event = w_status_alive_event[w_disp_select];

    logic [25:0] r_rx_stretch_cnt, r_tx_stretch_cnt, r_alive_stretch_cnt;
    logic        r_led_rx, r_led_tx, r_led_alive;

    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) begin
            r_rx_stretch_cnt   <= '0;
            r_tx_stretch_cnt   <= '0;
            r_alive_stretch_cnt<= '0;
            r_led_rx           <= 1'b0;
            r_led_tx           <= 1'b0;
            r_led_alive        <= 1'b0;
        end else begin
            if (w_uart_rx_act) begin r_led_rx <= 1'b1; r_rx_stretch_cnt <= '0; end
            else if (r_led_rx) begin
                r_rx_stretch_cnt <= r_rx_stretch_cnt + 1'b1;
                if (r_rx_stretch_cnt == '1) r_led_rx <= 1'b0;
            end
            if (w_uart_tx_act) begin r_led_tx <= 1'b1; r_tx_stretch_cnt <= '0; end
            else if (r_led_tx) begin
                r_tx_stretch_cnt <= r_tx_stretch_cnt + 1'b1;
                if (r_tx_stretch_cnt == '1) r_led_tx <= 1'b0;
            end
            if (w_sel_alive_event) begin r_led_alive <= ~r_led_alive; r_alive_stretch_cnt <= '0; end
            else begin
                r_alive_stretch_cnt <= r_alive_stretch_cnt + 1'b1;
            end
        end
    end

    logic [3:0] w_sel_one_hot;
    always_comb begin
        w_sel_one_hot = 4'h0;
        w_sel_one_hot[w_sel_ctr] = 1'b1;
    end

    assign LED[3:0] = w_sel_one_hot;
    assign LED[4]   = r_led_alive;
    assign LED[5]   = r_led_rx;
    assign LED[6]   = r_led_tx;
    assign LED[7]   = sys_rstn && mmcm_locked;

endmodule


// =====================================================================
// cdc_demo_seg8 — unchanged from v2
// =====================================================================
module cdc_demo_seg8 (
    input  logic        sys_clk,
    input  logic        sys_rstn,
    input  logic [15:0] i_value,
    input  logic [7:0]  i_pickoff,
    input  logic [2:0]  i_cdc_mode,
    output logic [7:0]  o_AN,
    output logic [6:0]  o_SEG,
    output logic        o_DP
);
    logic [16:0] r_refresh_cnt;
    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) r_refresh_cnt <= '0;
        else           r_refresh_cnt <= r_refresh_cnt + 1'b1;
    end

    logic [2:0] w_digit_idx;
    assign w_digit_idx = r_refresh_cnt[16:14];

    always_comb begin
        o_AN = 8'hFF;
        o_AN[w_digit_idx] = 1'b0;
    end

    logic [3:0] w_nibble;
    always_comb begin
        unique case (w_digit_idx)
            3'd0:    w_nibble = i_value[3:0];
            3'd1:    w_nibble = i_value[7:4];
            3'd2:    w_nibble = i_value[11:8];
            3'd3:    w_nibble = i_value[15:12];
            3'd4:    w_nibble = i_pickoff[3:0];
            3'd5:    w_nibble = i_pickoff[7:4];
            3'd6:    w_nibble = {1'b0, i_cdc_mode};
            3'd7:    w_nibble = 4'h0;
            default: w_nibble = 4'h0;
        endcase
    end

    always_comb begin
        unique case (w_nibble)
            4'h0: o_SEG = 7'b1000000;
            4'h1: o_SEG = 7'b1111001;
            4'h2: o_SEG = 7'b0100100;
            4'h3: o_SEG = 7'b0110000;
            4'h4: o_SEG = 7'b0011001;
            4'h5: o_SEG = 7'b0010010;
            4'h6: o_SEG = 7'b0000010;
            4'h7: o_SEG = 7'b1111000;
            4'h8: o_SEG = 7'b0000000;
            4'h9: o_SEG = 7'b0010000;
            4'hA: o_SEG = 7'b0001000;
            4'hB: o_SEG = 7'b0000011;
            4'hC: o_SEG = 7'b1000110;
            4'hD: o_SEG = 7'b0100001;
            4'hE: o_SEG = 7'b0000110;
            4'hF: o_SEG = 7'b0001110;
            default: o_SEG = 7'b1111111;
        endcase
    end
    assign o_DP = 1'b1;
endmodule
