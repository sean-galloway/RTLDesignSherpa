// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: cdc_demo_top
// Purpose: Board-level top for the CDC counter demo (phase 2).
//
//          Wires together:
//            - uart_axil_bridge        host link (115200 8N1)
//            - cdc_demo_harness        AXIL slave + CSR
//            - 4 × cdc_counter_domain  per-counter w/ 4 CDC modes
//            - button decoder          BTNU/D/L/C → harness pulses
//            - 8-digit 7-seg driver    mode label + pickoff + 16-bit value
//
// Display layout (left → right):
//   AN[7:6] = CDC mode label  ("Pr" / "br" / "S2" / "HS")
//   AN[5:4] = pickoff hex     (00-1F)
//   AN[3:0] = counter value   (16-bit hex)
//
// Controls — see docs/RUNBOOK.md for the full operator guide.

`timescale 1ns / 1ps

module cdc_demo_top (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,     // BTNR / active-low reset

    input  logic        UART_TXD_IN,    // FTDI → FPGA  (pin C4)
    output logic        UART_RXD_OUT,   // FPGA → FTDI  (pin D4)

    input  logic        btnC,           // inject press for selected counter
    input  logic        btnU,           // step pickoff UP   (faster)
    input  logic        btnD,           // step pickoff DOWN (slower)
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

    assign sys_clk = CLK100MHZ;

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
    // Button debounce + edge detect (sys_clk).
    //
    // 4 buttons -> 4 single-cycle "pressed" pulses. A 2-FF synchronizer
    // for the async pin, then a small counter-based debounce (~16 ms
    // at 100 MHz, since 2^21 cycles ≈ 21 ms) so light bounces collapse
    // into one event, then rising-edge detect.
    // ----------------------------------------------------------------
    logic [3:0] btn_raw;
    assign btn_raw = {btnL, btnD, btnU, btnC};

    (* ASYNC_REG = "TRUE" *) logic [3:0] r_btn_sync0;
    (* ASYNC_REG = "TRUE" *) logic [3:0] r_btn_sync1;
    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) begin r_btn_sync0 <= 4'h0; r_btn_sync1 <= 4'h0; end
        else           begin r_btn_sync0 <= btn_raw; r_btn_sync1 <= r_btn_sync0; end
    end

    // 21-bit debounce counter per button. When sampled level differs
    // from stable level for the full counter period, accept the new
    // stable level.
    logic [3:0] r_btn_stable;
    logic [3:0] r_btn_prev;
    logic [20:0] r_debounce_cnt [4];
    logic [3:0]  w_btn_pressed;       // single-cycle rising edge

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

    // Map debounced pulses to harness button-step pulses.
    // {btnL, btnD, btnU, btnC} → indices 3,2,1,0
    logic w_btn_press_pulse;     // BTNC
    logic w_btn_pickoff_dec;     // BTNU (faster → pickoff--)
    logic w_btn_pickoff_inc;     // BTND (slower → pickoff++)
    logic w_btn_cdc_cycle;       // BTNL
    assign w_btn_press_pulse = w_btn_pressed[0];
    assign w_btn_pickoff_dec = w_btn_pressed[1];
    assign w_btn_pickoff_inc = w_btn_pressed[2];
    assign w_btn_cdc_cycle   = w_btn_pressed[3];

    // ----------------------------------------------------------------
    // Switches → harness
    // ----------------------------------------------------------------
    logic [1:0]                 w_sel_ctr;
    logic                       w_auto_inc_level;
    logic [3:0]                 w_auto_inc_mask;

    assign w_sel_ctr        = SW[1:0];
    assign w_auto_inc_level = SW[15];
    // AUTO_INC level applies only to the selected counter (one-hot mask)
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
    logic [1:0]                               w_disp_select_csr;

    cdc_demo_harness #(
        .NUM_COUNTERS (NUM_COUNTERS),
        .VAL_WIDTH    (VAL_WIDTH),
        .PRESS_WIDTH  (PRESS_WIDTH)
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
        // Board-button live controls
        .i_btn_target_ctr       (w_sel_ctr),
        .i_btn_pickoff_inc_pulse(w_btn_pickoff_inc),
        .i_btn_pickoff_dec_pulse(w_btn_pickoff_dec),
        .i_btn_cdc_cycle_pulse  (w_btn_cdc_cycle),
        .i_btn_host_press_pulse (w_btn_press_pulse),
        .i_btn_auto_inc_level   (w_auto_inc_level),
        .i_btn_auto_inc_mask    (w_auto_inc_mask)
    );

    // ----------------------------------------------------------------
    // 4 × counter domains. Buttons are routed via the harness CSR, so
    // each counter's i_btn input is tied to 0 here (the physical
    // button is interpreted by the top-level button decoder above and
    // turned into a HOST_PRESS via the harness for the selected
    // counter only).
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
                .i_cfg_divisor            (w_cfg_divisor[gi]),
                .i_cfg_init               (w_cfg_init[gi]),
                .i_cfg_increment          (w_cfg_increment[gi]),
                .i_cfg_load_pulse         (w_cfg_load_pulse[gi]),
                .i_cfg_host_press_pulse   (w_cfg_host_press_pulse[gi]),
                .i_cfg_freeze             (w_cfg_freeze_all),
                .i_cfg_ignore_btn         (w_cfg_ignore_btn),
                .i_cfg_cdc_mode           (w_cfg_cdc_mode[gi]),
                .i_cfg_auto_inc           (w_cfg_auto_inc[gi]),
                .i_btn                    (1'b0),       // physical-button path off
                .o_value                  (w_status_value[gi]),
                .o_press_count            (w_status_press_count[gi]),
                .o_clk_ticks              (w_status_clk_ticks[gi]),
                .o_alive_event            (w_status_alive_event[gi])
            );
        end
    endgenerate

    // ----------------------------------------------------------------
    // 7-segment display driver — 8 digits.
    //
    // SW[1:0] takes priority over CSR DISP_SELECT (so the board user
    // gets immediate visual feedback when toggling switches).
    // ----------------------------------------------------------------
    logic [1:0]            w_disp_select;
    logic [VAL_WIDTH-1:0]  w_disp_value;
    logic [7:0]            w_disp_pickoff;
    logic [2:0]            w_disp_cdc_mode;

    assign w_disp_select  = w_sel_ctr;   // SW-driven; ignore w_disp_select_csr
    assign w_disp_value   = w_status_value[w_disp_select];
    assign w_disp_pickoff = w_cfg_divisor[w_disp_select][7:0];
    assign w_disp_cdc_mode= w_cfg_cdc_mode[w_disp_select];

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
    // LEDs
    //   [3:0] one-hot selected counter (matches SW[1:0])
    //   [4]   alive pulse from selected counter (toggle, stretched)
    //   [5]   UART RX activity (stretched)
    //   [6]   UART TX activity (stretched)
    //   [7]   system OK
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

    // One-hot selected counter LED bits
    logic [3:0] w_sel_one_hot;
    always_comb begin
        w_sel_one_hot = 4'h0;
        w_sel_one_hot[w_sel_ctr] = 1'b1;
    end

    assign LED[3:0] = w_sel_one_hot;
    assign LED[4]   = r_led_alive;
    assign LED[5]   = r_led_rx;
    assign LED[6]   = r_led_tx;
    assign LED[7]   = sys_rstn;

endmodule


// =====================================================================
// cdc_demo_seg8 — 8-digit 7-segment driver
//
// Time-multiplexed; each digit gets its own AN-low slice of a 8-phase
// round-robin sweep. Digit refresh ~763 Hz per slot at 100 MHz, full
// 8-digit cycle every ~1.05 ms (well above flicker threshold).
//
// Layout:
//   AN[7:6] = mode label chars (left two digits)
//   AN[5:4] = pickoff (2 hex digits)
//   AN[3:0] = value (4 hex digits — low nibble on far right)
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
    // 17-bit refresh counter → top 3 bits index 8 digits, each gets
    // 2^14 sys_clks (~164 µs) of dwell → ~6 kHz per-digit refresh,
    // full sweep ~1.3 ms.
    logic [16:0] r_refresh_cnt;
    always_ff @(posedge sys_clk or negedge sys_rstn) begin
        if (!sys_rstn) r_refresh_cnt <= '0;
        else           r_refresh_cnt <= r_refresh_cnt + 1'b1;
    end

    logic [2:0] w_digit_idx;
    assign w_digit_idx = r_refresh_cnt[16:14];   // 0..7

    // ----- one-hot anode (active-low) -----
    always_comb begin
        o_AN = 8'hFF;
        o_AN[w_digit_idx] = 1'b0;
    end

    // ----- per-digit nibble (mode / pickoff / value all displayed as hex) -----
    //
    // Layout (left = AN[7], right = AN[0]):
    //   AN[7]   high nibble of mode (always 0 today; room for >16 modes)
    //   AN[6]   low  nibble of mode (currently 0–3)
    //   AN[5:4] pickoff (2 hex digits, 00..1F)
    //   AN[3:0] 16-bit counter value (4 hex digits)
    //
    // Showing the mode as a number (rather than letter labels) keeps the
    // decoder trivial and scales to any future mode count up to 0xFF.
    // The legend lives in docs/RUNBOOK.md.
    logic [3:0] w_nibble;
    always_comb begin
        unique case (w_digit_idx)
            3'd0:    w_nibble = i_value[3:0];        // AN[0] = lowest value nibble
            3'd1:    w_nibble = i_value[7:4];
            3'd2:    w_nibble = i_value[11:8];
            3'd3:    w_nibble = i_value[15:12];
            3'd4:    w_nibble = i_pickoff[3:0];
            3'd5:    w_nibble = i_pickoff[7:4];
            3'd6:    w_nibble = {1'b0, i_cdc_mode};   // low nibble of mode (3-bit field)
            3'd7:    w_nibble = 4'h0;                 // high nibble of mode (always 0; reserve for >15 modes)
            default: w_nibble = 4'h0;
        endcase
    end

    // Hex → 7-seg, active-low, {g,f,e,d,c,b,a}
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

    assign o_DP = 1'b1;   // DP off
endmodule
