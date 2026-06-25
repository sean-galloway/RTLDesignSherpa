// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: cdc_demo_harness
// Purpose: AXI4-Lite slave register file for the CDC counter demo.
//          Decodes the CSR map documented in docs/HARNESS.md and fans
//          configuration out to four cdc_counter_domain instances.
//          Per-counter readbacks (value, press_count, ctr_clk_ticks)
//          are already CDC'd into sys_clk by the counter-domain blocks.
//
// Address map (12-bit decode, byte-addressable, 32-bit words):
//   0x000–0x03F  Global (BUILD_ID, STATUS, CTRL, DISP_SELECT, SCRATCH)
//   0x040–0x07F  Counter 0
//   0x080–0x0BF  Counter 1
//   0x0C0–0x0FF  Counter 2
//   0x100–0x13F  Counter 3
//
// All R/W is single-beat. AXIL responses are always OKAY; writes to
// undecoded offsets are silently dropped, reads to undecoded offsets
// return 0.

`timescale 1ns / 1ps

module cdc_demo_harness #(
    parameter int NUM_COUNTERS  = 4,
    parameter int VAL_WIDTH     = 16,
    parameter int PRESS_WIDTH   = 16,
    parameter int PICKOFF_MIN   = 0,
    parameter int PICKOFF_MAX   = 31      // matches CLKDIV_COUNTER_WIDTH-1 in counter_domain
) (
    // ----------------------------------------------------------------
    // Clock + reset (sys_clk domain)
    // ----------------------------------------------------------------
    input  logic                       aclk,
    input  logic                       aresetn,

    // ----------------------------------------------------------------
    // AXI4-Lite slave (32-bit data, 32-bit address)
    // ----------------------------------------------------------------
    input  logic [31:0]                s_axil_awaddr,
    input  logic [2:0]                 s_axil_awprot,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,

    input  logic [31:0]                s_axil_wdata,
    input  logic [3:0]                 s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,

    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic [31:0]                s_axil_araddr,
    input  logic [2:0]                 s_axil_arprot,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,

    output logic [31:0]                s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // ----------------------------------------------------------------
    // To/from each counter domain (sys_clk facing)
    // Per-counter cfg fan-out
    // ----------------------------------------------------------------
    output logic [NUM_COUNTERS-1:0][31:0]          o_cfg_divisor,
    output logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] o_cfg_init,
    output logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] o_cfg_increment,
    output logic [NUM_COUNTERS-1:0]                o_cfg_load_pulse,
    output logic [NUM_COUNTERS-1:0]                o_cfg_host_press_pulse,
    output logic [NUM_COUNTERS-1:0][2:0]           o_cfg_cdc_mode,     // 0=no-cdc, 1=stretch, 2=sync-fifo,
                                                                       // 3=two-phase, 4=four-phase
    output logic [NUM_COUNTERS-1:0]                o_cfg_auto_inc,     // 1=increment every ctr_clk
    output logic                                   o_cfg_freeze_all,
    output logic                                   o_cfg_ignore_btn,

    // Per-counter readback (already in sys_clk after CDC inside the domain)
    input  logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0]   i_status_value,
    input  logic [NUM_COUNTERS-1:0][PRESS_WIDTH-1:0] i_status_press_count,
    input  logic [NUM_COUNTERS-1:0][31:0]            i_status_clk_ticks,
    input  logic [NUM_COUNTERS-1:0]                  i_status_alive_event,

    // ----------------------------------------------------------------
    // Board-side live controls (from cdc_demo_top button decoder).
    // Each pulse is a 1-sys_clk strobe that nudges the stored cfg for
    // the counter identified by i_btn_target_ctr.
    // ----------------------------------------------------------------
    input  logic [1:0]                            i_btn_target_ctr,        // SW[1:0]
    input  logic                                  i_btn_pickoff_inc_pulse, // pickoff++ (slower)
    input  logic                                  i_btn_pickoff_dec_pulse, // pickoff-- (faster)
    input  logic                                  i_btn_cdc_cycle_pulse,   // cycle CDC_MODE
    input  logic                                  i_btn_host_press_pulse,  // inject press (selected ctr)
    input  logic                                  i_btn_auto_inc_level,    // SW[15] level
    input  logic [NUM_COUNTERS-1:0]               i_btn_auto_inc_mask,     // which counters get the level applied

    // Display select to the top
    output logic [1:0]                            o_disp_select,

    // Soft reset request to the top (1 sys_clk pulse)
    output logic                                  o_soft_reset,

    // UART activity flags from the bridge (for STATUS LEDs)
    input  logic                                  i_uart_rx_activity,
    input  logic                                  i_uart_tx_activity
);

    // -----------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------
    localparam logic [31:0] BUILD_ID        = 32'h4344_4331;  // "CDC1"
    localparam int          ADDR_DECODE_W   = 12;             // 4 KB decode

    // Global offsets
    localparam logic [ADDR_DECODE_W-1:0] OFF_BUILD_ID    = 12'h000;
    localparam logic [ADDR_DECODE_W-1:0] OFF_STATUS      = 12'h004;
    localparam logic [ADDR_DECODE_W-1:0] OFF_CTRL        = 12'h008;
    localparam logic [ADDR_DECODE_W-1:0] OFF_DISP_SELECT = 12'h00C;
    localparam logic [ADDR_DECODE_W-1:0] OFF_SCRATCH     = 12'h010;

    // Per-counter offsets (relative to per-counter base = 0x40 + i*0x40)
    localparam logic [5:0] CTR_OFF_DIVISOR    = 6'h00;
    localparam logic [5:0] CTR_OFF_INIT       = 6'h04;
    localparam logic [5:0] CTR_OFF_INCREMENT  = 6'h08;
    localparam logic [5:0] CTR_OFF_CFG_LOAD   = 6'h0C;
    localparam logic [5:0] CTR_OFF_HOST_PRESS = 6'h10;
    localparam logic [5:0] CTR_OFF_VALUE      = 6'h14;
    localparam logic [5:0] CTR_OFF_PRESS_CNT  = 6'h18;
    localparam logic [5:0] CTR_OFF_CLK_TICKS  = 6'h1C;
    localparam logic [5:0] CTR_OFF_CDC_MODE   = 6'h20;
    localparam logic [5:0] CTR_OFF_AUTO_INC   = 6'h24;

    // -----------------------------------------------------------------
    // Storage
    // -----------------------------------------------------------------
    logic [31:0]                        r_scratch;
    logic                               r_freeze_all;
    logic                               r_ignore_btn;
    logic                               r_soft_reset;
    logic [1:0]                         r_disp_select;
    logic                               r_any_csr_written;

    logic [NUM_COUNTERS-1:0][31:0]         r_divisor;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] r_init;
    logic [NUM_COUNTERS-1:0][VAL_WIDTH-1:0] r_increment;

    // 1-bit pulse latches (drive these into o_*_pulse for one sys_clk)
    logic [NUM_COUNTERS-1:0]            r_load_pulse;
    logic [NUM_COUNTERS-1:0]            r_host_press_pulse;
    logic [NUM_COUNTERS-1:0][2:0]       r_cdc_mode;
    logic [NUM_COUNTERS-1:0]            r_auto_inc;

    // STATUS alive flags — toggle a flop every time the alive_event ticks
    // from the counter domain, then OR-reduce inside a small "decay" window
    // so the host sees a recently-active bit (~1 s).
    logic [NUM_COUNTERS-1:0]            r_alive_seen;
    logic [25:0]                        r_alive_decay_cnt;  // ~0.67 s @ 100MHz

    assign o_cfg_divisor          = r_divisor;
    assign o_cfg_init             = r_init;
    assign o_cfg_increment        = r_increment;
    assign o_cfg_load_pulse       = r_load_pulse;
    assign o_cfg_host_press_pulse = r_host_press_pulse;
    assign o_cfg_cdc_mode         = r_cdc_mode;
    assign o_cfg_auto_inc         = r_auto_inc;
    assign o_cfg_freeze_all       = r_freeze_all;
    assign o_cfg_ignore_btn       = r_ignore_btn;
    assign o_disp_select          = r_disp_select;
    assign o_soft_reset           = r_soft_reset;

    // -----------------------------------------------------------------
    // AXIL handshake — simple single-cycle accept on each channel,
    // sequenced through a tiny FSM so write/read addr+data/resp pair
    // up correctly even if the host bursts them.
    // -----------------------------------------------------------------

    // ---- Write channel ----
    logic                       w_aw_hs;
    logic                       w_w_hs;
    logic                       w_b_pending;
    logic [ADDR_DECODE_W-1:0]   r_w_addr;
    logic [31:0]                r_w_data;
    logic [3:0]                 r_w_strb;
    logic                       r_w_have_addr;
    logic                       r_w_have_data;

    assign s_axil_awready = !r_w_have_addr;
    assign s_axil_wready  = !r_w_have_data;
    assign w_aw_hs        = s_axil_awvalid && s_axil_awready;
    assign w_w_hs         = s_axil_wvalid  && s_axil_wready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_w_addr      <= '0;
            r_w_data      <= '0;
            r_w_strb      <= '0;
            r_w_have_addr <= 1'b0;
            r_w_have_data <= 1'b0;
        end else begin
            if (w_aw_hs) begin
                r_w_addr      <= s_axil_awaddr[ADDR_DECODE_W-1:0];
                r_w_have_addr <= 1'b1;
            end
            if (w_w_hs) begin
                r_w_data      <= s_axil_wdata;
                r_w_strb      <= s_axil_wstrb;
                r_w_have_data <= 1'b1;
            end
            // Clear once both arrived and we've issued the write
            if (r_w_have_addr && r_w_have_data && !w_b_pending) begin
                r_w_have_addr <= 1'b0;
                r_w_have_data <= 1'b0;
            end
        end
    end

    // B response: fire one cycle after we've consumed addr+data
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            s_axil_bvalid <= 1'b0;
            s_axil_bresp  <= 2'b00;
            w_b_pending   <= 1'b0;
        end else begin
            if (r_w_have_addr && r_w_have_data && !w_b_pending) begin
                s_axil_bvalid <= 1'b1;
                s_axil_bresp  <= 2'b00;
                w_b_pending   <= 1'b1;
            end else if (s_axil_bvalid && s_axil_bready) begin
                s_axil_bvalid <= 1'b0;
                w_b_pending   <= 1'b0;
            end
        end
    end

    // ---- Read channel ----
    logic                       w_ar_hs;
    logic [ADDR_DECODE_W-1:0]   r_r_addr;
    logic                       r_r_pending;

    assign s_axil_arready = !r_r_pending;
    assign w_ar_hs        = s_axil_arvalid && s_axil_arready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_r_addr     <= '0;
            r_r_pending  <= 1'b0;
            s_axil_rvalid <= 1'b0;
            s_axil_rdata  <= '0;
            s_axil_rresp  <= 2'b00;
        end else begin
            if (w_ar_hs) begin
                r_r_addr    <= s_axil_araddr[ADDR_DECODE_W-1:0];
                r_r_pending <= 1'b1;
            end
            if (r_r_pending && !s_axil_rvalid) begin
                s_axil_rvalid <= 1'b1;
                s_axil_rdata  <= read_value(r_r_addr);
                s_axil_rresp  <= 2'b00;
            end else if (s_axil_rvalid && s_axil_rready) begin
                s_axil_rvalid <= 1'b0;
                r_r_pending   <= 1'b0;
            end
        end
    end

    // -----------------------------------------------------------------
    // Read decode (combinational — driven by latched r_r_addr)
    // -----------------------------------------------------------------
    function automatic logic [31:0] read_value(input logic [ADDR_DECODE_W-1:0] addr);
        logic [31:0] data;
        int          ci;            // counter index, derived from addr[11:6]
        logic [5:0]  off;
        // Each block (global, ctr0..ctrN-1) occupies 64 bytes, so the
        // block index is addr[11:6]:
        //   addr[11:6] = 0       → global  (0x000..0x03F)
        //   addr[11:6] = 1..NUM  → ctr i = addr[11:6] - 1
        //   addr[11:6] >= NUM+1  → reserved (returns 0)
        data = 32'h0;
        if (addr[11:6] == 6'h00) begin
            unique case (addr[5:0])
                OFF_BUILD_ID[5:0]:    data = BUILD_ID;
                OFF_STATUS[5:0]:      data = build_status();
                OFF_CTRL[5:0]:        data = {29'h0, r_ignore_btn, r_freeze_all, 1'b0};
                OFF_DISP_SELECT[5:0]: data = {30'h0, r_disp_select};
                OFF_SCRATCH[5:0]:     data = r_scratch;
                default:              data = 32'h0;
            endcase
        end else if (int'(addr[11:6]) >= 1 && int'(addr[11:6]) <= NUM_COUNTERS) begin
            ci  = int'(addr[11:6]) - 1;
            off = addr[5:0];
            unique case (off)
                CTR_OFF_DIVISOR:    data = r_divisor[ci];
                CTR_OFF_INIT:       data = {{(32-VAL_WIDTH){1'b0}}, r_init[ci]};
                CTR_OFF_INCREMENT:  data = {{(32-VAL_WIDTH){1'b0}}, r_increment[ci]};
                CTR_OFF_VALUE:      data = {{(32-VAL_WIDTH){1'b0}}, i_status_value[ci]};
                CTR_OFF_PRESS_CNT:  data = {16'h0, i_status_press_count[ci]};
                CTR_OFF_CLK_TICKS:  data = i_status_clk_ticks[ci];
                CTR_OFF_CDC_MODE:   data = {29'h0, r_cdc_mode[ci]};
                CTR_OFF_AUTO_INC:   data = {31'h0, r_auto_inc[ci]};
                default:            data = 32'h0;
            endcase
        end
        return data;
    endfunction

    function automatic logic [31:0] build_status();
        logic [31:0] s;
        s = 32'h0;
        s[NUM_COUNTERS-1:0] = r_alive_seen;
        s[4]                = i_uart_rx_activity;
        s[5]                = i_uart_tx_activity;
        s[6]                = r_any_csr_written;
        s[31]               = 1'b1;  // reset deasserted while we're alive to drive this
        return s;
    endfunction

    // -----------------------------------------------------------------
    // Write decode (single-cycle on the cycle after we've taken both
    // addr and data) — drives CSR storage + pulses
    // -----------------------------------------------------------------
    logic w_do_write;
    assign w_do_write = r_w_have_addr && r_w_have_data && !w_b_pending;

    integer wi;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_scratch        <= 32'h0;
            r_freeze_all     <= 1'b0;
            r_ignore_btn     <= 1'b0;
            r_soft_reset     <= 1'b0;
            r_disp_select    <= 2'h0;
            r_any_csr_written<= 1'b0;
            for (wi = 0; wi < NUM_COUNTERS; wi = wi + 1) begin
                r_divisor[wi]          <= default_divisor(wi);
                r_init[wi]             <= '0;
                r_increment[wi]        <= (VAL_WIDTH)'(wi + 1);
                r_load_pulse[wi]       <= 1'b0;
                r_host_press_pulse[wi] <= 1'b0;
                r_cdc_mode[wi]         <= 3'b000; // default: mode 0 = NO_CDC (the broken one — switch to a safe mode via BTNL or CSR)
                r_auto_inc[wi]         <= 1'b0;   // default: button-driven only
            end
        end else begin
            // pulses default-clear each cycle
            r_soft_reset       <= 1'b0;
            r_load_pulse       <= '0;
            r_host_press_pulse <= '0;

            if (w_do_write) begin
                r_any_csr_written <= 1'b1;
                if (r_w_addr[11:6] == 6'h00) begin
                    unique case (r_w_addr[5:0])
                        OFF_CTRL[5:0]: begin
                            r_soft_reset <= r_w_data[0];
                            r_freeze_all <= r_w_data[1];
                            r_ignore_btn <= r_w_data[2];
                        end
                        OFF_DISP_SELECT[5:0]: begin
                            r_disp_select <= r_w_data[1:0];
                        end
                        OFF_SCRATCH[5:0]: begin
                            r_scratch <= r_w_data;
                        end
                        default: ;
                    endcase
                end else if (int'(r_w_addr[11:6]) >= 1 && int'(r_w_addr[11:6]) <= NUM_COUNTERS) begin
                    automatic int ci = int'(r_w_addr[11:6]) - 1;
                    unique case (r_w_addr[5:0])
                        CTR_OFF_DIVISOR: begin
                            // DIVISOR is two packed fields:
                            //   [2:0]   CLOCK_SELECT (0..4 valid; 5..7 → divided clock)
                            //   [12:8]  DIV_PICKOFF for the divided-clock branch
                            // Pass through verbatim; the top-level clock
                            // mux handles out-of-range CLOCK_SELECT
                            // sanely (falls through to divided clock).
                            r_divisor[ci] <= r_w_data;
                        end
                        CTR_OFF_INIT:       r_init[ci]             <= r_w_data[VAL_WIDTH-1:0];
                        CTR_OFF_INCREMENT:  r_increment[ci]        <= r_w_data[VAL_WIDTH-1:0];
                        CTR_OFF_CFG_LOAD:   r_load_pulse[ci]       <= 1'b1;
                        CTR_OFF_HOST_PRESS: r_host_press_pulse[ci] <= 1'b1;
                        CTR_OFF_CDC_MODE:   r_cdc_mode[ci]         <= r_w_data[2:0];
                        CTR_OFF_AUTO_INC:   r_auto_inc[ci]         <= r_w_data[0];
                        default: ;
                    endcase
                end
            end

            // ----------------------------------------------------------
            // Board-button live controls. Buttons step the CLOCK_SELECT
            // field (low 3 bits of DIVISOR) for the selected counter.
            // 0..4 are the valid clock sources (4 MMCM outputs + 1
            // divided clock); we wrap at 5.
            // ----------------------------------------------------------
            if (i_btn_pickoff_inc_pulse) begin
                // "slower" — increase CLOCK_SELECT (toward divided clock)
                r_divisor[i_btn_target_ctr][2:0] <=
                    (r_divisor[i_btn_target_ctr][2:0] == 3'd4) ? 3'd0
                                                               : r_divisor[i_btn_target_ctr][2:0] + 3'd1;
            end
            if (i_btn_pickoff_dec_pulse) begin
                // "faster" — decrease CLOCK_SELECT (toward 72.7 MHz)
                r_divisor[i_btn_target_ctr][2:0] <=
                    (r_divisor[i_btn_target_ctr][2:0] == 3'd0) ? 3'd4
                                                               : r_divisor[i_btn_target_ctr][2:0] - 3'd1;
            end
            if (i_btn_cdc_cycle_pulse) begin
                // Wrap at NUM_CDC_MODES so BTNL cycles 0→1→2→3→4→0.
                r_cdc_mode[i_btn_target_ctr] <=
                    (r_cdc_mode[i_btn_target_ctr] == 3'd4) ? 3'd0
                                                           : r_cdc_mode[i_btn_target_ctr] + 3'd1;
            end
            if (i_btn_host_press_pulse) begin
                r_host_press_pulse[i_btn_target_ctr] <= 1'b1;
            end
            // Auto-inc applies as a level; mask says which counters get it.
            // Mask bit 0 → leave the host's CSR-written r_auto_inc[i] alone.
            for (wi = 0; wi < NUM_COUNTERS; wi = wi + 1) begin
                if (i_btn_auto_inc_mask[wi]) begin
                    r_auto_inc[wi] <= i_btn_auto_inc_level;
                end
            end
        end
    end

    function automatic logic [7:0] clamp_pickoff(input logic [7:0] v);
        // verilator lint_off UNSIGNED
        if (PICKOFF_MIN > 0 && v < PICKOFF_MIN[7:0]) return PICKOFF_MIN[7:0];
        // verilator lint_on UNSIGNED
        else if (v > PICKOFF_MAX[7:0])               return PICKOFF_MAX[7:0];
        else                                         return v;
    endfunction

    function automatic logic [31:0] default_divisor(input int i);
        // Defaults split per-counter so the demo opens with a useful
        // spread:
        //   ctr 0  CLOCK_SELECT=4 (divided), DIV_PICKOFF=23  → ~6 Hz (visible counting)
        //   ctr 1  CLOCK_SELECT=2 (MMCM /67) → 11.9 MHz
        //   ctr 2  CLOCK_SELECT=1 (MMCM /29) → 27.6 MHz
        //   ctr 3  CLOCK_SELECT=0 (MMCM /11) → 72.7 MHz
        // DIVISOR layout:  [12:8] = DIV_PICKOFF, [2:0] = CLOCK_SELECT
        case (i)
            0: return {19'h0, 5'd23, 5'h0, 3'd4};
            1: return 32'd0 | 32'd2;
            2: return 32'd0 | 32'd1;
            3: return 32'd0 | 32'd0;
            default: return 32'd0;
        endcase
    endfunction

    // -----------------------------------------------------------------
    // STATUS alive-decay window: when alive_event[i] pulses, set
    // r_alive_seen[i]; clear all bits every ~0.67 s.
    // -----------------------------------------------------------------
    integer ai;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_alive_seen      <= '0;
            r_alive_decay_cnt <= '0;
        end else begin
            r_alive_decay_cnt <= r_alive_decay_cnt + 1'b1;
            for (ai = 0; ai < NUM_COUNTERS; ai = ai + 1) begin
                if (i_status_alive_event[ai]) r_alive_seen[ai] <= 1'b1;
            end
            if (r_alive_decay_cnt == '1) begin
                r_alive_seen <= '0;
            end
        end
    end

endmodule
