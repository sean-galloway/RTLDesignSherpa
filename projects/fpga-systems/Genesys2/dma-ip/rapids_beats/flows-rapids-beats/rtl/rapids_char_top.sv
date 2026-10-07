// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rapids_char_top
// Purpose: FPGA pin-level top for the RAPIDS beats characterization harness.
//          Exposes the harness control surface (DUT APB config/kick, descriptor
//          RAM loading, and the gen/chk/mem/mon control+status CSRs) to a host
//          over a single 115200-8N1 UART link.
//
// Target board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
//
// Pin mapping (final pins fixed by rapids_char_top.xdc):
//   CLK100MHZ    - 100 MHz system clock (E3)
//   CPU_RESETN   - Center pushbutton  (C12, active-low)
//   UART_TXD_IN  - FTDI -> FPGA RX    (C4)
//   UART_RXD_OUT - FPGA -> FTDI TX    (D4)
//   LED[15:0]    - status bank (see LED map below)
//   7-seg        - PASS ("0123") / FAIL ("9999") result display
//
// -----------------------------------------------------------------------------
// Host interface architecture
// -----------------------------------------------------------------------------
// Unlike stream_char (whose UART/AXIL bridge + CSR live INSIDE the harness),
// rapids_char_harness deliberately exposes s_apb + raw control ports. This top
// therefore owns the host front-end:
//
//   (RELOCATED 2026-09-23) The UART->AXIL master, region decode, harness CSRs,
//   apb4_master and the kick sequencer now live INSIDE rapids_char_harness, so
//   simulating the harness exercises the board's own launch path. This module is
//   pins + reset sync + LED/7-seg only. Former note kept for the address map:
//   uart_axil_bridge  ->  single 32-bit AXIL master (UART "W addr data" /
//                         "R addr" ASCII command protocol)
//        |
//        v
//   AXIL slave decode/router (in this file) splits the master into 3 regions:
//
//   +---------------------------------------------------------------------+
//   | AXIL word-address map (host view; region = addr[19:16])             |
//   +--------------+------------------------------------------------------+
//   | 0x0_0000     | DUT-REG   : APB config/kick window into the DUT      |
//   |              |             (apb4_master cmd/rsp -> harness s_apb).    |
//   |              |             addr[12:0] = APB byte address. Reaches    |
//   |              |             SRC(0x0000)/SNK(0x1000) reg spaces +      |
//   |              |             the channel kick windows inside the DUT.   |
//   | 0x1_0000     | DESC-LOAD : assemble a 256-bit descriptor from 8 x   |
//   |              |             32-bit words, then issue ONE single-beat  |
//   |              |             AXI4 write into the SRC or SNK descriptor |
//   |              |             RAM host-write port.                      |
//   | 0x2_0000     | HARNESS CSR: gen/chk/mem/mon control + status readback|
//   +--------------+------------------------------------------------------+
//
// DUT-REG region (0x0_0000): AXIL read/write -> apb4_master cmd/rsp -> s_apb.
//   The AXIL slave FSM pushes one APB command per access and returns the APB
//   read data / write response over AXIL. apb4_master handles PSEL/PENABLE/
//   PREADY sequencing.
//
// DESC-LOAD region (0x1_0000), byte offsets:
//   0x000..0x01C  DESC_WORD[0..7]  256-bit descriptor holding register.
//                 WORD[0] = desc[31:0] ... WORD[7] = desc[255:224].
//   0x020         DESC_ADDR        target byte address in the descriptor RAM
//                                  (32-bit; upper ADDR_WIDTH bits are zero).
//   0x024         DESC_KICK        write triggers a single-beat AXI4 write of
//                                  the assembled descriptor. data[0]=half
//                                  select: 0 = SRC RAM, 1 = SNK RAM.
//   0x028         DESC_STATUS (rd) [0] = last descriptor write completed OK.
//
// HARNESS CSR region (0x2_0000), byte offsets:
//   Writable:
//   0x000 CTRL           [0] cam_clear (1-cycle pulse)
//   0x010 GEN_CTRL       [0] cfg_gen_start (1-cycle pulse; write 1 to arm one run)
//   0x014 GEN_LFSR_SEED  [31:0]
//   0x018 GEN_NUM_BEATS  [31:0] beats per channel
//   0x01C GEN_BEATS_PPKT [31:0]
//   0x020 GEN_CH_MASK    [NUM_CHANNELS-1:0]  (0 => all channels)
//   0x024 GEN_TDEST      [AXIS_DEST_WIDTH-1:0]
//   0x030 CHK_CTRL       [0] chk_cfg_start (1-cycle pulse)  [1] chk_ready_en (level)
//   0x034 CHK_LFSR_SEED  [31:0]
//   0x040 MEM_CTRL       [0] rd_crc_lfsr_reset pulse  [1] wr_crc_reset pulse
//   0x050 MON_BASE_ADDR  [31:0]
//   0x054 MON_LIMIT_ADDR [31:0]
//   0x058 MON_FLUSH_WM   [15:0]
//   0x060 CH_SEL         [CIW-1:0] selects channel for indexed per-ch reads
//   0x0C0 OBS_CTRL       [0] obs_arm (1-cycle pulse; re-arms the bus meters)
//   Readable:
//   0x000 ID             0x52415031 ("RAP1")
//   0x080 STATUS         [0]mon_irq [1]src_idle [2]snk_idle [3]gen_busy
//                        [4]gen_done [5]data_error [6]rd_mem_busy [7]wr_mem_busy
//   0x084 GEN_BEATS_TOTAL
//   0x088 CHK_BEATS_TOTAL
//   0x08C PKT_COUNT
//   0x090 RD_BEATS_TOTAL
//   0x094 WR_BEATS_TOTAL
//   0x098 SRC_SCHED_ERROR (NUM_CHANNELS bits)
//   0x09C SNK_SCHED_ERROR (NUM_CHANNELS bits)
//   0x0A0 GEN_EXPECTED_CRC[CH_SEL]
//   0x0A4 CHK_ACTUAL_CRC[CH_SEL]
//   0x0A8 RD_CRC_VALUE[CH_SEL]
//   0x0AC WR_CRC_VALUE[CH_SEL]
//   0x0B0 GEN_EXPECTED_CRC_VALID (NUM_CHANNELS bits)
//   0x0B4 CHK_ACTUAL_CRC_VALID   (NUM_CHANNELS bits)
//   0x0B8 RD_CRC_VALID           (NUM_CHANNELS bits)
//   0x0BC WR_CRC_VALID           (NUM_CHANNELS bits)
//   0x100 OBS_RD_PROD  source-read  R-channel productive cycles (frozen window)
//   0x104 OBS_RD_BP    source-read  R-channel backpressure cycles
//   0x108 OBS_RD_STARV source-read  R-channel starvation cycles
//   0x10C OBS_RD_IDLE  source-read  R-channel idle cycles
//   0x110 OBS_WR_PROD  sink-write   W-channel productive cycles
//   0x114 OBS_WR_BP    sink-write   W-channel backpressure cycles
//   0x118 OBS_WR_STARV sink-write   W-channel starvation cycles
//   0x11C OBS_WR_IDLE  sink-write   W-channel idle cycles
//   0x120..0x12C OBS_SIN_{PROD,BP,STARV,IDLE}  AXIS sink ingress (s_axis)
//   0x130..0x13C OBS_SOUT_{PROD,BP,STARV,IDLE} AXIS source egress (m_axis)
//
// Author: sean galloway
// Created: 2026-07-03

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_char_top #(
    // Harness clock. VCO_MHZ=0 (default) BYPASSES the MMCM: aclk = CLK100MHZ
    // direct at 100 MHz. Derate with VCO_MHZ/CLKOUT0_DIVIDE when a build
    // misses timing on the -1 fabric: 750/10 -> 75 MHz, 600/10 -> 60 MHz,
    // 1000/20 -> 50 MHz. MULT_F = VCO_MHZ/100 must stay on the MMCM 0.125
    // grid (VCO multiple of 12.5) inside the Artix-7 -1 range 600..1200.
    parameter int VCO_MHZ        = 0,
    parameter int CLKOUT0_DIVIDE = 10,
    parameter int UART_BAUD      = 115_200,
    // NUM_CHANNELS is overridable so the board target can build a narrower
    // configuration. Default 8 matches the harness/DUT native geometry; the
    // RAPIDS beats DUT (512-bit datapath, 256-bit descriptors) is area-heavy,
    // so a real xc7a100t bitstream will likely override this to 4 (mirroring
    // stream_char's overridable-NUM_CHANNELS approach).
    parameter int NUM_CHANNELS  = 8,
    parameter int DATA_WIDTH    = 512,
    parameter int ADDR_WIDTH    = 64,
    parameter int AXI_ID_WIDTH  = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    // Descriptor fetch is fixed 256-bit end-to-end.
    parameter int DESC_DATA_WIDTH = 256,
    // Extended row/col-major addressing in the DUT. Pinned OFF by default for
    // this characterization build (it is tuned down to close 8-channel timing);
    // override via the RAPIDS_ROW_COL env generic to measure the cost.
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 0,
    // In-core AXI/descriptor monitors + MonBus egress in the DUT, and the GEN_MON
    // cone in rapids_beats_top. Default OFF: this characterization build meters
    // externally (axi_bus_meter) and is tuned to close 8-channel timing. Override
    // via the USE_AXI_MONITORS / GEN_MON env generics -- the same knob names
    // STREAM's builds export -- to measure what the monitors cost.
    parameter int USE_AXI_MONITORS = 0,
    parameter bit GEN_MON          = 1'b0,
    // Shared interface observers on the harness (rapids TASK-001), default OUT.
    parameter bit USE_OBSERVERS       = 1'b0,
    parameter bit OBS_ENABLE_MON_TAPS = 1'b0,
    // Descriptor RAM depth per half. Shrunk from the harness default (2048)
    // to fit the 100T BRAM budget; bump for deeper descriptor chains.
    parameter int SRAM_DEPTH    = 256,   // sink/source data-buffer depth (board-fit; sim default is deeper)
    parameter int DESC_RAM_ENTRIES = 256,
    parameter int APB_ADDR_WIDTH = 13,
    parameter int APB_DATA_WIDTH = 32
) (
    input  logic        CLK100MHZ,       // 100 MHz board clock
    input  logic        CPU_RESETN,      // active-low pushbutton

    input  logic        UART_TXD_IN,     // FTDI->FPGA
    output logic        UART_RXD_OUT,    // FPGA->FTDI

    output logic [15:0] LED,

    // 7-segment display (rightmost 4 digits used; AN[7:4] blanked)
    output logic [7:0]  AN,              // anodes, active low
    output logic        CA, CB, CC, CD,  // cathode segments, active low
    output logic        CE, CF, CG,
    output logic        DP               // decimal point, active low
);

    localparam int CIW          = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1;
    // Derived harness clock frequency (0.125-grid VCO over CLKOUT0_DIVIDE);
    // single source of truth for the UART divisor / LED update / 7-seg scan.
    localparam int FPGA_CLK_HZ  = (VCO_MHZ == 0) ? 100_000_000
                                                 : (VCO_MHZ * 1_000_000) / CLKOUT0_DIVIDE;
    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;
    localparam int DESC_SW       = DESC_DATA_WIDTH / 8;

    // Elaboration guards: an unbuildable clock pair must fail here, not as a
    // silently-wrong tick rate or an MMCM DRC deep in synth.
    initial begin
        if (VCO_MHZ != 0) begin
            if ((VCO_MHZ * 8) % 100 != 0)
                $error("VCO_MHZ=%0d is not a multiple of 12.5: MULT_F=%0f is off the MMCM 0.125 grid",
                       VCO_MHZ, real'(VCO_MHZ) / 100.0);
            if (VCO_MHZ < 600 || VCO_MHZ > 1200)
                $error("VCO_MHZ=%0d outside the Artix-7 -1 MMCM range 600..1200", VCO_MHZ);
            if ((VCO_MHZ * 1_000_000) % CLKOUT0_DIVIDE != 0)
                $error("VCO_MHZ=%0d / CLKOUT0_DIVIDE=%0d is not an integer Hz frequency",
                       VCO_MHZ, CLKOUT0_DIVIDE);
        end
    end

    // =========================================================================
    // Harness clock. BYPASS (default): aclk = CLK100MHZ. Derated: 100 MHz ->
    // IBUF -> MMCM (VCO = 100 MHz x MULT_F) -> BUFG. Vivado auto-derives the
    // MMCM output clock from sys_clk_pin -- no XDC generated-clock needed.
    // =========================================================================
    logic clk_ib, clk_unbuf, aclk, clkfb, clkfb_buf, mmcm_locked;

    generate
    if (VCO_MHZ == 0) begin : g_clk_bypass
        assign aclk        = CLK100MHZ;
        assign mmcm_locked = 1'b1;
    end else begin : g_clk_mmcm
        localparam real CLKFBOUT_MULT = real'(VCO_MHZ) / 100.0;

        IBUF u_ibuf (.I(CLK100MHZ), .O(clk_ib));

        MMCME2_BASE #(
            .BANDWIDTH        ("OPTIMIZED"),
            .CLKIN1_PERIOD    (10.000),               // 100 MHz
            .DIVCLK_DIVIDE    (1),
            .CLKFBOUT_MULT_F  (CLKFBOUT_MULT),        // VCO = 100 MHz * MULT
            .CLKOUT0_DIVIDE_F (CLKOUT0_DIVIDE),
            .CLKOUT0_DUTY_CYCLE(0.500),
            .CLKOUT0_PHASE    (0.000),
            .STARTUP_WAIT     ("FALSE")
        ) u_mmcm (
            .CLKIN1   (clk_ib),
            .CLKFBIN  (clkfb_buf),
            .CLKFBOUT (clkfb),
            .CLKFBOUTB(),
            .CLKOUT0  (clk_unbuf),
            .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
            .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
            .LOCKED   (mmcm_locked),
            .RST      (1'b0),
            .PWRDWN   (1'b0)
        );
        BUFG u_bufg_fb (.I(clkfb),     .O(clkfb_buf));
        BUFG u_bufg_c0 (.I(clk_unbuf), .O(aclk));
    end
    endgenerate

    logic rst_n_raw;
    assign rst_n_raw = CPU_RESETN & mmcm_locked;

    // =========================================================================
    // Reset synchronization -- async assert, sync deassert. ASYNC_REG keeps the
    // flops adjacent for MTBF. False path to r_rst_meta/D is set in the XDC.
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    `ALWAYS_FF_RST(aclk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )

    wire aresetn = r_rst_sync;

    // =========================================================================
    // Harness instance -- ONE rtl harness that owns the whole host path (UART ->
    // AXIL -> CSR + kick sequencer + DUT), mirroring stream_genesys2_top ->
    // stream_harness. This top is now pins + reset sync + LED/7-seg only, so a
    // sim of rapids_char_harness exercises the same launch mechanism the board
    // uses -- the structural gap that was RAPIDS TASK-081.
    // =========================================================================
    logic [15:0] w_led_status;
    logic        w_result_valid;
    logic        w_pass;

    rapids_char_harness #(
        .NUM_CHANNELS     (NUM_CHANNELS),
        .DATA_WIDTH       (DATA_WIDTH),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .APB_ADDR_WIDTH   (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH   (APB_DATA_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .SRAM_DEPTH       (SRAM_DEPTH),
        .DESC_RAM_ENTRIES (DESC_RAM_ENTRIES),
        .DESC_DATA_WIDTH  (DESC_DATA_WIDTH),
        .USE_ROW_COL_MAJOR_ADDRESSING (USE_ROW_COL_MAJOR_ADDRESSING),
        .USE_AXI_MONITORS (USE_AXI_MONITORS),
        .GEN_MON          (GEN_MON),
        .USE_OBSERVERS       (USE_OBSERVERS),
        .OBS_ENABLE_MON_TAPS (OBS_ENABLE_MON_TAPS),
        .FPGA_CLK_HZ      (FPGA_CLK_HZ),
        .UART_BAUD        (UART_BAUD)
    ) u_harness (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .i_uart_rx     (UART_TXD_IN),
        .o_uart_tx     (UART_RXD_OUT),
        .o_led_status  (w_led_status),
        .o_result_valid(w_result_valid),
        .o_pass        (w_pass)
    );


    led_status_driver #(
        .FPGA_CLK_HZ  (FPGA_CLK_HZ),
        .LED_UPDATE_HZ(200),
        .NUM_LEDS     (16),
        .SYNC_STAGES  (3)
    ) u_led_status_driver (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_status(w_led_status),
        .o_led   (LED)
    );

    // =========================================================================
    // 7-segment: "0123" on PASS, "9999" on FAIL, blank until a result latches.
    // =========================================================================
    logic [15:0] w_seg_value;
    logic [6:0]  w_seg_bus;
    assign w_seg_value = w_pass ? 16'h0123 : 16'h9999;

    seven_seg_4digit #(
        .FPGA_CLK_HZ(FPGA_CLK_HZ),
        .REFRESH_HZ (1000)
    ) u_seven_seg (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_hex   (w_seg_value),
        .i_enable(w_result_valid),
        .o_an    (AN),
        .o_seg   (w_seg_bus),
        .o_dp    (DP)
    );

    // Cathode bus split into named board pins: w_seg_bus = {g,f,e,d,c,b,a}
    assign CA = w_seg_bus[0];
    assign CB = w_seg_bus[1];
    assign CC = w_seg_bus[2];
    assign CD = w_seg_bus[3];
    assign CE = w_seg_bus[4];
    assign CF = w_seg_bus[5];
    assign CG = w_seg_bus[6];

endmodule : rapids_char_top
