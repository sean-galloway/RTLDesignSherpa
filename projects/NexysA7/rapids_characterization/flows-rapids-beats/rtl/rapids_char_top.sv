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
//   |              |             (apb_master cmd/rsp -> harness s_apb).    |
//   |              |             addr[12:0] = APB byte address. Reaches    |
//   |              |             SRC(0x0000)/SNK(0x1000) reg spaces +      |
//   |              |             apbtodescr kick windows inside the DUT.   |
//   | 0x1_0000     | DESC-LOAD : assemble a 256-bit descriptor from 8 x   |
//   |              |             32-bit words, then issue ONE single-beat  |
//   |              |             AXI4 write into the SRC or SNK descriptor |
//   |              |             RAM host-write port.                      |
//   | 0x2_0000     | HARNESS CSR: gen/chk/mem/mon control + status readback|
//   +--------------+------------------------------------------------------+
//
// DUT-REG region (0x0_0000): AXIL read/write -> apb_master cmd/rsp -> s_apb.
//   The AXIL slave FSM pushes one APB command per access and returns the APB
//   read data / write response over AXIL. apb_master handles PSEL/PENABLE/
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
    parameter int FPGA_CLK_HZ   = 100_000_000,
    parameter int UART_BAUD     = 115_200,
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
    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;
    localparam int DESC_SW       = DESC_DATA_WIDTH / 8;

    // =========================================================================
    // Reset synchronization — async assert, sync deassert. ASYNC_REG keeps the
    // flops adjacent for MTBF. False path to r_rst_meta/D is set in the XDC.
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    always_ff @(posedge CLK100MHZ or negedge CPU_RESETN) begin
        if (!CPU_RESETN) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    end

    wire aclk    = CLK100MHZ;
    wire aresetn = r_rst_sync;

    // =========================================================================
    // UART <-> AXIL master
    // =========================================================================
    logic [31:0] uart_awaddr;
    logic [2:0]  uart_awprot;
    logic        uart_awvalid, uart_awready;
    logic [31:0] uart_wdata;
    logic [3:0]  uart_wstrb;
    logic        uart_wvalid, uart_wready;
    logic [1:0]  uart_bresp;
    logic        uart_bvalid, uart_bready;
    logic [31:0] uart_araddr;
    logic [2:0]  uart_arprot;
    logic        uart_arvalid, uart_arready;
    logic [31:0] uart_rdata;
    logic [1:0]  uart_rresp;
    logic        uart_rvalid, uart_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_uart_rx(UART_TXD_IN),
        .o_uart_tx(UART_RXD_OUT),

        .m_axil_awaddr (uart_awaddr),
        .m_axil_awprot (uart_awprot),
        .m_axil_awvalid(uart_awvalid),
        .m_axil_awready(uart_awready),
        .m_axil_wdata  (uart_wdata),
        .m_axil_wstrb  (uart_wstrb),
        .m_axil_wvalid (uart_wvalid),
        .m_axil_wready (uart_wready),
        .m_axil_bresp  (uart_bresp),
        .m_axil_bvalid (uart_bvalid),
        .m_axil_bready (uart_bready),
        .m_axil_araddr (uart_araddr),
        .m_axil_arprot (uart_arprot),
        .m_axil_arvalid(uart_arvalid),
        .m_axil_arready(uart_arready),
        .m_axil_rdata  (uart_rdata),
        .m_axil_rresp  (uart_rresp),
        .m_axil_rvalid (uart_rvalid),
        .m_axil_rready (uart_rready)
    );

    // =========================================================================
    // Region decode helpers
    // =========================================================================
    localparam logic [3:0] REGION_APB  = 4'h0;
    localparam logic [3:0] REGION_DESC = 4'h1;
    localparam logic [3:0] REGION_CSR  = 4'h2;

    // DESC-LOAD offsets
    localparam logic [11:0] DESC_ADDR_OFF   = 12'h020;
    localparam logic [11:0] DESC_KICK_OFF   = 12'h024;
    localparam logic [11:0] DESC_STATUS_OFF = 12'h028;

    // CSR offsets
    localparam logic [11:0] CSR_CTRL        = 12'h000;
    localparam logic [11:0] CSR_GEN_CTRL    = 12'h010;
    localparam logic [11:0] CSR_GEN_SEED    = 12'h014;
    localparam logic [11:0] CSR_GEN_NBEATS  = 12'h018;
    localparam logic [11:0] CSR_GEN_BPP     = 12'h01C;
    localparam logic [11:0] CSR_GEN_CHMASK  = 12'h020;
    localparam logic [11:0] CSR_GEN_TDEST   = 12'h024;
    localparam logic [11:0] CSR_CHK_CTRL    = 12'h030;
    localparam logic [11:0] CSR_CHK_SEED    = 12'h034;
    localparam logic [11:0] CSR_MEM_CTRL    = 12'h040;
    localparam logic [11:0] CSR_MON_BASE    = 12'h050;
    localparam logic [11:0] CSR_MON_LIMIT   = 12'h054;
    localparam logic [11:0] CSR_MON_FLUSHWM = 12'h058;
    localparam logic [11:0] CSR_CH_SEL      = 12'h060;
    // Atomic launch (stage-all-then-GO): the host programs every CSR + descriptor
    // over the slow UART FIRST, stages the per-channel descriptor kicks as config
    // below, then issues ONE CSR_GO write. GO arms the meter window, (optionally)
    // pulses the AXIS gen start, and starts an on-chip kick-sequencer that replays
    // the LOW/HIGH APB kick writes for every masked channel back-to-back at aclk.
    // This keeps ALL UART latency OUT of the measured window (which is otherwise
    // smeared across seconds and dilutes utilization to ~0%).
    localparam logic [11:0] CSR_KICK_CFG    = 12'h064;  // [0]=half(0 SRC/1 SNK) [1]=start_gen_on_go
    localparam logic [11:0] CSR_KICK_MASK   = 12'h068;  // [NUM_CHANNELS-1:0] kick channel mask
    localparam logic [11:0] CSR_KICK_BASE_LO= 12'h06C;  // descriptor base addr [31:0]
    localparam logic [11:0] CSR_KICK_BASE_HI= 12'h070;  // descriptor base addr [63:32]
    localparam logic [11:0] CSR_KICK_STRIDE = 12'h074;  // per-channel byte stride (base+ch*stride)
    localparam logic [11:0] CSR_GO          = 12'h078;  // [0]=GO (arm+gen+kick, 1-cyc)
    localparam logic [11:0] CSR_OBS_TARGET  = 12'h07C;  // freeze window at N productive beats
    localparam logic [11:0] CSR_OBS_CTRL    = 12'h0C0;  // [0] ARM (1-cyc pulse)

    localparam logic [11:0] CSR_ID          = 12'h000;
    localparam logic [11:0] CSR_STATUS      = 12'h080;
    localparam logic [11:0] CSR_GEN_BEATS_T = 12'h084;
    localparam logic [11:0] CSR_CHK_BEATS_T = 12'h088;
    localparam logic [11:0] CSR_PKT_CNT     = 12'h08C;
    localparam logic [11:0] CSR_RD_BEATS_T  = 12'h090;
    localparam logic [11:0] CSR_WR_BEATS_T  = 12'h094;
    localparam logic [11:0] CSR_SRC_SCHERR  = 12'h098;
    localparam logic [11:0] CSR_SNK_SCHERR  = 12'h09C;
    localparam logic [11:0] CSR_GEN_EXP_CRC = 12'h0A0;
    localparam logic [11:0] CSR_CHK_ACT_CRC = 12'h0A4;
    localparam logic [11:0] CSR_RD_CRC      = 12'h0A8;
    localparam logic [11:0] CSR_WR_CRC      = 12'h0AC;
    localparam logic [11:0] CSR_GEN_EXP_VLD = 12'h0B0;
    localparam logic [11:0] CSR_CHK_ACT_VLD = 12'h0B4;
    localparam logic [11:0] CSR_RD_CRC_VLD  = 12'h0B8;
    localparam logic [11:0] CSR_WR_CRC_VLD  = 12'h0BC;
    // Per-direction AXI bus-meter buckets (axi_bus_meter in the harness).
    localparam logic [11:0] CSR_OBS_RD_PROD = 12'h100;
    localparam logic [11:0] CSR_OBS_RD_BP   = 12'h104;
    localparam logic [11:0] CSR_OBS_RD_STRV = 12'h108;
    localparam logic [11:0] CSR_OBS_RD_IDLE = 12'h10C;
    localparam logic [11:0] CSR_OBS_WR_PROD = 12'h110;
    localparam logic [11:0] CSR_OBS_WR_BP   = 12'h114;
    localparam logic [11:0] CSR_OBS_WR_STRV = 12'h118;
    localparam logic [11:0] CSR_OBS_WR_IDLE = 12'h11C;
    localparam logic [11:0] CSR_OBS_SIN_PROD  = 12'h120;  // AXIS sink ingress
    localparam logic [11:0] CSR_OBS_SIN_BP    = 12'h124;
    localparam logic [11:0] CSR_OBS_SIN_STRV  = 12'h128;
    localparam logic [11:0] CSR_OBS_SIN_IDLE  = 12'h12C;
    localparam logic [11:0] CSR_OBS_SOUT_PROD = 12'h130;  // AXIS source egress
    localparam logic [11:0] CSR_OBS_SOUT_BP   = 12'h134;
    localparam logic [11:0] CSR_OBS_SOUT_STRV = 12'h138;
    localparam logic [11:0] CSR_OBS_SOUT_IDLE = 12'h13C;
    // AXIS-native throughput counters (bytes 64-bit -> LO/HI, packets 32-bit)
    localparam logic [11:0] CSR_OBS_SIN_BYTES_LO  = 12'h140;
    localparam logic [11:0] CSR_OBS_SIN_BYTES_HI  = 12'h144;
    localparam logic [11:0] CSR_OBS_SIN_PKTS      = 12'h148;
    localparam logic [11:0] CSR_OBS_SOUT_BYTES_LO = 12'h14C;
    localparam logic [11:0] CSR_OBS_SOUT_BYTES_HI = 12'h150;
    localparam logic [11:0] CSR_OBS_SOUT_PKTS     = 12'h154;

    // =========================================================================
    // Harness control/status registers (driven by the CSR region)
    // =========================================================================
    logic                       r_cam_clear;          // 1-cycle pulse
    logic                       r_cfg_gen_start;       // 1-cycle pulse (single run per arm)
    logic [31:0]                r_cfg_gen_lfsr_seed;
    logic [31:0]                r_cfg_gen_num_beats;
    logic [31:0]                r_cfg_gen_beats_per_pkt;
    logic [NUM_CHANNELS-1:0]    r_cfg_gen_channel_mask;
    logic [AXIS_DEST_WIDTH-1:0] r_cfg_gen_tdest;
    logic                       r_chk_cfg_start;       // 1-cycle pulse
    logic [31:0]                r_chk_cfg_lfsr_seed;
    logic                       r_chk_ready_en;        // level
    logic                       r_rd_crc_lfsr_reset;   // 1-cycle pulse
    logic                       r_wr_crc_reset;        // 1-cycle pulse
    logic [31:0]                r_cfg_mon_base_addr;
    logic [31:0]                r_cfg_mon_limit_addr;
    logic [15:0]                r_cfg_mon_flush_wm;
    logic [CIW-1:0]             r_ch_sel;

    // Atomic-launch (GO) staging registers + kick-sequencer state
    logic                       r_kick_half;       // 0=SRC, 1=SNK APB kick window
    logic                       r_kick_start_gen;  // GO also pulses cfg_gen_start (sink)
    logic [NUM_CHANNELS-1:0]    r_kick_mask;       // channels to kick on GO
    logic [31:0]                r_kick_base_lo;    // descriptor base addr [31:0]
    logic [31:0]                r_kick_base_hi;    // descriptor base addr [63:32]
    logic [31:0]                r_kick_stride;     // per-channel byte stride
    logic                       r_go;              // 1-cycle GO pulse
    logic [31:0]                r_obs_target;      // freeze window at N productive beats

    // Descriptor-load holding registers
    logic [DESC_DATA_WIDTH-1:0] r_desc_data;
    logic [31:0]                r_desc_addr;
    logic                       r_desc_half;   // 0=SRC, 1=SNK
    logic                       r_desc_ok;     // last write BRESP == OKAY

    // =========================================================================
    // Harness boundary wires
    // =========================================================================
    logic [APB_ADDR_WIDTH-1:0]     s_apb_paddr;
    logic                          s_apb_psel, s_apb_penable, s_apb_pwrite;
    logic [APB_DATA_WIDTH-1:0]     s_apb_pwdata, s_apb_prdata;
    logic [(APB_DATA_WIDTH/8)-1:0] s_apb_pstrb;
    logic                          s_apb_pready, s_apb_pslverr;

    logic                       gen_busy, gen_done;
    logic [NUM_CHANNELS-1:0][31:0] o_gen_expected_crc;
    logic [NUM_CHANNELS-1:0]    o_gen_expected_crc_valid;
    logic [31:0]                o_gen_beat_count_total;
    logic [NUM_CHANNELS-1:0][31:0] o_chk_actual_crc;
    logic [NUM_CHANNELS-1:0]    o_chk_actual_crc_valid;
    logic                       o_data_error;
    logic [31:0]                o_chk_beat_count_total;
    logic [31:0]                o_pkt_count;
    logic [NUM_CHANNELS-1:0][31:0] rd_crc_value;
    logic [NUM_CHANNELS-1:0]    rd_crc_valid;
    logic [31:0]                rd_beat_count_total;
    logic                       rd_mem_busy;
    logic [NUM_CHANNELS-1:0][31:0] wr_crc_value;
    logic [NUM_CHANNELS-1:0]    wr_crc_valid;
    logic [31:0]                wr_beat_count_total;
    logic                       wr_mem_busy;
    // Per-interface bus-meter buckets from the harness (AXI4 rd/wr + AXIS sin/sout).
    logic [31:0]                obs_rd_prod, obs_rd_bp, obs_rd_starv, obs_rd_idle;
    logic [31:0]                obs_wr_prod, obs_wr_bp, obs_wr_starv, obs_wr_idle;
    logic [31:0]                obs_sin_prod, obs_sin_bp, obs_sin_starv, obs_sin_idle;
    logic [31:0]                obs_sout_prod, obs_sout_bp, obs_sout_starv, obs_sout_idle;
    // AXIS-native throughput counters (axis_bus_meter): exact bytes + packets.
    logic [63:0]                obs_sin_bytes, obs_sout_bytes;
    logic [31:0]                obs_sin_packets, obs_sout_packets;
    logic                       r_obs_arm;   // 1-cycle bus-meter re-arm pulse
    logic                       src_system_idle, snk_system_idle;
    logic [NUM_CHANNELS-1:0]    src_sched_error, snk_sched_error;
    logic                       mon_irq;

    // SRC descriptor-RAM host write port
    logic                       desc_src_awvalid, desc_src_awready;
    logic                       desc_src_wvalid,  desc_src_wready;
    logic [AXI_ID_WIDTH-1:0]    desc_src_bid;
    logic [1:0]                 desc_src_bresp;
    logic                       desc_src_bvalid;
    // SNK descriptor-RAM host write port
    logic                       desc_snk_awvalid, desc_snk_awready;
    logic                       desc_snk_wvalid,  desc_snk_wready;
    logic [AXI_ID_WIDTH-1:0]    desc_snk_bid;
    logic [1:0]                 desc_snk_bresp;
    logic                       desc_snk_bvalid;

    // =========================================================================
    // apb_master : AXIL-slave FSM cmd/rsp  ->  harness s_apb
    // =========================================================================
    logic                      apb_cmd_valid, apb_cmd_ready, apb_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0] apb_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0] apb_cmd_pwdata;
    logic [3:0]                apb_cmd_pstrb;
    logic                      apb_rsp_valid, apb_rsp_ready, apb_rsp_pslverr;
    logic [APB_DATA_WIDTH-1:0] apb_rsp_prdata;

    apb_master #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_apb (
        .pclk         (aclk),
        .presetn      (aresetn),
        .m_apb_PSEL   (s_apb_psel),
        .m_apb_PENABLE(s_apb_penable),
        .m_apb_PADDR  (s_apb_paddr),
        .m_apb_PWRITE (s_apb_pwrite),
        .m_apb_PWDATA (s_apb_pwdata),
        .m_apb_PSTRB  (s_apb_pstrb),
        .m_apb_PPROT  (),
        .m_apb_PRDATA (s_apb_prdata),
        .m_apb_PSLVERR(s_apb_pslverr),
        .m_apb_PREADY (s_apb_pready),
        .cmd_valid    (apb_cmd_valid),
        .cmd_ready    (apb_cmd_ready),
        .cmd_pwrite   (apb_cmd_pwrite),
        .cmd_paddr    (apb_cmd_paddr),
        .cmd_pwdata   (apb_cmd_pwdata),
        .cmd_pstrb    (apb_cmd_pstrb),
        .cmd_pprot    (3'b000),
        .rsp_valid    (apb_rsp_valid),
        .rsp_ready    (apb_rsp_ready),
        .rsp_prdata   (apb_rsp_prdata),
        .rsp_pslverr  (apb_rsp_pslverr)
    );

    // =========================================================================
    // AXIL slave — WRITE channel FSM
    // =========================================================================
    typedef enum logic [2:0] {
        WST_AW, WST_W, WST_ACT, WST_APB, WST_DESC, WST_B
    } wstate_t;
    wstate_t r_wstate;

    logic [31:0] r_waddr;
    logic [31:0] r_wdata;
    logic [3:0]  r_wstrb;
    logic        r_apb_cmd_acc_w;
    logic        r_daw_pending, r_dw_pending;

    wire [3:0]  w_wregion = r_waddr[19:16];
    wire [11:0] w_woff    = r_waddr[11:0];

    // Descriptor write half select
    wire w_sel_src = (r_wstate == WST_DESC) && (r_desc_half == 1'b0);
    wire w_sel_snk = (r_wstate == WST_DESC) && (r_desc_half == 1'b1);
    wire w_desc_aw_hs = (w_sel_src && desc_src_awvalid && desc_src_awready)
                     || (w_sel_snk && desc_snk_awvalid && desc_snk_awready);
    wire w_desc_w_hs  = (w_sel_src && desc_src_wvalid  && desc_src_wready)
                     || (w_sel_snk && desc_snk_wvalid  && desc_snk_wready);
    wire w_desc_b_hs  = (w_sel_src && desc_src_bvalid)
                     || (w_sel_snk && desc_snk_bvalid);

    // Write-commit event: register/pulse updates happen on the WST_ACT cycle.
    wire w_csr_we  = (r_wstate == WST_ACT) && (w_wregion == REGION_CSR);
    wire w_desc_we = (r_wstate == WST_ACT) && (w_wregion == REGION_DESC);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wstate        <= WST_AW;
            r_waddr         <= '0;
            r_wdata         <= '0;
            r_wstrb         <= '0;
            r_apb_cmd_acc_w <= 1'b0;
            r_daw_pending   <= 1'b0;
            r_dw_pending    <= 1'b0;
            r_desc_half     <= 1'b0;
            r_desc_ok       <= 1'b0;
        end else begin
            case (r_wstate)
                WST_AW: begin
                    if (uart_awvalid) begin
                        r_waddr  <= uart_awaddr;
                        r_wstate <= WST_W;
                    end
                end
                WST_W: begin
                    if (uart_wvalid) begin
                        r_wdata  <= uart_wdata;
                        r_wstrb  <= uart_wstrb;
                        r_wstate <= WST_ACT;
                    end
                end
                WST_ACT: begin
                    case (w_wregion)
                        REGION_APB: r_wstate <= WST_APB;
                        REGION_DESC: begin
                            if (w_woff == DESC_KICK_OFF) begin
                                r_desc_half   <= r_wdata[0];
                                r_daw_pending <= 1'b1;
                                r_dw_pending  <= 1'b1;
                                r_wstate      <= WST_DESC;
                            end else begin
                                r_wstate <= WST_B;   // holding-reg write
                            end
                        end
                        default: r_wstate <= WST_B;  // CSR write
                    endcase
                end
                WST_APB: begin
                    if (apb_cmd_valid && apb_cmd_ready) r_apb_cmd_acc_w <= 1'b1;
                    if (apb_rsp_valid && apb_rsp_ready) begin
                        r_apb_cmd_acc_w <= 1'b0;
                        r_wstate        <= WST_B;
                    end
                end
                WST_DESC: begin
                    if (w_desc_aw_hs) r_daw_pending <= 1'b0;
                    if (w_desc_w_hs)  r_dw_pending  <= 1'b0;
                    if (w_desc_b_hs) begin
                        r_desc_ok <= (w_sel_src ? (desc_src_bresp == 2'b00)
                                                : (desc_snk_bresp == 2'b00));
                        r_wstate  <= WST_B;
                    end
                end
                WST_B: begin
                    if (uart_bready) r_wstate <= WST_AW;
                end
                default: r_wstate <= WST_AW;
            endcase
        end
    )

    // CSR / DESC holding-register updates + reset-type pulses
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cam_clear             <= 1'b0;
            r_cfg_gen_start         <= 1'b0;
            r_cfg_gen_lfsr_seed     <= '0;
            r_cfg_gen_num_beats     <= '0;
            r_cfg_gen_beats_per_pkt <= '0;
            r_cfg_gen_channel_mask  <= '0;
            r_cfg_gen_tdest         <= '0;
            r_chk_cfg_start         <= 1'b0;
            r_chk_cfg_lfsr_seed     <= '0;
            r_chk_ready_en          <= 1'b0;
            r_rd_crc_lfsr_reset     <= 1'b0;
            r_wr_crc_reset          <= 1'b0;
            r_cfg_mon_base_addr     <= '0;
            r_cfg_mon_limit_addr    <= '0;
            r_cfg_mon_flush_wm      <= '0;
            r_ch_sel                <= '0;
            r_desc_data             <= '0;
            r_desc_addr             <= '0;
            r_obs_arm               <= 1'b0;
            r_kick_half             <= 1'b0;
            r_kick_start_gen        <= 1'b0;
            r_kick_mask             <= '0;
            r_kick_base_lo          <= '0;
            r_kick_base_hi          <= '0;
            r_kick_stride           <= '0;
            r_go                    <= 1'b0;
            r_obs_target            <= '0;
        end else begin
            // Pulses default low; re-asserted for one cycle on a matching write.
            // The gen/chk START bits are ALSO 1-cycle pulses (not held levels):
            // a held start would re-arm the pattern generator every time it
            // returns to IDLE, and over UART the host holds a level for ~1-2 ms
            // (~100k aclk cycles), so the generator would re-run many times per
            // "arm" and desync the sink's per-channel state. Pulsing gives
            // exactly one run per write, matching the cocotb TB's edge-arm.
            // (chk_ready_en stays a level -- it must hold high during a run.)
            r_cam_clear         <= 1'b0;
            r_rd_crc_lfsr_reset <= 1'b0;
            r_wr_crc_reset      <= 1'b0;
            r_cfg_gen_start     <= 1'b0;
            r_chk_cfg_start     <= 1'b0;
            r_obs_arm           <= 1'b0;
            r_go                <= 1'b0;

            if (w_csr_we) begin
                case (w_woff)
                    CSR_CTRL:        r_cam_clear             <= r_wdata[0];
                    CSR_OBS_CTRL:    r_obs_arm               <= r_wdata[0];
                    CSR_GEN_CTRL:    r_cfg_gen_start         <= r_wdata[0];
                    CSR_GEN_SEED:    r_cfg_gen_lfsr_seed     <= r_wdata;
                    CSR_GEN_NBEATS:  r_cfg_gen_num_beats     <= r_wdata;
                    CSR_GEN_BPP:     r_cfg_gen_beats_per_pkt <= r_wdata;
                    CSR_GEN_CHMASK:  r_cfg_gen_channel_mask  <= r_wdata[NUM_CHANNELS-1:0];
                    CSR_GEN_TDEST:   r_cfg_gen_tdest         <= r_wdata[AXIS_DEST_WIDTH-1:0];
                    CSR_CHK_CTRL: begin
                        r_chk_cfg_start <= r_wdata[0];
                        r_chk_ready_en  <= r_wdata[1];
                    end
                    CSR_CHK_SEED:    r_chk_cfg_lfsr_seed     <= r_wdata;
                    CSR_MEM_CTRL: begin
                        r_rd_crc_lfsr_reset <= r_wdata[0];
                        r_wr_crc_reset      <= r_wdata[1];
                    end
                    CSR_MON_BASE:    r_cfg_mon_base_addr     <= r_wdata;
                    CSR_MON_LIMIT:   r_cfg_mon_limit_addr    <= r_wdata;
                    CSR_MON_FLUSHWM: r_cfg_mon_flush_wm      <= r_wdata[15:0];
                    CSR_CH_SEL:      r_ch_sel                <= r_wdata[CIW-1:0];
                    // --- atomic-launch staging (levels, held until next write) ---
                    CSR_KICK_CFG: begin
                        r_kick_half      <= r_wdata[0];
                        r_kick_start_gen <= r_wdata[1];
                    end
                    CSR_KICK_MASK:    r_kick_mask    <= r_wdata[NUM_CHANNELS-1:0];
                    CSR_KICK_BASE_LO: r_kick_base_lo <= r_wdata;
                    CSR_KICK_BASE_HI: r_kick_base_hi <= r_wdata;
                    CSR_KICK_STRIDE:  r_kick_stride  <= r_wdata;
                    CSR_OBS_TARGET:   r_obs_target   <= r_wdata;
                    // --- GO: one write fires meter-arm + gen-start + kicks ---
                    CSR_GO: begin
                        r_go            <= r_wdata[0];
                        r_obs_arm       <= r_wdata[0];                    // arm meter window
                        r_cfg_gen_start <= r_wdata[0] & r_kick_start_gen; // start AXIS gen (sink)
                    end
                    default: ; // no-op
                endcase
            end

            if (w_desc_we) begin
                if (w_woff == DESC_ADDR_OFF) begin
                    r_desc_addr <= r_wdata;
                end else if (w_woff < 12'h020) begin
                    // DESC_WORD[0..7] at byte offsets 0x00..0x1C
                    r_desc_data[ {r_waddr[4:2], 5'b0} +: 32 ] <= r_wdata;
                end
            end
        end
    )

    // =========================================================================
    // AXIL slave — READ channel FSM
    // =========================================================================
    typedef enum logic [1:0] { RST_AR, RST_ACT, RST_APB, RST_R } rstate_t;
    rstate_t r_rstate;

    logic [31:0] r_raddr;
    logic [31:0] r_rdata;
    logic        r_apb_cmd_acc_r;

    wire [3:0]  w_rregion = r_raddr[19:16];
    wire [11:0] w_roff    = r_raddr[11:0];

    // Combinational readback mux (valid once r_raddr is latched in RST_ACT).
    logic [31:0] w_readmux;
    always_comb begin
        w_readmux = 32'hDEAD_BEEF;
        case (w_rregion)
            REGION_CSR: begin
                case (w_roff)
                    CSR_ID:          w_readmux = 32'h5241_5031;  // "RAP1"
                    CSR_STATUS:      w_readmux = {24'b0,
                                        wr_mem_busy, rd_mem_busy, o_data_error,
                                        gen_done, gen_busy,
                                        snk_system_idle, src_system_idle, mon_irq};
                    CSR_GEN_BEATS_T: w_readmux = o_gen_beat_count_total;
                    CSR_CHK_BEATS_T: w_readmux = o_chk_beat_count_total;
                    CSR_PKT_CNT:     w_readmux = o_pkt_count;
                    CSR_RD_BEATS_T:  w_readmux = rd_beat_count_total;
                    CSR_WR_BEATS_T:  w_readmux = wr_beat_count_total;
                    CSR_SRC_SCHERR:  w_readmux = 32'(src_sched_error);
                    CSR_SNK_SCHERR:  w_readmux = 32'(snk_sched_error);
                    CSR_GEN_EXP_CRC: w_readmux = o_gen_expected_crc[r_ch_sel];
                    CSR_CHK_ACT_CRC: w_readmux = o_chk_actual_crc[r_ch_sel];
                    CSR_RD_CRC:      w_readmux = rd_crc_value[r_ch_sel];
                    CSR_WR_CRC:      w_readmux = wr_crc_value[r_ch_sel];
                    CSR_GEN_EXP_VLD: w_readmux = 32'(o_gen_expected_crc_valid);
                    CSR_CHK_ACT_VLD: w_readmux = 32'(o_chk_actual_crc_valid);
                    CSR_RD_CRC_VLD:  w_readmux = 32'(rd_crc_valid);
                    CSR_WR_CRC_VLD:  w_readmux = 32'(wr_crc_valid);
                    CSR_OBS_RD_PROD: w_readmux = obs_rd_prod;
                    CSR_OBS_RD_BP:   w_readmux = obs_rd_bp;
                    CSR_OBS_RD_STRV: w_readmux = obs_rd_starv;
                    CSR_OBS_RD_IDLE: w_readmux = obs_rd_idle;
                    CSR_OBS_WR_PROD: w_readmux = obs_wr_prod;
                    CSR_OBS_WR_BP:   w_readmux = obs_wr_bp;
                    CSR_OBS_WR_STRV: w_readmux = obs_wr_starv;
                    CSR_OBS_WR_IDLE: w_readmux = obs_wr_idle;
                    CSR_OBS_SIN_PROD:  w_readmux = obs_sin_prod;
                    CSR_OBS_SIN_BP:    w_readmux = obs_sin_bp;
                    CSR_OBS_SIN_STRV:  w_readmux = obs_sin_starv;
                    CSR_OBS_SIN_IDLE:  w_readmux = obs_sin_idle;
                    CSR_OBS_SOUT_PROD: w_readmux = obs_sout_prod;
                    CSR_OBS_SOUT_BP:   w_readmux = obs_sout_bp;
                    CSR_OBS_SOUT_STRV: w_readmux = obs_sout_starv;
                    CSR_OBS_SOUT_IDLE: w_readmux = obs_sout_idle;
                    CSR_OBS_SIN_BYTES_LO:  w_readmux = obs_sin_bytes[31:0];
                    CSR_OBS_SIN_BYTES_HI:  w_readmux = obs_sin_bytes[63:32];
                    CSR_OBS_SIN_PKTS:      w_readmux = obs_sin_packets;
                    CSR_OBS_SOUT_BYTES_LO: w_readmux = obs_sout_bytes[31:0];
                    CSR_OBS_SOUT_BYTES_HI: w_readmux = obs_sout_bytes[63:32];
                    CSR_OBS_SOUT_PKTS:     w_readmux = obs_sout_packets;
                    default:         w_readmux = 32'h0;
                endcase
            end
            REGION_DESC: begin
                if (w_roff == DESC_STATUS_OFF)
                    w_readmux = {31'b0, r_desc_ok};
                else if (w_roff == DESC_ADDR_OFF)
                    w_readmux = r_desc_addr;
                else if (w_roff < 12'h020)
                    w_readmux = r_desc_data[ {r_raddr[4:2], 5'b0} +: 32 ];
                else
                    w_readmux = 32'h0;
            end
            default: w_readmux = 32'hDEAD_BEEF;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate        <= RST_AR;
            r_raddr         <= '0;
            r_rdata         <= '0;
            r_apb_cmd_acc_r <= 1'b0;
        end else begin
            case (r_rstate)
                RST_AR: begin
                    if (uart_arvalid) begin
                        r_raddr  <= uart_araddr;
                        r_rstate <= RST_ACT;
                    end
                end
                RST_ACT: begin
                    if (w_rregion == REGION_APB) begin
                        r_rstate <= RST_APB;
                    end else begin
                        r_rdata  <= w_readmux;
                        r_rstate <= RST_R;
                    end
                end
                RST_APB: begin
                    if (apb_cmd_valid && apb_cmd_ready) r_apb_cmd_acc_r <= 1'b1;
                    if (apb_rsp_valid && apb_rsp_ready) begin
                        r_apb_cmd_acc_r <= 1'b0;
                        r_rdata         <= apb_rsp_prdata;
                        r_rstate        <= RST_R;
                    end
                end
                RST_R: begin
                    if (uart_rready) r_rstate <= RST_AR;
                end
                default: r_rstate <= RST_AR;
            endcase
        end
    )

    // =========================================================================
    // AXIL slave handshake outputs
    // =========================================================================
    assign uart_awready = (r_wstate == WST_AW);
    assign uart_wready  = (r_wstate == WST_W);
    assign uart_bvalid  = (r_wstate == WST_B);
    assign uart_bresp   = 2'b00;
    assign uart_arready = (r_rstate == RST_AR);
    assign uart_rvalid  = (r_rstate == RST_R);
    assign uart_rresp   = 2'b00;
    assign uart_rdata   = r_rdata;

    // =========================================================================
    // Atomic-launch kick sequencer: on GO, replay the LOW/HIGH APB descriptor
    // kicks for every masked channel back-to-back at aclk, sourcing the DUT's
    // own apbtodescr kick window (paddr = {half@bit12} + ch*8, +0=LOW/+4=HIGH;
    // pwdata = descriptor addr {base + ch*stride}). This does on-chip in tens of
    // cycles what the host used to do over UART in milliseconds, so the meter
    // window brackets only the transfer.
    // =========================================================================
    typedef enum logic [1:0] { KST_IDLE, KST_SCAN, KST_LOW, KST_HIGH } kstate_t;
    kstate_t     r_kstate;
    logic [7:0]  r_kick_ch;      // current channel (NUM_CHANNELS <= 8)
    logic [63:0] r_kick_addr;    // running descriptor address (base + ch*stride)
    logic        r_kick_acc;     // cmd accepted, awaiting rsp

    wire w_kick_active = (r_kstate != KST_IDLE);
    wire w_kick_cmd    = (r_kstate == KST_LOW) || (r_kstate == KST_HIGH);
    wire [APB_ADDR_WIDTH-1:0] w_kick_base  = r_kick_half ? {1'b1, 12'h000} : '0; // bit[12]=half
    wire [APB_ADDR_WIDTH-1:0] w_kick_paddr =
              w_kick_base
            + (APB_ADDR_WIDTH'(r_kick_ch) << 3)
            + ((r_kstate == KST_HIGH) ? APB_ADDR_WIDTH'('h4) : '0);
    wire [31:0] w_kick_pwdata = (r_kstate == KST_HIGH) ? r_kick_addr[63:32]
                                                       : r_kick_addr[31:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_kstate    <= KST_IDLE;
            r_kick_ch   <= '0;
            r_kick_addr <= '0;
            r_kick_acc  <= 1'b0;
        end else begin
            case (r_kstate)
                KST_IDLE: begin
                    if (r_go) begin
                        r_kick_ch   <= '0;
                        r_kick_addr <= {r_kick_base_hi, r_kick_base_lo};
                        r_kick_acc  <= 1'b0;
                        r_kstate    <= KST_SCAN;
                    end
                end
                KST_SCAN: begin
                    if (r_kick_ch >= 8'(NUM_CHANNELS)) begin
                        r_kstate <= KST_IDLE;
                    end else if (r_kick_mask[r_kick_ch[CIW-1:0]]) begin
                        r_kstate <= KST_LOW;
                    end else begin
                        r_kick_addr <= r_kick_addr + {32'b0, r_kick_stride};
                        r_kick_ch   <= r_kick_ch + 8'd1;
                    end
                end
                KST_LOW: begin
                    if (apb_cmd_valid && apb_cmd_ready) r_kick_acc <= 1'b1;
                    if (apb_rsp_valid && apb_rsp_ready) begin
                        r_kick_acc <= 1'b0;
                        r_kstate   <= KST_HIGH;   // HIGH write triggers the kick
                    end
                end
                KST_HIGH: begin
                    if (apb_cmd_valid && apb_cmd_ready) r_kick_acc <= 1'b1;
                    if (apb_rsp_valid && apb_rsp_ready) begin
                        r_kick_acc  <= 1'b0;
                        r_kick_addr <= r_kick_addr + {32'b0, r_kick_stride};
                        r_kick_ch   <= r_kick_ch + 8'd1;
                        r_kstate    <= KST_SCAN;
                    end
                end
                default: r_kstate <= KST_IDLE;
            endcase
        end
    )

    // =========================================================================
    // APB command/response mux. Host write/read FSMs are mutually exclusive
    // (the UART master issues one transaction at a time); the kick sequencer
    // takes priority but only ever runs when the host is idle (post-GO).
    // =========================================================================
    wire w_apb_active = (r_wstate == WST_APB);
    wire r_apb_active = (r_rstate == RST_APB);
    assign apb_cmd_valid  = w_kick_active
                          ? (w_kick_cmd && !r_kick_acc)
                          : ((w_apb_active && !r_apb_cmd_acc_w)
                              || (r_apb_active && !r_apb_cmd_acc_r));
    assign apb_cmd_pwrite = w_kick_active ? 1'b1 : w_apb_active;   // read active => 0
    assign apb_cmd_paddr  = w_kick_active ? w_kick_paddr
                          : (w_apb_active ? r_waddr[APB_ADDR_WIDTH-1:0]
                                          : r_raddr[APB_ADDR_WIDTH-1:0]);
    assign apb_cmd_pwdata = w_kick_active ? w_kick_pwdata : r_wdata;
    assign apb_cmd_pstrb  = w_kick_active ? 4'hF : (w_apb_active ? r_wstrb : 4'hF);
    assign apb_rsp_ready  = w_kick_active ? 1'b1 : (w_apb_active || r_apb_active);

    // =========================================================================
    // Descriptor-load AXI4 single-beat write payload (shared by SRC/SNK)
    // =========================================================================
    localparam logic [2:0] DESC_AWSIZE = 3'($clog2(DESC_SW));  // 256b => 5
    assign desc_src_awvalid = w_sel_src && r_daw_pending;
    assign desc_src_wvalid  = w_sel_src && r_dw_pending;
    assign desc_snk_awvalid = w_sel_snk && r_daw_pending;
    assign desc_snk_wvalid  = w_sel_snk && r_dw_pending;

    // =========================================================================
    // Harness instance
    // =========================================================================
    rapids_char_harness #(
        .NUM_CHANNELS     (NUM_CHANNELS),
        .DATA_WIDTH       (DATA_WIDTH),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .APB_ADDR_WIDTH   (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH   (APB_DATA_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .SRAM_DEPTH       (SRAM_DEPTH),
        .DESC_RAM_ENTRIES (DESC_RAM_ENTRIES)
    ) u_harness (
        .aclk    (aclk),
        .aresetn (aresetn),
        .cam_clear(r_cam_clear),

        // APB config/kick (from apb_master)
        .s_apb_paddr  (s_apb_paddr),
        .s_apb_psel   (s_apb_psel),
        .s_apb_penable(s_apb_penable),
        .s_apb_pwrite (s_apb_pwrite),
        .s_apb_pwdata (s_apb_pwdata),
        .s_apb_pstrb  (s_apb_pstrb),
        .s_apb_prdata (s_apb_prdata),
        .s_apb_pready (s_apb_pready),
        .s_apb_pslverr(s_apb_pslverr),

        // Monitor egress window config
        .cfg_mon_base_addr      (r_cfg_mon_base_addr),
        .cfg_mon_limit_addr     (r_cfg_mon_limit_addr),
        .cfg_mon_flush_watermark(r_cfg_mon_flush_wm),

        // AXIS pattern generator control/status
        .cfg_gen_start          (r_cfg_gen_start),
        .cfg_gen_lfsr_seed      (r_cfg_gen_lfsr_seed),
        .cfg_gen_num_beats      (r_cfg_gen_num_beats),
        .cfg_gen_beats_per_pkt  (r_cfg_gen_beats_per_pkt),
        .cfg_gen_channel_mask   (r_cfg_gen_channel_mask),
        .cfg_gen_tdest          (r_cfg_gen_tdest),
        .gen_busy               (gen_busy),
        .gen_done               (gen_done),
        .o_gen_expected_crc     (o_gen_expected_crc),
        .o_gen_expected_crc_valid(o_gen_expected_crc_valid),
        .o_gen_beat_count_total (o_gen_beat_count_total),

        // AXIS pattern checker control/status
        .chk_cfg_start          (r_chk_cfg_start),
        .chk_cfg_lfsr_seed      (r_chk_cfg_lfsr_seed),
        .chk_ready_en           (r_chk_ready_en),
        .o_chk_actual_crc       (o_chk_actual_crc),
        .o_chk_actual_crc_valid (o_chk_actual_crc_valid),
        .o_data_error           (o_data_error),
        .o_chk_beat_count_total (o_chk_beat_count_total),
        .o_pkt_count            (o_pkt_count),

        // Source-data memory
        .rd_crc_lfsr_reset      (r_rd_crc_lfsr_reset),
        .rd_crc_value           (rd_crc_value),
        .rd_crc_valid           (rd_crc_valid),
        .rd_beat_count_total    (rd_beat_count_total),
        .rd_mem_busy            (rd_mem_busy),

        // Sink-data memory
        .wr_crc_reset           (r_wr_crc_reset),
        .wr_crc_value           (wr_crc_value),
        .wr_crc_valid           (wr_crc_valid),
        .wr_beat_count_total    (wr_beat_count_total),
        .wr_mem_busy            (wr_mem_busy),

        // Per-interface bus-meter buckets (AXI4 rd/wr + AXIS sin/sout)
        .obs_arm                (r_obs_arm),
        .obs_target             (r_obs_target),
        .obs_active_half        (r_kick_half),   // 1=SNK(wr) 0=SRC(sout) completion meter
        .obs_rd_prod            (obs_rd_prod),
        .obs_rd_bp              (obs_rd_bp),
        .obs_rd_starv           (obs_rd_starv),
        .obs_rd_idle            (obs_rd_idle),
        .obs_wr_prod            (obs_wr_prod),
        .obs_wr_bp              (obs_wr_bp),
        .obs_wr_starv           (obs_wr_starv),
        .obs_wr_idle            (obs_wr_idle),
        .obs_sin_prod           (obs_sin_prod),
        .obs_sin_bp             (obs_sin_bp),
        .obs_sin_starv          (obs_sin_starv),
        .obs_sin_idle           (obs_sin_idle),
        .obs_sout_prod          (obs_sout_prod),
        .obs_sout_bp            (obs_sout_bp),
        .obs_sout_starv         (obs_sout_starv),
        .obs_sout_idle          (obs_sout_idle),
        .obs_sin_bytes          (obs_sin_bytes),
        .obs_sin_packets        (obs_sin_packets),
        .obs_sout_bytes         (obs_sout_bytes),
        .obs_sout_packets       (obs_sout_packets),

        // SOURCE descriptor-RAM host write port
        .desc_src_awid   (AXI_ID_WIDTH'(0)),
        .desc_src_awaddr (ADDR_WIDTH'(r_desc_addr)),
        .desc_src_awlen  (8'h0),
        .desc_src_awsize (DESC_AWSIZE),
        .desc_src_awburst(2'b01),
        .desc_src_awvalid(desc_src_awvalid),
        .desc_src_awready(desc_src_awready),
        .desc_src_wdata  (r_desc_data),
        .desc_src_wstrb  ({DESC_SW{1'b1}}),
        .desc_src_wlast  (1'b1),
        .desc_src_wvalid (desc_src_wvalid),
        .desc_src_wready (desc_src_wready),
        .desc_src_bid    (desc_src_bid),
        .desc_src_bresp  (desc_src_bresp),
        .desc_src_bvalid (desc_src_bvalid),
        .desc_src_bready (1'b1),

        // SINK descriptor-RAM host write port
        .desc_snk_awid   (AXI_ID_WIDTH'(0)),
        .desc_snk_awaddr (ADDR_WIDTH'(r_desc_addr)),
        .desc_snk_awlen  (8'h0),
        .desc_snk_awsize (DESC_AWSIZE),
        .desc_snk_awburst(2'b01),
        .desc_snk_awvalid(desc_snk_awvalid),
        .desc_snk_awready(desc_snk_awready),
        .desc_snk_wdata  (r_desc_data),
        .desc_snk_wstrb  ({DESC_SW{1'b1}}),
        .desc_snk_wlast  (1'b1),
        .desc_snk_wvalid (desc_snk_wvalid),
        .desc_snk_wready (desc_snk_wready),
        .desc_snk_bid    (desc_snk_bid),
        .desc_snk_bresp  (desc_snk_bresp),
        .desc_snk_bvalid (desc_snk_bvalid),
        .desc_snk_bready (1'b1),

        // Status rollups
        .src_system_idle (src_system_idle),
        .src_sched_error (src_sched_error),
        .snk_system_idle (snk_system_idle),
        .snk_sched_error (snk_sched_error),
        .mon_irq         (mon_irq)
    );

    // =========================================================================
    // Board status: heartbeat, sticky error, PASS/FAIL result
    // =========================================================================
    logic [27:0] r_hb;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_hb <= '0;
        else                        r_hb <= r_hb + 28'd1;
    )
    wire w_heartbeat = r_hb[26];   // ~0.75 Hz at 100 MHz

    wire w_any_error = o_data_error | (|src_sched_error) | (|snk_sched_error);
    logic r_err_sticky;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_err_sticky <= 1'b0;
        else if (r_cam_clear)       r_err_sticky <= 1'b0;
        else if (w_any_error)       r_err_sticky <= 1'b1;
    )

    // A "result" is latchable once generation completed and both halves are
    // idle (transfer drained). PASS = no error seen; FAIL = any error.
    wire w_result_valid = gen_done & src_system_idle & snk_system_idle;
    wire w_pass         = w_result_valid & ~r_err_sticky & ~o_data_error;

    // =========================================================================
    // LEDs — driven from a slow (~200 Hz) domain via CDC handshake.
    //   LED[0] mon_irq     LED[1] any_error(sticky)  LED[2] gen_busy
    //   LED[3] heartbeat   LED[4] src_system_idle    LED[5] snk_system_idle
    //   LED[6] gen_done    LED[7] o_data_error       LED[15:8] reserved
    // On a latched result the per-bit view is overridden by a glanceable code:
    //   PASS = 0x0123   FAIL = 0x9999
    // =========================================================================
    localparam logic [15:0] LED_PATTERN_PASS = 16'h0123;
    localparam logic [15:0] LED_PATTERN_FAIL = 16'h9999;

    logic [15:0] w_led_status_idle;
    logic [15:0] w_led_status;
    assign w_led_status_idle = {8'h00,
                                o_data_error,      // [7]
                                gen_done,          // [6]
                                snk_system_idle,   // [5]
                                src_system_idle,   // [4]
                                w_heartbeat,       // [3]
                                gen_busy,          // [2]
                                r_err_sticky,      // [1]
                                mon_irq};          // [0]
    assign w_led_status = w_result_valid
        ? (w_pass ? LED_PATTERN_PASS : LED_PATTERN_FAIL)
        : w_led_status_idle;

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
