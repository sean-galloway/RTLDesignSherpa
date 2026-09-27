// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rapids_char_harness
// Purpose: Synthesizable characterization harness that wraps the split
//          rapids_beats_top DUT with on-chip pattern generators/checkers and
//          memories, mirroring the STREAM characterization harness structure.
//
// Instantiates:
//   - rapids_beats_top          (DUT: split SOURCE + SINK beats DMA)
//   - axis4_master_pattern_gen  (drives DUT s_axis_* : sink-ingress stimulus)
//   - axis4_slave_pattern_check (consumes DUT m_axis_*: source-egress check)
//   - axi4_slave_rd_pattern_gen (backs DUT m_axi_rd_*  : 512b source data source)
//   - axi4_slave_wr_crc_check   (backs DUT m_axi_wr_*  : 512b sink data verify)
//   - sdpram_slave_axi4_axi4 x2 (descriptor RAM per half; DUT reads port A via
//                                {src,snk}_m_axi_desc_*, host writes descriptors
//                                via the exposed write/port-B boundary)
//   - sdpram_slave_axi4_axi4 x2 (control semaphore RAM per half; the ctrlwr
//                                master WRITES and the ctrlrd master READS the
//                                same backing store, so a doorbell write is
//                                observable by a gate read)
//   - always-accept AXIL write responder for m_axil_mon_* (monitor egress never
//                                stalls); s_axil_err_* quiesced.
//
// The cocotb TB drives s_apb_* + the control ports directly. A UART/AXIL bridge
// + CSR + trace observer are intentionally NOT part of this stage; the harness
// is structured so they can be layered on later (a board top would wrap this).
//
// Author: sean galloway
// Created: 2026-07-03

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_char_harness #(
    // ---- DUT geometry (NUM_CHANNELS / DATA_WIDTH overridable) ----
    parameter int NUM_CHANNELS    = 8,
    parameter int DATA_WIDTH      = 512,
    parameter int ADDR_WIDTH      = 64,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int SRAM_DEPTH      = 4096,
    parameter int APB_ADDR_WIDTH  = 13,
    parameter int APB_DATA_WIDTH  = 32,
    // AXIS network-interface parameters (tid carries the channel id)
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,
    // ---- Harness memory sizing ----
    parameter int DESC_RAM_ENTRIES = 2048,  // 2048 x 256b descriptors per half
    parameter int CTRL_RAM_DEPTH   = 256,   // control semaphore words per half
    // RD/WR data "memory" depth. The pattern gen / CRC check are stateless LFSR
    // engines (no backing array), so these are advisory sizing knobs only.
    parameter int RD_MEM_DEPTH     = 4096,
    parameter int WR_MEM_DEPTH     = 4096,
    // ---- Derived ----
    parameter int SW  = DATA_WIDTH / 8,
    parameter int CIW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    // Descriptor fetch is fixed 256-bit end-to-end (DUT src/snk desc rdata).
    parameter int DESC_DATA_WIDTH = 256,
    // Extended row/col-major addressing in the DUT. Pinned OFF by default for
    // this characterization build (it is tuned down to close 8-channel timing);
    // override via the RAPIDS_ROW_COL env generic to measure the cost.
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 0,
    // ---- Host interface (relocated from rapids_char_top) ----
    parameter int FPGA_CLK_HZ     = 100_000_000,
    parameter int UART_BAUD       = 115_200
) (
    input  logic        aclk,
    input  logic        aresetn,

    // UART host interface -- the harness OWNS the host path now, so a
    // sim of this module exercises the same launch mechanism the board
    // uses. That structural gap is what RAPIDS TASK-081 was.
    input  logic        i_uart_rx,
    output logic        o_uart_tx,

    // Board status rollup (the board top owns the LED/7-seg drivers)
    output logic [15:0] o_led_status,
    output logic        o_result_valid,
    output logic        o_pass
);

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;
    localparam int DESC_SW      = DESC_DATA_WIDTH / 8;

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
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),

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
    // The DUT's per-half KICK_ENABLE, inside the APB kick window -- NOT a
    // char_top CSR. The numeric clash with CSR_MEM_CTRL (12'h040) above is
    // coincidental: that one is a char_top CSR, this is an offset into the
    // rapids_beats_top register map (SRC 0x0040 / SNK 0x1040).
    localparam logic [11:0] DUT_KICK_ENABLE = 12'h040;
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
    // apb4_master : AXIL-slave FSM cmd/rsp  ->  harness s_apb
    // =========================================================================
    logic                      apb_cmd_valid, apb_cmd_ready, apb_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0] apb_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0] apb_cmd_pwdata;
    logic [3:0]                apb_cmd_pstrb;
    logic                      apb_rsp_valid, apb_rsp_ready, apb_rsp_pslverr;
    logic [APB_DATA_WIDTH-1:0] apb_rsp_prdata;

    apb4_master #(
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
    // own channel kick window (paddr = {half@bit12} + ch*8, +0=LOW/+4=HIGH;
    // pwdata = descriptor addr {base + ch*stride}). This does on-chip in tens of
    // cycles what the host used to do over UART in milliseconds, so the meter
    // window brackets only the transfer.
    // =========================================================================
    typedef enum logic [2:0] { KST_IDLE, KST_SCAN, KST_LOW, KST_HIGH,
                               KST_KICK } kstate_t;
    kstate_t     r_kstate;
    logic [7:0]  r_kick_ch;      // current channel (NUM_CHANNELS <= 8)
    logic [63:0] r_kick_addr;    // running descriptor address (base + ch*stride)
    logic        r_kick_acc;     // cmd accepted, awaiting rsp

    wire w_kick_active = (r_kstate != KST_IDLE);
    wire w_kick_cmd    = (r_kstate == KST_LOW) || (r_kstate == KST_HIGH)
                      || (r_kstate == KST_KICK);
    wire [APB_ADDR_WIDTH-1:0] w_kick_base  = r_kick_half ? {1'b1, 12'h000} : '0; // bit[12]=half
    wire [APB_ADDR_WIDTH-1:0] w_kick_paddr =
              (r_kstate == KST_KICK)
            ? (w_kick_base + APB_ADDR_WIDTH'(DUT_KICK_ENABLE))
            : ( w_kick_base
              + (APB_ADDR_WIDTH'(r_kick_ch) << 3)
              + ((r_kstate == KST_HIGH) ? APB_ADDR_WIDTH'('h4) : '0));
    // KST_KICK carries the whole staged mask: one write launches every channel
    // on the same cycle, which is the point of the staged-addr refactor.
    wire [31:0] w_kick_pwdata =
              (r_kstate == KST_KICK) ? 32'(r_kick_mask)
            : (r_kstate == KST_HIGH) ? r_kick_addr[63:32]
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
                        // Every masked channel is staged; now LAUNCH. Skip the
                        // write when nothing was staged so GO with mask=0 stays
                        // a no-op rather than pulsing KICK_ENABLE with 0.
                        r_kstate <= (r_kick_mask != '0) ? KST_KICK : KST_IDLE;
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
                        r_kstate   <= KST_HIGH;   // stages addr[63:32]; does NOT kick
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
                // Staging the address pair does NOT kick: rapids_beats_top
                // replaced write-to-kick with staged CHx_DESC_ADDR_{LOW,HIGH}
                // plus a rising-edge-detected KICK_ENABLE. Without this write
                // every channel stays parked -- no descriptor fetch is issued,
                // the scheduler never leaves idle, and the campaign measures
                // nothing. KICK_ENABLE.KICKn is a singlepulse, so it
                // self-clears and needs no follow-up write.
                KST_KICK: begin
                    if (apb_cmd_valid && apb_cmd_ready) r_kick_acc <= 1'b1;
                    if (apb_rsp_valid && apb_rsp_ready) begin
                        r_kick_acc <= 1'b0;
                        r_kstate   <= KST_IDLE;
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
    // Former rapids_char_top -> u_harness port map, now internal. Only the
    // connections whose actual differed from the formal need an alias; every
    // .name(name) pass-through is already declared by the relocated host block.
    // =========================================================================
    logic cam_clear;
    logic [31:0] cfg_mon_base_addr;
    logic [31:0] cfg_mon_limit_addr;
    logic [15:0] cfg_mon_flush_watermark;
    logic cfg_gen_start;
    logic [31:0] cfg_gen_lfsr_seed;
    logic [31:0] cfg_gen_num_beats;
    logic [31:0] cfg_gen_beats_per_pkt;
    logic [NUM_CHANNELS-1:0] cfg_gen_channel_mask;
    logic [AXIS_DEST_WIDTH-1:0] cfg_gen_tdest;
    logic chk_cfg_start;
    logic [31:0] chk_cfg_lfsr_seed;
    logic chk_ready_en;
    logic rd_crc_lfsr_reset;
    logic wr_crc_reset;
    logic obs_arm;
    logic [31:0] obs_target;
    logic [AXI_ID_WIDTH-1:0] desc_src_awid;
    logic [ADDR_WIDTH-1:0] desc_src_awaddr;
    logic [7:0] desc_src_awlen;
    logic [2:0] desc_src_awsize;
    logic [1:0] desc_src_awburst;
    logic [DESC_DATA_WIDTH-1:0] desc_src_wdata;
    logic [(DESC_DATA_WIDTH/8)-1:0] desc_src_wstrb;
    logic desc_src_wlast;
    logic desc_src_bready;
    logic [AXI_ID_WIDTH-1:0] desc_snk_awid;
    logic [ADDR_WIDTH-1:0] desc_snk_awaddr;
    logic [7:0] desc_snk_awlen;
    logic [2:0] desc_snk_awsize;
    logic [1:0] desc_snk_awburst;
    logic [DESC_DATA_WIDTH-1:0] desc_snk_wdata;
    logic [(DESC_DATA_WIDTH/8)-1:0] desc_snk_wstrb;
    logic desc_snk_wlast;
    logic desc_snk_bready;
    assign cam_clear = r_cam_clear;
    logic obs_active_half;
    assign obs_active_half = r_kick_half;
    assign cfg_mon_base_addr = r_cfg_mon_base_addr;
    assign cfg_mon_limit_addr = r_cfg_mon_limit_addr;
    assign cfg_mon_flush_watermark = r_cfg_mon_flush_wm;
    assign cfg_gen_start = r_cfg_gen_start;
    assign cfg_gen_lfsr_seed = r_cfg_gen_lfsr_seed;
    assign cfg_gen_num_beats = r_cfg_gen_num_beats;
    assign cfg_gen_beats_per_pkt = r_cfg_gen_beats_per_pkt;
    assign cfg_gen_channel_mask = r_cfg_gen_channel_mask;
    assign cfg_gen_tdest = r_cfg_gen_tdest;
    assign chk_cfg_start = r_chk_cfg_start;
    assign chk_cfg_lfsr_seed = r_chk_cfg_lfsr_seed;
    assign chk_ready_en = r_chk_ready_en;
    assign rd_crc_lfsr_reset = r_rd_crc_lfsr_reset;
    assign wr_crc_reset = r_wr_crc_reset;
    assign obs_arm = r_obs_arm;
    assign obs_target = r_obs_target;
    assign desc_src_awid = AXI_ID_WIDTH'(0);
    assign desc_src_awaddr = ADDR_WIDTH'(r_desc_addr);
    assign desc_src_awlen = 8'h0;
    assign desc_src_awsize = DESC_AWSIZE;
    assign desc_src_awburst = 2'b01;
    assign desc_src_wdata = r_desc_data;
    assign desc_src_wstrb = {DESC_SW{1'b1}};
    assign desc_src_wlast = 1'b1;
    assign desc_src_bready = 1'b1;
    assign desc_snk_awid = AXI_ID_WIDTH'(0);
    assign desc_snk_awaddr = ADDR_WIDTH'(r_desc_addr);
    assign desc_snk_awlen = 8'h0;
    assign desc_snk_awsize = DESC_AWSIZE;
    assign desc_snk_awburst = 2'b01;
    assign desc_snk_wdata = r_desc_data;
    assign desc_snk_wstrb = {DESC_SW{1'b1}};
    assign desc_snk_wlast = 1'b1;
    assign desc_snk_bready = 1'b1;

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
    // Status bitmap exported as o_led_status. The board top owns the actual
    // led_status_driver (slow ~200 Hz domain + CDC handshake) and the 7-seg.
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


    // Status rollup to the board top, which owns the LED and 7-seg
    // drivers (stream_genesys2_top does exactly this).
    assign o_led_status   = w_led_status;
    assign o_result_valid = w_result_valid;
    assign o_pass         = w_pass;


    //=========================================================================
    // Internal wires between the DUT masters and the harness slaves/memories
    //=========================================================================

    // ---- SOURCE descriptor fetch master (AR/R, 256-bit) ----
    logic [AXI_ID_WIDTH-1:0]   src_desc_arid;
    logic [ADDR_WIDTH-1:0]     src_desc_araddr;
    logic [7:0]                src_desc_arlen;
    logic [2:0]                src_desc_arsize;
    logic [1:0]                src_desc_arburst;
    logic                      src_desc_arlock;
    logic [3:0]                src_desc_arcache;
    logic [2:0]                src_desc_arprot;
    logic [3:0]                src_desc_arqos;
    logic [3:0]                src_desc_arregion;
    logic                      src_desc_arvalid, src_desc_arready;
    logic [AXI_ID_WIDTH-1:0]   src_desc_rid;
    logic [DESC_DATA_WIDTH-1:0] src_desc_rdata;
    logic [1:0]                src_desc_rresp;
    logic                      src_desc_rlast, src_desc_rvalid, src_desc_rready;

    // ---- SINK descriptor fetch master (AR/R, 256-bit) ----
    logic [AXI_ID_WIDTH-1:0]   snk_desc_arid;
    logic [ADDR_WIDTH-1:0]     snk_desc_araddr;
    logic [7:0]                snk_desc_arlen;
    logic [2:0]                snk_desc_arsize;
    logic [1:0]                snk_desc_arburst;
    logic                      snk_desc_arlock;
    logic [3:0]                snk_desc_arcache;
    logic [2:0]                snk_desc_arprot;
    logic [3:0]                snk_desc_arqos;
    logic [3:0]                snk_desc_arregion;
    logic                      snk_desc_arvalid, snk_desc_arready;
    logic [AXI_ID_WIDTH-1:0]   snk_desc_rid;
    logic [DESC_DATA_WIDTH-1:0] snk_desc_rdata;
    logic [1:0]                snk_desc_rresp;
    logic                      snk_desc_rlast, snk_desc_rvalid, snk_desc_rready;

    // ---- SOURCE control read master (AR/R, 32-bit) ----
    logic                      src_crd_arvalid, src_crd_arready;
    logic [ADDR_WIDTH-1:0]     src_crd_araddr;
    logic [7:0]                src_crd_arlen;
    logic [2:0]                src_crd_arsize;
    logic [1:0]                src_crd_arburst;
    logic [AXI_ID_WIDTH-1:0]   src_crd_arid;
    logic                      src_crd_arlock;
    logic [3:0]                src_crd_arcache;
    logic [2:0]                src_crd_arprot;
    logic [3:0]                src_crd_arqos;
    logic [3:0]                src_crd_arregion;
    logic                      src_crd_rvalid, src_crd_rready;
    logic [31:0]               src_crd_rdata;
    logic [1:0]                src_crd_rresp;
    logic                      src_crd_rlast;
    logic [AXI_ID_WIDTH-1:0]   src_crd_rid;

    // ---- SOURCE control write master (AW/W/B, 32-bit) ----
    logic                      src_cwr_awvalid, src_cwr_awready;
    logic [ADDR_WIDTH-1:0]     src_cwr_awaddr;
    logic [7:0]                src_cwr_awlen;
    logic [2:0]                src_cwr_awsize;
    logic [1:0]                src_cwr_awburst;
    logic [AXI_ID_WIDTH-1:0]   src_cwr_awid;
    logic                      src_cwr_awlock;
    logic [3:0]                src_cwr_awcache;
    logic [2:0]                src_cwr_awprot;
    logic [3:0]                src_cwr_awqos;
    logic [3:0]                src_cwr_awregion;
    logic                      src_cwr_wvalid, src_cwr_wready;
    logic [31:0]               src_cwr_wdata;
    logic [3:0]                src_cwr_wstrb;
    logic                      src_cwr_wlast;
    logic                      src_cwr_bvalid, src_cwr_bready;
    logic [AXI_ID_WIDTH-1:0]   src_cwr_bid;
    logic [1:0]                src_cwr_bresp;

    // ---- SINK control read master (AR/R, 32-bit) ----
    logic                      snk_crd_arvalid, snk_crd_arready;
    logic [ADDR_WIDTH-1:0]     snk_crd_araddr;
    logic [7:0]                snk_crd_arlen;
    logic [2:0]                snk_crd_arsize;
    logic [1:0]                snk_crd_arburst;
    logic [AXI_ID_WIDTH-1:0]   snk_crd_arid;
    logic                      snk_crd_arlock;
    logic [3:0]                snk_crd_arcache;
    logic [2:0]                snk_crd_arprot;
    logic [3:0]                snk_crd_arqos;
    logic [3:0]                snk_crd_arregion;
    logic                      snk_crd_rvalid, snk_crd_rready;
    logic [31:0]               snk_crd_rdata;
    logic [1:0]                snk_crd_rresp;
    logic                      snk_crd_rlast;
    logic [AXI_ID_WIDTH-1:0]   snk_crd_rid;

    // ---- SINK control write master (AW/W/B, 32-bit) ----
    logic                      snk_cwr_awvalid, snk_cwr_awready;
    logic [ADDR_WIDTH-1:0]     snk_cwr_awaddr;
    logic [7:0]                snk_cwr_awlen;
    logic [2:0]                snk_cwr_awsize;
    logic [1:0]                snk_cwr_awburst;
    logic [AXI_ID_WIDTH-1:0]   snk_cwr_awid;
    logic                      snk_cwr_awlock;
    logic [3:0]                snk_cwr_awcache;
    logic [2:0]                snk_cwr_awprot;
    logic [3:0]                snk_cwr_awqos;
    logic [3:0]                snk_cwr_awregion;
    logic                      snk_cwr_wvalid, snk_cwr_wready;
    logic [31:0]               snk_cwr_wdata;
    logic [3:0]                snk_cwr_wstrb;
    logic                      snk_cwr_wlast;
    logic                      snk_cwr_bvalid, snk_cwr_bready;
    logic [AXI_ID_WIDTH-1:0]   snk_cwr_bid;
    logic [1:0]                snk_cwr_bresp;

    // ---- SOURCE data read master (AR/R, 512-bit) ----
    logic [AXI_ID_WIDTH-1:0]   rd_arid;
    logic [ADDR_WIDTH-1:0]     rd_araddr;
    logic [7:0]                rd_arlen;
    logic [2:0]                rd_arsize;
    logic [1:0]                rd_arburst;
    logic                      rd_arvalid, rd_arready;
    logic [AXI_ID_WIDTH-1:0]   rd_rid;
    logic [DATA_WIDTH-1:0]     rd_rdata;
    logic [1:0]                rd_rresp;
    logic                      rd_rlast, rd_rvalid, rd_rready;

    // ---- SINK data write master (AW/W/B, 512-bit) ----
    logic [AXI_ID_WIDTH-1:0]   wr_awid;
    logic [ADDR_WIDTH-1:0]     wr_awaddr;
    logic [7:0]                wr_awlen;
    logic [2:0]                wr_awsize;
    logic [1:0]                wr_awburst;
    logic                      wr_awlock;
    logic [3:0]                wr_awcache;
    logic [2:0]                wr_awprot;
    logic [3:0]                wr_awqos;
    logic [3:0]                wr_awregion;
    logic                      wr_awvalid, wr_awready;
    logic [DATA_WIDTH-1:0]     wr_wdata;
    logic [SW-1:0]             wr_wstrb;
    logic                      wr_wlast, wr_wvalid, wr_wready;
    logic [AXI_ID_WIDTH-1:0]   wr_bid;
    logic [1:0]                wr_bresp;
    logic                      wr_bvalid, wr_bready;

    // ---- AXIS ingress (harness gen -> DUT s_axis) ----
    logic [DATA_WIDTH-1:0]     s_axis_tdata;
    logic [SW-1:0]             s_axis_tstrb;
    logic                      s_axis_tlast;
    logic [AXIS_ID_WIDTH-1:0]  s_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] s_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] s_axis_tuser;
    logic                      s_axis_tvalid, s_axis_tready;

    // ---- AXIS egress (DUT m_axis -> harness check) ----
    logic [DATA_WIDTH-1:0]     m_axis_tdata;
    logic [SW-1:0]             m_axis_tstrb;
    logic                      m_axis_tlast;
    logic [AXIS_ID_WIDTH-1:0]  m_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] m_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] m_axis_tuser;
    logic                      m_axis_tvalid, m_axis_tready;

    // ---- MonBus AXIL capture master (DUT -> always-accept responder) ----
    logic                      mon_awvalid, mon_awready;
    logic [31:0]               mon_awaddr;
    logic [2:0]                mon_awprot;
    logic                      mon_wvalid, mon_wready;
    logic [63:0]               mon_wdata;
    logic [7:0]                mon_wstrb;
    logic                      mon_bvalid, mon_bready;
    logic [1:0]                mon_bresp;

    //=========================================================================
    // DUT: rapids_beats_top
    //=========================================================================
    rapids_beats_top #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .DATA_WIDTH     (DATA_WIDTH),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .SRAM_DEPTH     (SRAM_DEPTH),
        .APB_ADDR_WIDTH (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH (APB_DATA_WIDTH),
        .AXIS_ID_WIDTH  (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH),
        // Compile the in-core AXI/descriptor monitors + MonBus egress OUT: this
        // char build meters utilization externally (axi_bus_meter), so the DUT
        // monitors are dead weight -- removing them reclaims LUTs and closes
        // 8-channel timing (mirrors stream_char's USE_AXI_MONITORS=0).
        .USE_AXI_MONITORS(0),
        .GEN_MON         (1'b0),
        // Extended addressing compiled OUT. rapids_beats_top defaults this to 1
        // as of the default flip, but this char build is tuned down to close
        // 8-channel timing and meters externally; inheriting the new default
        // would silently add two stream_run_addr_gen instances per channel plus
        // the second descriptor-fetch path. Pin it here so the board flow's
        // area and WNS are unchanged by that flip.
        .USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING)
    ) u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),
        .cam_clear(cam_clear),

        // APB
        .s_apb_paddr   (s_apb_paddr),
        .s_apb_psel    (s_apb_psel),
        .s_apb_penable (s_apb_penable),
        .s_apb_pwrite  (s_apb_pwrite),
        .s_apb_pwdata  (s_apb_pwdata),
        .s_apb_pstrb   (s_apb_pstrb),
        .s_apb_prdata  (s_apb_prdata),
        .s_apb_pready  (s_apb_pready),
        .s_apb_pslverr (s_apb_pslverr),

        // SOURCE descriptor master
        .src_m_axi_desc_arid    (src_desc_arid),
        .src_m_axi_desc_araddr  (src_desc_araddr),
        .src_m_axi_desc_arlen   (src_desc_arlen),
        .src_m_axi_desc_arsize  (src_desc_arsize),
        .src_m_axi_desc_arburst (src_desc_arburst),
        .src_m_axi_desc_arlock  (src_desc_arlock),
        .src_m_axi_desc_arcache (src_desc_arcache),
        .src_m_axi_desc_arprot  (src_desc_arprot),
        .src_m_axi_desc_arqos   (src_desc_arqos),
        .src_m_axi_desc_arregion(src_desc_arregion),
        .src_m_axi_desc_arvalid (src_desc_arvalid),
        .src_m_axi_desc_arready (src_desc_arready),
        .src_m_axi_desc_rid     (src_desc_rid),
        .src_m_axi_desc_rdata   (src_desc_rdata),
        .src_m_axi_desc_rresp   (src_desc_rresp),
        .src_m_axi_desc_rlast   (src_desc_rlast),
        .src_m_axi_desc_rvalid  (src_desc_rvalid),
        .src_m_axi_desc_rready  (src_desc_rready),

        // SINK descriptor master
        .snk_m_axi_desc_arid    (snk_desc_arid),
        .snk_m_axi_desc_araddr  (snk_desc_araddr),
        .snk_m_axi_desc_arlen   (snk_desc_arlen),
        .snk_m_axi_desc_arsize  (snk_desc_arsize),
        .snk_m_axi_desc_arburst (snk_desc_arburst),
        .snk_m_axi_desc_arlock  (snk_desc_arlock),
        .snk_m_axi_desc_arcache (snk_desc_arcache),
        .snk_m_axi_desc_arprot  (snk_desc_arprot),
        .snk_m_axi_desc_arqos   (snk_desc_arqos),
        .snk_m_axi_desc_arregion(snk_desc_arregion),
        .snk_m_axi_desc_arvalid (snk_desc_arvalid),
        .snk_m_axi_desc_arready (snk_desc_arready),
        .snk_m_axi_desc_rid     (snk_desc_rid),
        .snk_m_axi_desc_rdata   (snk_desc_rdata),
        .snk_m_axi_desc_rresp   (snk_desc_rresp),
        .snk_m_axi_desc_rlast   (snk_desc_rlast),
        .snk_m_axi_desc_rvalid  (snk_desc_rvalid),
        .snk_m_axi_desc_rready  (snk_desc_rready),

        // SOURCE control read master
        .src_m_axi_ctrlrd_arvalid (src_crd_arvalid),
        .src_m_axi_ctrlrd_arready (src_crd_arready),
        .src_m_axi_ctrlrd_araddr  (src_crd_araddr),
        .src_m_axi_ctrlrd_arlen   (src_crd_arlen),
        .src_m_axi_ctrlrd_arsize  (src_crd_arsize),
        .src_m_axi_ctrlrd_arburst (src_crd_arburst),
        .src_m_axi_ctrlrd_arid    (src_crd_arid),
        .src_m_axi_ctrlrd_arlock  (src_crd_arlock),
        .src_m_axi_ctrlrd_arcache (src_crd_arcache),
        .src_m_axi_ctrlrd_arprot  (src_crd_arprot),
        .src_m_axi_ctrlrd_arqos   (src_crd_arqos),
        .src_m_axi_ctrlrd_arregion(src_crd_arregion),
        .src_m_axi_ctrlrd_rvalid  (src_crd_rvalid),
        .src_m_axi_ctrlrd_rready  (src_crd_rready),
        .src_m_axi_ctrlrd_rdata   (src_crd_rdata),
        .src_m_axi_ctrlrd_rresp   (src_crd_rresp),
        .src_m_axi_ctrlrd_rlast   (src_crd_rlast),
        .src_m_axi_ctrlrd_rid     (src_crd_rid),

        // SOURCE control write master
        .src_m_axi_ctrlwr_awvalid (src_cwr_awvalid),
        .src_m_axi_ctrlwr_awready (src_cwr_awready),
        .src_m_axi_ctrlwr_awaddr  (src_cwr_awaddr),
        .src_m_axi_ctrlwr_awlen   (src_cwr_awlen),
        .src_m_axi_ctrlwr_awsize  (src_cwr_awsize),
        .src_m_axi_ctrlwr_awburst (src_cwr_awburst),
        .src_m_axi_ctrlwr_awid    (src_cwr_awid),
        .src_m_axi_ctrlwr_awlock  (src_cwr_awlock),
        .src_m_axi_ctrlwr_awcache (src_cwr_awcache),
        .src_m_axi_ctrlwr_awprot  (src_cwr_awprot),
        .src_m_axi_ctrlwr_awqos   (src_cwr_awqos),
        .src_m_axi_ctrlwr_awregion(src_cwr_awregion),
        .src_m_axi_ctrlwr_wvalid  (src_cwr_wvalid),
        .src_m_axi_ctrlwr_wready  (src_cwr_wready),
        .src_m_axi_ctrlwr_wdata   (src_cwr_wdata),
        .src_m_axi_ctrlwr_wstrb   (src_cwr_wstrb),
        .src_m_axi_ctrlwr_wlast   (src_cwr_wlast),
        .src_m_axi_ctrlwr_bvalid  (src_cwr_bvalid),
        .src_m_axi_ctrlwr_bready  (src_cwr_bready),
        .src_m_axi_ctrlwr_bid     (src_cwr_bid),
        .src_m_axi_ctrlwr_bresp   (src_cwr_bresp),

        // SINK control read master
        .snk_m_axi_ctrlrd_arvalid (snk_crd_arvalid),
        .snk_m_axi_ctrlrd_arready (snk_crd_arready),
        .snk_m_axi_ctrlrd_araddr  (snk_crd_araddr),
        .snk_m_axi_ctrlrd_arlen   (snk_crd_arlen),
        .snk_m_axi_ctrlrd_arsize  (snk_crd_arsize),
        .snk_m_axi_ctrlrd_arburst (snk_crd_arburst),
        .snk_m_axi_ctrlrd_arid    (snk_crd_arid),
        .snk_m_axi_ctrlrd_arlock  (snk_crd_arlock),
        .snk_m_axi_ctrlrd_arcache (snk_crd_arcache),
        .snk_m_axi_ctrlrd_arprot  (snk_crd_arprot),
        .snk_m_axi_ctrlrd_arqos   (snk_crd_arqos),
        .snk_m_axi_ctrlrd_arregion(snk_crd_arregion),
        .snk_m_axi_ctrlrd_rvalid  (snk_crd_rvalid),
        .snk_m_axi_ctrlrd_rready  (snk_crd_rready),
        .snk_m_axi_ctrlrd_rdata   (snk_crd_rdata),
        .snk_m_axi_ctrlrd_rresp   (snk_crd_rresp),
        .snk_m_axi_ctrlrd_rlast   (snk_crd_rlast),
        .snk_m_axi_ctrlrd_rid     (snk_crd_rid),

        // SINK control write master
        .snk_m_axi_ctrlwr_awvalid (snk_cwr_awvalid),
        .snk_m_axi_ctrlwr_awready (snk_cwr_awready),
        .snk_m_axi_ctrlwr_awaddr  (snk_cwr_awaddr),
        .snk_m_axi_ctrlwr_awlen   (snk_cwr_awlen),
        .snk_m_axi_ctrlwr_awsize  (snk_cwr_awsize),
        .snk_m_axi_ctrlwr_awburst (snk_cwr_awburst),
        .snk_m_axi_ctrlwr_awid    (snk_cwr_awid),
        .snk_m_axi_ctrlwr_awlock  (snk_cwr_awlock),
        .snk_m_axi_ctrlwr_awcache (snk_cwr_awcache),
        .snk_m_axi_ctrlwr_awprot  (snk_cwr_awprot),
        .snk_m_axi_ctrlwr_awqos   (snk_cwr_awqos),
        .snk_m_axi_ctrlwr_awregion(snk_cwr_awregion),
        .snk_m_axi_ctrlwr_wvalid  (snk_cwr_wvalid),
        .snk_m_axi_ctrlwr_wready  (snk_cwr_wready),
        .snk_m_axi_ctrlwr_wdata   (snk_cwr_wdata),
        .snk_m_axi_ctrlwr_wstrb   (snk_cwr_wstrb),
        .snk_m_axi_ctrlwr_wlast   (snk_cwr_wlast),
        .snk_m_axi_ctrlwr_bvalid  (snk_cwr_bvalid),
        .snk_m_axi_ctrlwr_bready  (snk_cwr_bready),
        .snk_m_axi_ctrlwr_bid     (snk_cwr_bid),
        .snk_m_axi_ctrlwr_bresp   (snk_cwr_bresp),

        // SOURCE data read master
        .m_axi_rd_arid   (rd_arid),
        .m_axi_rd_araddr (rd_araddr),
        .m_axi_rd_arlen  (rd_arlen),
        .m_axi_rd_arsize (rd_arsize),
        .m_axi_rd_arburst(rd_arburst),
        .m_axi_rd_arvalid(rd_arvalid),
        .m_axi_rd_arready(rd_arready),
        .m_axi_rd_rid    (rd_rid),
        .m_axi_rd_rdata  (rd_rdata),
        .m_axi_rd_rresp  (rd_rresp),
        .m_axi_rd_rlast  (rd_rlast),
        .m_axi_rd_rvalid (rd_rvalid),
        .m_axi_rd_rready (rd_rready),

        // SINK data write master
        .m_axi_wr_awid   (wr_awid),
        .m_axi_wr_awaddr (wr_awaddr),
        .m_axi_wr_awlen  (wr_awlen),
        .m_axi_wr_awsize (wr_awsize),
        .m_axi_wr_awburst(wr_awburst),
        .m_axi_wr_awlock (wr_awlock),
        .m_axi_wr_awcache(wr_awcache),
        .m_axi_wr_awprot (wr_awprot),
        .m_axi_wr_awqos  (wr_awqos),
        .m_axi_wr_awregion(wr_awregion),
        .m_axi_wr_awvalid(wr_awvalid),
        .m_axi_wr_awready(wr_awready),
        .m_axi_wr_wdata  (wr_wdata),
        .m_axi_wr_wstrb  (wr_wstrb),
        .m_axi_wr_wlast  (wr_wlast),
        .m_axi_wr_wvalid (wr_wvalid),
        .m_axi_wr_wready (wr_wready),
        .m_axi_wr_bid    (wr_bid),
        .m_axi_wr_bresp  (wr_bresp),
        .m_axi_wr_bvalid (wr_bvalid),
        .m_axi_wr_bready (wr_bready),

        // AXIS ingress (sink)
        .s_axis_tdata  (s_axis_tdata),
        .s_axis_tstrb  (s_axis_tstrb),
        .s_axis_tlast  (s_axis_tlast),
        .s_axis_tid    (s_axis_tid),
        .s_axis_tdest  (s_axis_tdest),
        .s_axis_tuser  (s_axis_tuser),
        .s_axis_tvalid (s_axis_tvalid),
        .s_axis_tready (s_axis_tready),

        // AXIS egress (source)
        .m_axis_tdata  (m_axis_tdata),
        .m_axis_tstrb  (m_axis_tstrb),
        .m_axis_tlast  (m_axis_tlast),
        .m_axis_tid    (m_axis_tid),
        .m_axis_tdest  (m_axis_tdest),
        .m_axis_tuser  (m_axis_tuser),
        .m_axis_tvalid (m_axis_tvalid),
        .m_axis_tready (m_axis_tready),

        // MonBus AXIL error-drain slave (quiesced: no external reader)
        .s_axil_err_arvalid (1'b0),
        .s_axil_err_arready (),
        .s_axil_err_araddr  (32'h0),
        .s_axil_err_arprot  (3'h0),
        .s_axil_err_rvalid  (),
        .s_axil_err_rready  (1'b1),
        .s_axil_err_rdata   (),
        .s_axil_err_rresp   (),

        // MonBus AXIL capture master (always-accept responder below)
        .m_axil_mon_awvalid (mon_awvalid),
        .m_axil_mon_awready (mon_awready),
        .m_axil_mon_awaddr  (mon_awaddr),
        .m_axil_mon_awprot  (mon_awprot),
        .m_axil_mon_wvalid  (mon_wvalid),
        .m_axil_mon_wready  (mon_wready),
        .m_axil_mon_wdata   (mon_wdata),
        .m_axil_mon_wstrb   (mon_wstrb),
        .m_axil_mon_bvalid  (mon_bvalid),
        .m_axil_mon_bready  (mon_bready),
        .m_axil_mon_bresp   (mon_bresp),

        .mon_irq (mon_irq),

        .cfg_mon_base_addr       (cfg_mon_base_addr),
        .cfg_mon_limit_addr      (cfg_mon_limit_addr),
        .cfg_mon_flush_watermark (cfg_mon_flush_watermark),

        // Status
        .src_system_idle (src_system_idle),
        .src_sched_error (src_sched_error),
        .snk_system_idle (snk_system_idle),
        .snk_sched_error (snk_sched_error)
    );

    //=========================================================================
    // AXIS pattern generator -> DUT s_axis (sink-ingress stimulus)
    //=========================================================================
    // NOTE: LFSR/CRC params left at defaults, which are IDENTICAL across
    // axis4_master_pattern_gen, axis4_slave_pattern_check,
    // axi4_slave_rd_pattern_gen and axi4_slave_wr_crc_check (LFSR_SEED=DEADBEEF,
    // LFSR_TAPS={32,22,2,1}, CRC-32 Ethernet 0x04C11DB7). This keeps the on-chip
    // self-check (per-channel CRC) bit-consistent across all four blocks.
    axis4_master_pattern_gen #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH)
    ) u_axis_gen (
        .clk   (aclk),
        .rst_n (aresetn),
        .cfg_start            (cfg_gen_start),
        .cfg_lfsr_seed        (cfg_gen_lfsr_seed),
        .cfg_channel_mask     (cfg_gen_channel_mask),
        .cfg_num_beats        (cfg_gen_num_beats),
        .cfg_beats_per_pkt    (cfg_gen_beats_per_pkt),
        .cfg_tdest            (cfg_gen_tdest),
        .cfg_busy             (gen_busy),
        .cfg_done             (gen_done),
        .o_expected_crc       (o_gen_expected_crc),
        .o_expected_crc_valid (o_gen_expected_crc_valid),
        .o_beat_count         (),
        .o_beat_count_total   (o_gen_beat_count_total),
        .m_axis_tvalid (s_axis_tvalid),
        .m_axis_tready (s_axis_tready),
        .m_axis_tdata  (s_axis_tdata),
        .m_axis_tstrb  (s_axis_tstrb),
        .m_axis_tlast  (s_axis_tlast),
        .m_axis_tid    (s_axis_tid),
        .m_axis_tdest  (s_axis_tdest),
        .m_axis_tuser  (s_axis_tuser)
    );

    //=========================================================================
    // AXIS pattern checker <- DUT m_axis (source-egress check)
    //=========================================================================
    axis4_slave_pattern_check #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH)
    ) u_axis_chk (
        .clk   (aclk),
        .rst_n (aresetn),
        .cfg_start          (chk_cfg_start),
        .cfg_lfsr_seed      (chk_cfg_lfsr_seed),
        .ready_en           (chk_ready_en),
        .o_actual_crc       (o_chk_actual_crc),
        .o_actual_crc_valid (o_chk_actual_crc_valid),
        .o_data_error       (o_data_error),
        .o_beat_count       (),
        .o_beat_count_total (o_chk_beat_count_total),
        .o_pkt_count        (o_pkt_count),
        .s_axis_tvalid (m_axis_tvalid),
        .s_axis_tready (m_axis_tready),
        .s_axis_tdata  (m_axis_tdata),
        .s_axis_tstrb  (m_axis_tstrb),
        .s_axis_tlast  (m_axis_tlast),
        .s_axis_tid    (m_axis_tid),
        .s_axis_tdest  (m_axis_tdest),
        .s_axis_tuser  (m_axis_tuser)
    );

    //=========================================================================
    // Source-data memory: LFSR pattern generator backing DUT m_axi_rd_*
    //=========================================================================
    axi4_slave_rd_pattern_gen #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH)
    ) u_rd_mem (
        .aclk   (aclk),
        .aresetn(aresetn),
        .crc_lfsr_reset (rd_crc_lfsr_reset),
        .read_crc_value (rd_crc_value),
        .read_crc_valid (rd_crc_valid),
        .read_beat_count (),
        .read_beat_count_total (rd_beat_count_total),
        // AR (DUT m_axi_rd master -> slave); DUT drives no lock/cache/prot/
        // qos/region/user on this port, so tie the slave inputs quiescent.
        .s_axi_arid    (rd_arid),
        .s_axi_araddr  (rd_araddr),
        .s_axi_arlen   (rd_arlen),
        .s_axi_arsize  (rd_arsize),
        .s_axi_arburst (rd_arburst),
        .s_axi_arlock  (1'b0),
        .s_axi_arcache (4'h0),
        .s_axi_arprot  (3'h0),
        .s_axi_arqos   (4'h0),
        .s_axi_arregion(4'h0),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (rd_arvalid),
        .s_axi_arready (rd_arready),
        // R
        .s_axi_rid     (rd_rid),
        .s_axi_rdata   (rd_rdata),
        .s_axi_rresp   (rd_rresp),
        .s_axi_rlast   (rd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (rd_rvalid),
        .s_axi_rready  (rd_rready),
        .busy          (rd_mem_busy)
    );

    //=========================================================================
    // Sink-data memory: CRC checker backing DUT m_axi_wr_*
    //=========================================================================
    axi4_slave_wr_crc_check #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH)
    ) u_wr_mem (
        .aclk   (aclk),
        .aresetn(aresetn),
        .crc_reset (wr_crc_reset),
        .write_crc_value (wr_crc_value),
        .write_crc_valid (wr_crc_valid),
        .write_beat_count (),
        .write_beat_count_total (wr_beat_count_total),
        // AW (DUT m_axi_wr master -> slave); DUT drives no user on this port.
        .s_axi_awid    (wr_awid),
        .s_axi_awaddr  (wr_awaddr),
        .s_axi_awlen   (wr_awlen),
        .s_axi_awsize  (wr_awsize),
        .s_axi_awburst (wr_awburst),
        .s_axi_awlock  (wr_awlock),
        .s_axi_awcache (wr_awcache),
        .s_axi_awprot  (wr_awprot),
        .s_axi_awqos   (wr_awqos),
        .s_axi_awregion(wr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (wr_awvalid),
        .s_axi_awready (wr_awready),
        // W
        .s_axi_wdata   (wr_wdata),
        .s_axi_wstrb   (wr_wstrb),
        .s_axi_wlast   (wr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (wr_wvalid),
        .s_axi_wready  (wr_wready),
        // B
        .s_axi_bid     (wr_bid),
        .s_axi_bresp   (wr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (wr_bvalid),
        .s_axi_bready  (wr_bready),
        .busy          (wr_mem_busy)
    );

    //=========================================================================
    // SOURCE descriptor RAM (256-bit): DUT reads (port A) / host writes (port B)
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DESC_DATA_WIDTH),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_ENTRIES)
    ) u_desc_ram_src (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Port B: host descriptor write (exposed at harness boundary)
        .s_axi_awid    (desc_src_awid),
        .s_axi_awaddr  (desc_src_awaddr),
        .s_axi_awlen   (desc_src_awlen),
        .s_axi_awsize  (desc_src_awsize),
        .s_axi_awburst (desc_src_awburst),
        .s_axi_awlock  (1'b0),
        .s_axi_awcache (4'h0),
        .s_axi_awprot  (3'h0),
        .s_axi_awqos   (4'h0),
        .s_axi_awregion(4'h0),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (desc_src_awvalid),
        .s_axi_awready (desc_src_awready),
        .s_axi_wdata   (desc_src_wdata),
        .s_axi_wstrb   (desc_src_wstrb),
        .s_axi_wlast   (desc_src_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (desc_src_wvalid),
        .s_axi_wready  (desc_src_wready),
        .s_axi_bid     (desc_src_bid),
        .s_axi_bresp   (desc_src_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (desc_src_bvalid),
        .s_axi_bready  (desc_src_bready),
        // Port A: DUT source descriptor fetch (read-only)
        .s_axi_arid    (src_desc_arid),
        .s_axi_araddr  (src_desc_araddr),
        .s_axi_arlen   (src_desc_arlen),
        .s_axi_arsize  (src_desc_arsize),
        .s_axi_arburst (src_desc_arburst),
        .s_axi_arlock  (src_desc_arlock),
        .s_axi_arcache (src_desc_arcache),
        .s_axi_arprot  (src_desc_arprot),
        .s_axi_arqos   (src_desc_arqos),
        .s_axi_arregion(src_desc_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (src_desc_arvalid),
        .s_axi_arready (src_desc_arready),
        .s_axi_rid     (src_desc_rid),
        .s_axi_rdata   (src_desc_rdata),
        .s_axi_rresp   (src_desc_rresp),
        .s_axi_rlast   (src_desc_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (src_desc_rvalid),
        .s_axi_rready  (src_desc_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SINK descriptor RAM (256-bit): DUT reads (port A) / host writes (port B)
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DESC_DATA_WIDTH),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_ENTRIES)
    ) u_desc_ram_snk (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Port B: host descriptor write (exposed at harness boundary)
        .s_axi_awid    (desc_snk_awid),
        .s_axi_awaddr  (desc_snk_awaddr),
        .s_axi_awlen   (desc_snk_awlen),
        .s_axi_awsize  (desc_snk_awsize),
        .s_axi_awburst (desc_snk_awburst),
        .s_axi_awlock  (1'b0),
        .s_axi_awcache (4'h0),
        .s_axi_awprot  (3'h0),
        .s_axi_awqos   (4'h0),
        .s_axi_awregion(4'h0),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (desc_snk_awvalid),
        .s_axi_awready (desc_snk_awready),
        .s_axi_wdata   (desc_snk_wdata),
        .s_axi_wstrb   (desc_snk_wstrb),
        .s_axi_wlast   (desc_snk_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (desc_snk_wvalid),
        .s_axi_wready  (desc_snk_wready),
        .s_axi_bid     (desc_snk_bid),
        .s_axi_bresp   (desc_snk_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (desc_snk_bvalid),
        .s_axi_bready  (desc_snk_bready),
        // Port A: DUT sink descriptor fetch (read-only)
        .s_axi_arid    (snk_desc_arid),
        .s_axi_araddr  (snk_desc_araddr),
        .s_axi_arlen   (snk_desc_arlen),
        .s_axi_arsize  (snk_desc_arsize),
        .s_axi_arburst (snk_desc_arburst),
        .s_axi_arlock  (snk_desc_arlock),
        .s_axi_arcache (snk_desc_arcache),
        .s_axi_arprot  (snk_desc_arprot),
        .s_axi_arqos   (snk_desc_arqos),
        .s_axi_arregion(snk_desc_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (snk_desc_arvalid),
        .s_axi_arready (snk_desc_arready),
        .s_axi_rid     (snk_desc_rid),
        .s_axi_rdata   (snk_desc_rdata),
        .s_axi_rresp   (snk_desc_rresp),
        .s_axi_rlast   (snk_desc_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (snk_desc_rvalid),
        .s_axi_rready  (snk_desc_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SOURCE control semaphore RAM (32-bit): shared backing store so a ctrlwr
    // doorbell write is observable by a ctrlrd gate read.
    //   write port <- src_m_axi_ctrlwr ; read port <- src_m_axi_ctrlrd
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (32),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (CTRL_RAM_DEPTH)
    ) u_ctrl_ram_src (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Write port <- SOURCE ctrlwr master
        .s_axi_awid    (src_cwr_awid),
        .s_axi_awaddr  (src_cwr_awaddr),
        .s_axi_awlen   (src_cwr_awlen),
        .s_axi_awsize  (src_cwr_awsize),
        .s_axi_awburst (src_cwr_awburst),
        .s_axi_awlock  (src_cwr_awlock),
        .s_axi_awcache (src_cwr_awcache),
        .s_axi_awprot  (src_cwr_awprot),
        .s_axi_awqos   (src_cwr_awqos),
        .s_axi_awregion(src_cwr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (src_cwr_awvalid),
        .s_axi_awready (src_cwr_awready),
        .s_axi_wdata   (src_cwr_wdata),
        .s_axi_wstrb   (src_cwr_wstrb),
        .s_axi_wlast   (src_cwr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (src_cwr_wvalid),
        .s_axi_wready  (src_cwr_wready),
        .s_axi_bid     (src_cwr_bid),
        .s_axi_bresp   (src_cwr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (src_cwr_bvalid),
        .s_axi_bready  (src_cwr_bready),
        // Read port <- SOURCE ctrlrd master
        .s_axi_arid    (src_crd_arid),
        .s_axi_araddr  (src_crd_araddr),
        .s_axi_arlen   (src_crd_arlen),
        .s_axi_arsize  (src_crd_arsize),
        .s_axi_arburst (src_crd_arburst),
        .s_axi_arlock  (src_crd_arlock),
        .s_axi_arcache (src_crd_arcache),
        .s_axi_arprot  (src_crd_arprot),
        .s_axi_arqos   (src_crd_arqos),
        .s_axi_arregion(src_crd_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (src_crd_arvalid),
        .s_axi_arready (src_crd_arready),
        .s_axi_rid     (src_crd_rid),
        .s_axi_rdata   (src_crd_rdata),
        .s_axi_rresp   (src_crd_rresp),
        .s_axi_rlast   (src_crd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (src_crd_rvalid),
        .s_axi_rready  (src_crd_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SINK control semaphore RAM (32-bit): shared backing store.
    //   write port <- snk_m_axi_ctrlwr ; read port <- snk_m_axi_ctrlrd
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (32),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (CTRL_RAM_DEPTH)
    ) u_ctrl_ram_snk (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Write port <- SINK ctrlwr master
        .s_axi_awid    (snk_cwr_awid),
        .s_axi_awaddr  (snk_cwr_awaddr),
        .s_axi_awlen   (snk_cwr_awlen),
        .s_axi_awsize  (snk_cwr_awsize),
        .s_axi_awburst (snk_cwr_awburst),
        .s_axi_awlock  (snk_cwr_awlock),
        .s_axi_awcache (snk_cwr_awcache),
        .s_axi_awprot  (snk_cwr_awprot),
        .s_axi_awqos   (snk_cwr_awqos),
        .s_axi_awregion(snk_cwr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (snk_cwr_awvalid),
        .s_axi_awready (snk_cwr_awready),
        .s_axi_wdata   (snk_cwr_wdata),
        .s_axi_wstrb   (snk_cwr_wstrb),
        .s_axi_wlast   (snk_cwr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (snk_cwr_wvalid),
        .s_axi_wready  (snk_cwr_wready),
        .s_axi_bid     (snk_cwr_bid),
        .s_axi_bresp   (snk_cwr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (snk_cwr_bvalid),
        .s_axi_bready  (snk_cwr_bready),
        // Read port <- SINK ctrlrd master
        .s_axi_arid    (snk_crd_arid),
        .s_axi_araddr  (snk_crd_araddr),
        .s_axi_arlen   (snk_crd_arlen),
        .s_axi_arsize  (snk_crd_arsize),
        .s_axi_arburst (snk_crd_arburst),
        .s_axi_arlock  (snk_crd_arlock),
        .s_axi_arcache (snk_crd_arcache),
        .s_axi_arprot  (snk_crd_arprot),
        .s_axi_arqos   (snk_crd_arqos),
        .s_axi_arregion(snk_crd_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (snk_crd_arvalid),
        .s_axi_arready (snk_crd_arready),
        .s_axi_rid     (snk_crd_rid),
        .s_axi_rdata   (snk_crd_rdata),
        .s_axi_rresp   (snk_crd_rresp),
        .s_axi_rlast   (snk_crd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (snk_crd_rvalid),
        .s_axi_rready  (snk_crd_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // MonBus AXIL capture master: always-accept write responder.
    // aw/w are accepted every cycle (never stalls the always-on monitor
    // egress); a matched aw/w pair produces one OKAY B. Monotonic counters
    // compared mod-2^16 keep bvalid asserted while responses are owed.
    //=========================================================================
    assign mon_awready = 1'b1;
    assign mon_wready  = 1'b1;
    assign mon_bresp   = 2'b00;  // OKAY

    logic [15:0] r_mon_aw_cnt, r_mon_w_cnt, r_mon_b_cnt;
    wire mon_b_beat = mon_bvalid && mon_bready;
    assign mon_bvalid = (r_mon_aw_cnt != r_mon_b_cnt) && (r_mon_w_cnt != r_mon_b_cnt);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mon_aw_cnt <= '0;
            r_mon_w_cnt  <= '0;
            r_mon_b_cnt  <= '0;
        end else begin
            if (mon_awvalid && mon_awready) r_mon_aw_cnt <= r_mon_aw_cnt + 16'd1;
            if (mon_wvalid  && mon_wready)  r_mon_w_cnt  <= r_mon_w_cnt  + 16'd1;
            if (mon_b_beat)                 r_mon_b_cnt  <= r_mon_b_cnt  + 16'd1;
        end
    )

    //=========================================================================
    // Datapath bus meters (per-interface utilization + AXIS throughput)
    //
    // AXI4 interfaces use axi_bus_meter; AXIS interfaces use axis_bus_meter (the
    // AXIS-native observer, which additionally counts bytes via tstrb and packets
    // via tlast):
    //   rd   AXI4 source read  (rd_r*)      wr   AXI4 sink write (wr_w*)
    //   sin  AXIS sink ingress (s_axis)     sout AXIS source egress (m_axis)
    // Each classifies every window cycle into PRODUCTIVE / BACKPRESSURE /
    // STARVATION / IDLE; the AXIS meters also accumulate exact bytes/packets.
    //=========================================================================
    // Measurement window: DUT-IDLE driven. A host obs_arm pulse clears + re-arms;
    // the window OPENS when the DUT goes busy (system_idle deasserts) and CLOSES
    // OBS_SETTLE_CYCLES after it goes idle again. Keying the window on the DUT's
    // own "transfer done" (system_idle) -- NOT on valid/ready -- makes it immune
    // to the AXIS pattern generator holding tvalid asserted after it has finished
    // sending (which previously inflated the sink backpressure bucket without
    // bound). The trailing settle idle lands in the IDLE bucket, excluded from
    // engaged utilization (prod / (prod+bp+starv)).
    localparam int OBS_SETTLE_CYCLES = 255;   // ~2.5us @ 100 MHz -- bridge idle blips
    // Busy is gated by the ACTIVE half only. Keying on both halves let a stuck
    // (non-idle) idle half from a prior run poison the window forever, so it
    // never closed and ran until the host read it (util diluted to ~0%).
    logic obs_dut_busy;
    assign obs_dut_busy = obs_active_half ? ~snk_system_idle : ~src_system_idle;
    // Completion trigger: productive beats on the LAST interface of the path.
    wire [31:0] w_obs_trigger = obs_active_half ? obs_wr_prod : obs_sout_prod;
    wire        w_obs_target_hit = (obs_target != 32'd0) && (w_obs_trigger >= obs_target);
    logic        obs_win_active, obs_started;
    logic [7:0]  obs_settle;
    logic        obs_meter_clear, obs_meter_freeze;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            obs_win_active <= 1'b0; obs_started <= 1'b0; obs_settle <= 8'd0;
        end else if (obs_arm) begin
            obs_win_active <= 1'b0; obs_started <= 1'b0; obs_settle <= 8'd0;
        end else begin
            if (obs_dut_busy && !obs_win_active && !obs_started) begin
                obs_win_active <= 1'b1; obs_started <= 1'b1; obs_settle <= 8'd0;
            end else if (obs_win_active) begin
                // Deterministic close the cycle after the target-th productive
                // beat -- immune to whether system_idle ever asserts. The
                // system_idle settle remains a fallback when obs_target == 0.
                if (w_obs_target_hit)                          obs_win_active <= 1'b0;
                else if (obs_dut_busy)                         obs_settle <= 8'd0;
                else if (obs_settle != OBS_SETTLE_CYCLES[7:0]) obs_settle <= obs_settle + 8'd1;
                else                                           obs_win_active <= 1'b0;  // close
            end
        end
    )
    assign obs_meter_clear  = obs_arm || (obs_dut_busy && !obs_win_active && !obs_started);
    assign obs_meter_freeze = ~obs_win_active;

    // ---- Sink-ingress window (TASK-082) -------------------------------------
    // The shared window above opens on obs_dut_busy (~snk_system_idle), which
    // CANNOT assert until the DUT has already accepted traffic. So every ingress
    // beat that lands in the gap between ARM and that first busy cycle was never
    // counted: measured missed == min(dead_zone, total) -- 190 beats on the
    // 8-channel board, and 100% of the transfer whenever it is shorter than the
    // gap (which is why small runs read a flat prod=0 and looked like a dead
    // meter). Confirmed on a waveform: 32 handshakes complete 78 clocks BEFORE
    // the counted window opens.
    //
    // So s_axis gets its own window that opens at ARM -- the same cycle CSR_GO
    // pulses cfg_gen_start, i.e. before the generator can emit anything -- and
    // closes WITH the shared window so sin and wr still describe the same span.
    //
    // The original busy-gating existed to stop the generator holding tvalid after
    // it finishes from inflating the backpressure bucket "without bound". That
    // stays bounded here: the shared window closes deterministically on
    // wr_prod >= obs_target, so any trailing bp is bounded by the transfer.
    logic obs_sin_win_active;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))                obs_sin_win_active <= 1'b0;
        else if (obs_arm)                          obs_sin_win_active <= 1'b1;
        else if (obs_started && !obs_win_active)   obs_sin_win_active <= 1'b0;
    )
    logic obs_sin_clear, obs_sin_freeze;
    assign obs_sin_clear  = obs_arm;
    assign obs_sin_freeze = ~obs_sin_win_active;

    // ---- AXI4 meters: rd (source read) + wr (sink write) --------------------
    logic [15:0] rd_ch_p[1], rd_ch_b[1], rd_ch_s[1], rd_ch_i[1]; logic [3:0] rd_ch_o;
    logic [15:0] wr_ch_p[1], wr_ch_b[1], wr_ch_s[1], wr_ch_i[1]; logic [3:0] wr_ch_o;
    axi_bus_meter #(.NUM_CHANNELS(1)) u_meter_rd (
        .aclk(aclk), .aresetn(aresetn), .i_clear(obs_meter_clear), .i_freeze(obs_meter_freeze),
        .i_valid(rd_rvalid), .i_ready(rd_rready), .i_channel_id(1'b0), .i_channel_valid(rd_rvalid),
        .o_agg_productive(obs_rd_prod), .o_agg_backpressure(obs_rd_bp),
        .o_agg_starvation(obs_rd_starv), .o_agg_idle(obs_rd_idle),
        .o_ch_productive(rd_ch_p), .o_ch_backpressure(rd_ch_b),
        .o_ch_starvation(rd_ch_s), .o_ch_idle(rd_ch_i), .o_ch_overflow(rd_ch_o));
    axi_bus_meter #(.NUM_CHANNELS(1)) u_meter_wr (
        .aclk(aclk), .aresetn(aresetn), .i_clear(obs_meter_clear), .i_freeze(obs_meter_freeze),
        .i_valid(wr_wvalid), .i_ready(wr_wready), .i_channel_id(1'b0), .i_channel_valid(wr_wvalid),
        .o_agg_productive(obs_wr_prod), .o_agg_backpressure(obs_wr_bp),
        .o_agg_starvation(obs_wr_starv), .o_agg_idle(obs_wr_idle),
        .o_ch_productive(wr_ch_p), .o_ch_backpressure(wr_ch_b),
        .o_ch_starvation(wr_ch_s), .o_ch_idle(wr_ch_i), .o_ch_overflow(wr_ch_o));

    // ---- AXIS meters: sin (sink ingress) + sout (source egress) -------------
    // axis_bus_meter adds exact byte (tstrb) + packet (tlast) counts.
    logic [15:0] sin_ch_p[1], sin_ch_b[1], sin_ch_s[1], sin_ch_i[1]; logic [3:0] sin_ch_o;
    logic [15:0] sot_ch_p[1], sot_ch_b[1], sot_ch_s[1], sot_ch_i[1]; logic [3:0] sot_ch_o;
    axis_bus_meter #(.DATA_WIDTH(DATA_WIDTH), .NUM_CHANNELS(1)) u_meter_sin (
        .aclk(aclk), .aresetn(aresetn), .i_clear(obs_sin_clear), .i_freeze(obs_sin_freeze),
        .i_tvalid(s_axis_tvalid), .i_tready(s_axis_tready), .i_tlast(s_axis_tlast),
        .i_tstrb(s_axis_tstrb), .i_tid(1'b0),
        .o_agg_productive(obs_sin_prod), .o_agg_backpressure(obs_sin_bp),
        .o_agg_starvation(obs_sin_starv), .o_agg_idle(obs_sin_idle),
        .o_agg_bytes(obs_sin_bytes), .o_agg_beats(), .o_agg_packets(obs_sin_packets),
        .o_ch_productive(sin_ch_p), .o_ch_backpressure(sin_ch_b),
        .o_ch_starvation(sin_ch_s), .o_ch_idle(sin_ch_i), .o_ch_overflow(sin_ch_o));
    axis_bus_meter #(.DATA_WIDTH(DATA_WIDTH), .NUM_CHANNELS(1)) u_meter_sout (
        .aclk(aclk), .aresetn(aresetn), .i_clear(obs_meter_clear), .i_freeze(obs_meter_freeze),
        .i_tvalid(m_axis_tvalid), .i_tready(m_axis_tready), .i_tlast(m_axis_tlast),
        .i_tstrb(m_axis_tstrb), .i_tid(1'b0),
        .o_agg_productive(obs_sout_prod), .o_agg_backpressure(obs_sout_bp),
        .o_agg_starvation(obs_sout_starv), .o_agg_idle(obs_sout_idle),
        .o_agg_bytes(obs_sout_bytes), .o_agg_beats(), .o_agg_packets(obs_sout_packets),
        .o_ch_productive(sot_ch_p), .o_ch_backpressure(sot_ch_b),
        .o_ch_starvation(sot_ch_s), .o_ch_idle(sot_ch_i), .o_ch_overflow(sot_ch_o));

endmodule : rapids_char_harness
