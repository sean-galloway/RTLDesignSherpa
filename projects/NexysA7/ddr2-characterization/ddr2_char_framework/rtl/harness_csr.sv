// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: harness_csr
// Purpose: Control / status / engine-cfg registers for the DDR2/LPDDR2
//          characterization harness. AXI4-Lite slave; host visibility
//          via the 1->5 UART-fed AXIL bridge.
//
// This is the DDR2 sibling of stream_char_framework/rtl/harness_csr.sv.
// Same shape (skid-buffered AXIL slave, one write FSM + one read decode),
// different register map. Because the char macro has two indepedent
// master-side engines (axi4_master_wr_pattern_gen + axi4_master_rd_crc_check)
// each with ~15 cfg inputs, this CSR block ALSO holds every engine cfg
// register — the host writes them here, this block fans them out as
// steady-state signals to the char macro.
//
// Register map (byte offsets from harness_csr base = 0x0001_0000):
//
// -- Harness control / status --------------------------------------------
//   0x00  CTRL              RW  [0]  start_wr     (self-clearing pulse)
//                                [1]  start_rd     (self-clearing pulse)
//                                [2]  clear_stats  (self-clearing pulse)
//                                [3]  freeze_trace (latch; stops debug_sram)
//                                [4]  soft_reset   (self-clearing pulse)
//   0x04  STATUS            R   [0]  wr_done       (from engine)
//                                [1]  rd_done       (from engine)
//                                [2]  wr_error      (bresp / sticky)
//                                [3]  rd_error      (rresp / data / sticky)
//                                [4]  any_error     (any of the above)
//                                [5]  dbg_clear_busy
//                                [6]  init_done     (controller init sequence)
//                                [7]  init_fail
//   0x08  DBG_WR_PTR        R   words written to debug_sram
//   0x0C  DBG_OVERFLOW      R   sticky trace-overflow flag
//   0x10  CRC_EXPECTED      R   from WR engine (o_expected_crc)
//   0x14  CRC_ACTUAL        R   from RD engine (o_actual_crc)
//   0x18  CRC_MATCH         R   [0]match [1]exp_valid [2]act_valid
//                                [3] beats_mismatched != 0
//   0x1C  SCRATCH           RW  host bring-up ping
//   0x20  BUILD_ID          R   parameter-driven build ID (default "DDR2")
//   0x24  BEATS_MISM        R   o_beats_mismatched (RD engine)
//
// -- Characterization timer ----------------------------------------------
//   0x28  TIMER_CTRL        W   [0] clear-pulse (resets done/cycles/pass)
//   0x2C  TIMER_STATUS      R   [0]done [1]running [2]pass
//   0x30  TIMER_CYCLES_LO   R   64b cycle counter, low
//   0x34  TIMER_CYCLES_HI   R
//   0x38  TIMER_EXP_BEATS   RW  stop trigger; 0 = disable
//   0x3C  RESP_DELAY        RW  [15:0]rd_delay [31:16]wr_delay (axi_response_delay)
//
//   0x40  TIMER_R_FIRST_LO  R
//   0x44  TIMER_R_FIRST_HI  R
//   0x48  TIMER_R_LAST_LO   R
//   0x4C  TIMER_R_LAST_HI   R
//   0x50  TIMER_W_FIRST_LO  R
//   0x54  TIMER_W_FIRST_HI  R
//   0x58  TIMER_W_LAST_LO   R
//   0x5C  TIMER_W_LAST_HI   R
//
// -- Runtime controller cfg (drives ddr2_char_macro cfg inputs) ----------
//   0x60  CTRLR_CFG         RW  [0]     memtype (0=DDR2, 1=LPDDR2)
//                                [15:8]  t_phy_wrlat
//                                [23:16] t_rddata_en
//                                [24]    rd_in_order
//   0x64  CTRLR_CAP         RW  [3:0]   cap_lookahead_max
//                                [7:4]   cap_synth_mask
//
// -- WR engine cfg (0x100..0x12F) ----------------------------------------
//   0x100  WR_START_ADDR    RW
//   0x104  WR_STRIDE_0      RW  (signed, STRIDE_WIDTH-bit sign-extended in RTL)
//   0x108  WR_STRIDE_1      RW
//   0x10C  WR_WRAP_MASK_0   RW
//   0x110  WR_WRAP_MASK_1   RW
//   0x114  WR_BLEN_TXN      RW  [7:0]burst_len  [23:8]txn_count  [31:24]gap[3:0]
//   0x118  WR_AXI_ATTR      RW  [3:0]axi_id  [5:4]id_mode  [8:6]axi_size
//                                 [10:9]axi_burst  [11]data_mode
//   0x11C  WR_LFSR_SEED     RW
//   0x120  WR_HASH_SEED0    RW
//   0x124  WR_HASH_SEED1    RW
//   0x128  WR_HASH_SEED2    RW
//
// -- RD engine cfg (0x180..0x1AF) — mirror of WR ------------------------
//   0x180  RD_START_ADDR    RW
//   0x184  RD_STRIDE_0      RW
//   0x188  RD_STRIDE_1      RW
//   0x18C  RD_WRAP_MASK_0   RW
//   0x190  RD_WRAP_MASK_1   RW
//   0x194  RD_BLEN_TXN      RW
//   0x198  RD_AXI_ATTR      RW
//   0x19C  RD_LFSR_SEED     RW
//   0x1A0  RD_HASH_SEED0    RW
//   0x1A4  RD_HASH_SEED1    RW
//   0x1A8  RD_HASH_SEED2    RW
//
// Any address not listed reads as 0 and ignores writes.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module harness_csr
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AW = 32,
    parameter int DW = 32,
    parameter int AXI_ID_WIDTH     = 4,
    parameter int STRIDE_WIDTH     = 24,
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int BURST_LEN_WIDTH  = 8,
    parameter logic [31:0] BUILD_ID = 32'h4444_5232,  // "DDR2"

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2
) (
    input  logic            aclk,
    input  logic            aresetn,

    // =====================================================================
    // AXI4-Lite slave
    // =====================================================================
    input  logic [AW-1:0]   s_awaddr,
    input  logic [2:0]      s_awprot,
    input  logic            s_awvalid,
    output logic            s_awready,

    input  logic [DW-1:0]   s_wdata,
    input  logic [DW/8-1:0] s_wstrb,
    input  logic            s_wvalid,
    output logic            s_wready,

    output logic [1:0]      s_bresp,
    output logic            s_bvalid,
    input  logic            s_bready,

    input  logic [AW-1:0]   s_araddr,
    input  logic [2:0]      s_arprot,
    input  logic            s_arvalid,
    output logic            s_arready,

    output logic [DW-1:0]   s_rdata,
    output logic [1:0]      s_rresp,
    output logic            s_rvalid,
    input  logic            s_rready,

    // =====================================================================
    // Harness control outputs
    // =====================================================================
    output logic            o_start_wr_pulse,
    output logic            o_start_rd_pulse,
    output logic            o_clear_stats_pulse,
    output logic            o_freeze_trace,
    output logic            o_soft_reset_pulse,

    // =====================================================================
    // Harness status inputs
    // =====================================================================
    input  logic            i_wr_done,
    input  logic            i_rd_done,
    input  logic            i_wr_error,
    input  logic            i_rd_error,
    input  logic            i_init_done,
    input  logic            i_init_fail,
    input  logic [31:0]     i_dbg_wr_ptr,
    input  logic            i_dbg_overflow,
    input  logic            i_dbg_clear_busy,

    input  logic [31:0]     i_crc_expected,
    input  logic [31:0]     i_crc_actual,
    input  logic            i_crc_exp_valid,
    input  logic            i_crc_act_valid,
    input  logic [TXN_COUNT_WIDTH-1:0] i_beats_mismatched,

    // =====================================================================
    // Timer interface
    // =====================================================================
    output logic            o_timer_clear_pulse,
    output logic [31:0]     o_timer_expected_beats,
    input  logic            i_timer_done,
    input  logic            i_timer_running,
    input  logic            i_timer_pass,
    input  logic [63:0]     i_timer_cycles,
    input  logic [63:0]     i_timer_r_first,
    input  logic [63:0]     i_timer_r_last,
    input  logic [63:0]     i_timer_w_first,
    input  logic [63:0]     i_timer_w_last,

    // =====================================================================
    // Response-delay knobs
    // =====================================================================
    output logic [15:0]     o_rd_resp_delay_cyc,
    output logic [15:0]     o_wr_resp_delay_cyc,

    // =====================================================================
    // Runtime controller cfg outputs (into ddr2_char_macro)
    // =====================================================================
    output memtype_e        o_memtype,
    output logic [7:0]      o_t_phy_wrlat,
    output logic [7:0]      o_t_rddata_en,
    output logic            o_rd_in_order,
    output logic [3:0]      o_cap_lookahead_max,
    output logic [3:0]      o_cap_synth_mask,

    // =====================================================================
    // WR-engine cfg outputs (drive ddr2_char_macro cfg_wr_* inputs)
    // =====================================================================
    output logic [AW-1:0]                       o_cfg_wr_start_addr,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_wr_stride_0,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_wr_stride_1,
    output logic [AW-1:0]                       o_cfg_wr_wrap_mask_0,
    output logic [AW-1:0]                       o_cfg_wr_wrap_mask_1,
    output logic [BURST_LEN_WIDTH-1:0]          o_cfg_wr_burst_len,
    output logic [TXN_COUNT_WIDTH-1:0]          o_cfg_wr_txn_count,
    output logic [AXI_ID_WIDTH-1:0]             o_cfg_wr_axi_id,
    output logic [1:0]                          o_cfg_wr_id_mode,
    output logic [2:0]                          o_cfg_wr_axi_size,
    output logic [1:0]                          o_cfg_wr_axi_burst,
    output logic [3:0]                          o_cfg_wr_gap,
    output logic                                o_cfg_wr_data_mode,
    output logic [31:0]                         o_cfg_wr_lfsr_seed,
    output logic [31:0]                         o_cfg_wr_hash_seed0,
    output logic [31:0]                         o_cfg_wr_hash_seed1,
    output logic [31:0]                         o_cfg_wr_hash_seed2,

    // =====================================================================
    // RD-engine cfg outputs (drive ddr2_char_macro cfg_rd_* inputs)
    // =====================================================================
    output logic [AW-1:0]                       o_cfg_rd_start_addr,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_rd_stride_0,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_rd_stride_1,
    output logic [AW-1:0]                       o_cfg_rd_wrap_mask_0,
    output logic [AW-1:0]                       o_cfg_rd_wrap_mask_1,
    output logic [BURST_LEN_WIDTH-1:0]          o_cfg_rd_burst_len,
    output logic [TXN_COUNT_WIDTH-1:0]          o_cfg_rd_txn_count,
    output logic [AXI_ID_WIDTH-1:0]             o_cfg_rd_axi_id,
    output logic [1:0]                          o_cfg_rd_id_mode,
    output logic [2:0]                          o_cfg_rd_axi_size,
    output logic [1:0]                          o_cfg_rd_axi_burst,
    output logic [3:0]                          o_cfg_rd_gap,
    output logic                                o_cfg_rd_data_mode,
    output logic [31:0]                         o_cfg_rd_lfsr_seed,
    output logic [31:0]                         o_cfg_rd_hash_seed0,
    output logic [31:0]                         o_cfg_rd_hash_seed1,
    output logic [31:0]                         o_cfg_rd_hash_seed2
);

    // Packed widths for the skid buffers
    localparam int AW_PKT_W = AW + 3;
    localparam int W_PKT_W  = DW + (DW/8);
    localparam int B_PKT_W  = 2;
    localparam int AR_PKT_W = AW + 3;
    localparam int R_PKT_W  = DW + 2;

    // =========================================================================
    // AW / W / B skid buffers
    // =========================================================================
    logic                 int_awvalid, int_awready;
    logic [AW_PKT_W-1:0]  int_aw_pkt;
    logic [AW-1:0]        int_awaddr;
    logic [2:0]           int_awprot;
    assign {int_awaddr, int_awprot} = int_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AW_PKT_W)
    ) u_skid_aw (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_awvalid), .wr_ready(s_awready),
        .wr_data ({s_awaddr, s_awprot}),
        .count   (),
        .rd_valid(int_awvalid), .rd_ready(int_awready),
        .rd_count(), .rd_data(int_aw_pkt)
    );

    logic                int_wvalid, int_wready;
    logic [W_PKT_W-1:0]  int_w_pkt;
    logic [DW-1:0]       int_wdata;
    logic [DW/8-1:0]     int_wstrb;
    assign {int_wdata, int_wstrb} = int_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(W_PKT_W)
    ) u_skid_w (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_wvalid), .wr_ready(s_wready),
        .wr_data ({s_wdata, s_wstrb}),
        .count   (),
        .rd_valid(int_wvalid), .rd_ready(int_wready),
        .rd_count(), .rd_data(int_w_pkt)
    );

    logic                int_bvalid, int_bready;
    logic [B_PKT_W-1:0]  int_b_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_B),
        .DATA_WIDTH(B_PKT_W)
    ) u_skid_b (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_bvalid), .wr_ready(int_bready),
        .wr_data (int_b_pkt),
        .count   (),
        .rd_valid(s_bvalid), .rd_ready(s_bready),
        .rd_count(), .rd_data(s_bresp)
    );

    // =========================================================================
    // AR / R skid buffers
    // =========================================================================
    logic                 int_arvalid, int_arready;
    logic [AR_PKT_W-1:0]  int_ar_pkt;
    logic [AW-1:0]        int_araddr;
    logic [2:0]           int_arprot;
    assign {int_araddr, int_arprot} = int_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR_PKT_W)
    ) u_skid_ar (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_arvalid), .wr_ready(s_arready),
        .wr_data ({s_araddr, s_arprot}),
        .count   (),
        .rd_valid(int_arvalid), .rd_ready(int_arready),
        .rd_count(), .rd_data(int_ar_pkt)
    );

    logic                int_rvalid, int_rready;
    logic [R_PKT_W-1:0]  int_r_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_R),
        .DATA_WIDTH(R_PKT_W)
    ) u_skid_r (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_rvalid), .wr_ready(int_rready),
        .wr_data (int_r_pkt),
        .count   (),
        .rd_valid(s_rvalid), .rd_ready(s_rready),
        .rd_count(), .rd_data({s_rdata, s_rresp})
    );

    // =========================================================================
    // Register storage
    // =========================================================================
    // Harness control latches / pulses
    logic        r_freeze_trace;
    logic        r_start_wr_pulse;
    logic        r_start_rd_pulse;
    logic        r_clear_stats_pulse;
    logic        r_soft_reset_pulse;

    // Sticky status
    logic        r_wr_err_sticky;
    logic        r_rd_err_sticky;

    logic [31:0] r_scratch;

    // Timer
    logic        r_timer_clear_pulse;
    logic [31:0] r_timer_expected_beats;

    // Response delay
    logic [15:0] r_rd_resp_delay_cyc;
    logic [15:0] r_wr_resp_delay_cyc;

    // Controller runtime cfg
    logic [31:0] r_ctrlr_cfg;   // {7'd0, rd_in_order, t_rddata_en, t_phy_wrlat, 7'd0, memtype}
    logic [31:0] r_ctrlr_cap;   // {24'd0, cap_synth_mask, cap_lookahead_max}

    // WR engine cfg
    logic [31:0] r_wr_start_addr;
    logic [31:0] r_wr_stride_0;
    logic [31:0] r_wr_stride_1;
    logic [31:0] r_wr_wrap_mask_0;
    logic [31:0] r_wr_wrap_mask_1;
    logic [31:0] r_wr_blen_txn;   // [7:0]burst_len [23:8]txn_count [27:24]gap
    logic [31:0] r_wr_axi_attr;   // [3:0]axi_id [5:4]id_mode [8:6]axi_size [10:9]axi_burst [11]data_mode
    logic [31:0] r_wr_lfsr_seed;
    logic [31:0] r_wr_hash_seed0;
    logic [31:0] r_wr_hash_seed1;
    logic [31:0] r_wr_hash_seed2;

    // RD engine cfg (mirror)
    logic [31:0] r_rd_start_addr;
    logic [31:0] r_rd_stride_0;
    logic [31:0] r_rd_stride_1;
    logic [31:0] r_rd_wrap_mask_0;
    logic [31:0] r_rd_wrap_mask_1;
    logic [31:0] r_rd_blen_txn;
    logic [31:0] r_rd_axi_attr;
    logic [31:0] r_rd_lfsr_seed;
    logic [31:0] r_rd_hash_seed0;
    logic [31:0] r_rd_hash_seed1;
    logic [31:0] r_rd_hash_seed2;

    // =========================================================================
    // Write channel FSM
    // =========================================================================
    typedef enum logic [1:0] {
        W_IDLE  = 2'd0,
        W_BRESP = 2'd1
    } w_state_t;

    w_state_t r_wstate;

    // 9-bit slice covers 0x000..0x1FF (harness ctrl + engine cfg regions).
    logic [8:0] w_waddr;
    assign w_waddr = int_awaddr[8:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wstate               <= W_IDLE;
            r_freeze_trace         <= 1'b0;
            r_start_wr_pulse       <= 1'b0;
            r_start_rd_pulse       <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_scratch              <= '0;
            r_timer_clear_pulse    <= 1'b0;
            r_timer_expected_beats <= '0;
            r_rd_resp_delay_cyc    <= '0;
            r_wr_resp_delay_cyc    <= '0;
            r_ctrlr_cfg            <= '0;
            r_ctrlr_cap            <= '0;

            r_wr_start_addr        <= '0;
            r_wr_stride_0          <= '0;
            r_wr_stride_1          <= '0;
            r_wr_wrap_mask_0       <= '0;
            r_wr_wrap_mask_1       <= '0;
            r_wr_blen_txn          <= '0;
            r_wr_axi_attr          <= '0;
            r_wr_lfsr_seed         <= '0;
            r_wr_hash_seed0        <= '0;
            r_wr_hash_seed1        <= '0;
            r_wr_hash_seed2        <= '0;

            r_rd_start_addr        <= '0;
            r_rd_stride_0          <= '0;
            r_rd_stride_1          <= '0;
            r_rd_wrap_mask_0       <= '0;
            r_rd_wrap_mask_1       <= '0;
            r_rd_blen_txn          <= '0;
            r_rd_axi_attr          <= '0;
            r_rd_lfsr_seed         <= '0;
            r_rd_hash_seed0        <= '0;
            r_rd_hash_seed1        <= '0;
            r_rd_hash_seed2        <= '0;
        end else begin
            // Default: pulses auto-clear each cycle
            r_start_wr_pulse       <= 1'b0;
            r_start_rd_pulse       <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_timer_clear_pulse    <= 1'b0;

            case (r_wstate)
                W_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        case (w_waddr)
                            9'h000: begin
                                r_start_wr_pulse    <= int_wdata[0];
                                r_start_rd_pulse    <= int_wdata[1];
                                r_clear_stats_pulse <= int_wdata[2];
                                r_freeze_trace      <= int_wdata[3];
                                r_soft_reset_pulse  <= int_wdata[4];
                            end
                            9'h01C: r_scratch <= int_wdata;
                            9'h028: r_timer_clear_pulse <= int_wdata[0];
                            9'h038: r_timer_expected_beats <= int_wdata;
                            9'h03C: begin
                                r_rd_resp_delay_cyc <= int_wdata[15:0];
                                r_wr_resp_delay_cyc <= int_wdata[31:16];
                            end
                            9'h060: r_ctrlr_cfg <= int_wdata;
                            9'h064: r_ctrlr_cap <= int_wdata;

                            // WR engine cfg
                            9'h100: r_wr_start_addr  <= int_wdata;
                            9'h104: r_wr_stride_0    <= int_wdata;
                            9'h108: r_wr_stride_1    <= int_wdata;
                            9'h10C: r_wr_wrap_mask_0 <= int_wdata;
                            9'h110: r_wr_wrap_mask_1 <= int_wdata;
                            9'h114: r_wr_blen_txn    <= int_wdata;
                            9'h118: r_wr_axi_attr    <= int_wdata;
                            9'h11C: r_wr_lfsr_seed   <= int_wdata;
                            9'h120: r_wr_hash_seed0  <= int_wdata;
                            9'h124: r_wr_hash_seed1  <= int_wdata;
                            9'h128: r_wr_hash_seed2  <= int_wdata;

                            // RD engine cfg
                            9'h180: r_rd_start_addr  <= int_wdata;
                            9'h184: r_rd_stride_0    <= int_wdata;
                            9'h188: r_rd_stride_1    <= int_wdata;
                            9'h18C: r_rd_wrap_mask_0 <= int_wdata;
                            9'h190: r_rd_wrap_mask_1 <= int_wdata;
                            9'h194: r_rd_blen_txn    <= int_wdata;
                            9'h198: r_rd_axi_attr    <= int_wdata;
                            9'h19C: r_rd_lfsr_seed   <= int_wdata;
                            9'h1A0: r_rd_hash_seed0  <= int_wdata;
                            9'h1A4: r_rd_hash_seed1  <= int_wdata;
                            9'h1A8: r_rd_hash_seed2  <= int_wdata;

                            default: ;  // ignore
                        endcase
                        r_wstate <= W_BRESP;
                    end
                end
                W_BRESP: begin
                    if (int_bready) r_wstate <= W_IDLE;
                end
                default: r_wstate <= W_IDLE;
            endcase
        end
    )

    assign int_awready = (r_wstate == W_IDLE) && int_wvalid;
    assign int_wready  = (r_wstate == W_IDLE) && int_awvalid;
    assign int_bvalid  = (r_wstate == W_BRESP);
    assign int_b_pkt   = 2'b00;

    // =========================================================================
    // Sticky error latches (cleared by CTRL.clear_stats)
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_err_sticky <= 1'b0;
            r_rd_err_sticky <= 1'b0;
        end else begin
            if (r_clear_stats_pulse) begin
                r_wr_err_sticky <= 1'b0;
                r_rd_err_sticky <= 1'b0;
            end else begin
                if (i_wr_error) r_wr_err_sticky <= 1'b1;
                if (i_rd_error) r_rd_err_sticky <= 1'b1;
            end
        end
    )

    // =========================================================================
    // Read channel FSM
    // =========================================================================
    typedef enum logic [0:0] {
        R_IDLE  = 1'b0,
        R_RRESP = 1'b1
    } r_state_t;

    r_state_t r_rstate;
    logic [31:0] r_rdata;

    logic [8:0] w_raddr;
    assign w_raddr = int_araddr[8:0];

    // Assembled words
    logic [31:0] w_status;
    always_comb begin
        w_status = '0;
        w_status[0] = i_wr_done;
        w_status[1] = i_rd_done;
        w_status[2] = r_wr_err_sticky;
        w_status[3] = r_rd_err_sticky;
        w_status[4] = r_wr_err_sticky | r_rd_err_sticky;
        w_status[5] = i_dbg_clear_busy;
        w_status[6] = i_init_done;
        w_status[7] = i_init_fail;
    end

    logic [31:0] w_crc_match;
    always_comb begin
        w_crc_match = '0;
        w_crc_match[0] = (i_crc_expected == i_crc_actual)
                         && i_crc_exp_valid && i_crc_act_valid;
        w_crc_match[1] = i_crc_exp_valid;
        w_crc_match[2] = i_crc_act_valid;
        w_crc_match[3] = |i_beats_mismatched;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= R_IDLE;
            r_rdata  <= '0;
        end else begin
            case (r_rstate)
                R_IDLE: begin
                    if (int_arvalid) begin
                        case (w_raddr)
                            9'h000: r_rdata <= {27'd0, 1'b0, r_freeze_trace, 3'b000};
                            9'h004: r_rdata <= w_status;
                            9'h008: r_rdata <= i_dbg_wr_ptr;
                            9'h00C: r_rdata <= {31'd0, i_dbg_overflow};
                            9'h010: r_rdata <= i_crc_expected;
                            9'h014: r_rdata <= i_crc_actual;
                            9'h018: r_rdata <= w_crc_match;
                            9'h01C: r_rdata <= r_scratch;
                            9'h020: r_rdata <= BUILD_ID;
                            9'h024: r_rdata <= {{(32-TXN_COUNT_WIDTH){1'b0}}, i_beats_mismatched};

                            9'h028: r_rdata <= 32'h0;  // TIMER_CTRL is W-only
                            9'h02C: r_rdata <= {29'd0, i_timer_pass,
                                                       i_timer_running,
                                                       i_timer_done};
                            9'h030: r_rdata <= i_timer_cycles[31:0];
                            9'h034: r_rdata <= i_timer_cycles[63:32];
                            9'h038: r_rdata <= r_timer_expected_beats;
                            9'h03C: r_rdata <= {r_wr_resp_delay_cyc, r_rd_resp_delay_cyc};
                            9'h040: r_rdata <= i_timer_r_first[31:0];
                            9'h044: r_rdata <= i_timer_r_first[63:32];
                            9'h048: r_rdata <= i_timer_r_last[31:0];
                            9'h04C: r_rdata <= i_timer_r_last[63:32];
                            9'h050: r_rdata <= i_timer_w_first[31:0];
                            9'h054: r_rdata <= i_timer_w_first[63:32];
                            9'h058: r_rdata <= i_timer_w_last[31:0];
                            9'h05C: r_rdata <= i_timer_w_last[63:32];

                            9'h060: r_rdata <= r_ctrlr_cfg;
                            9'h064: r_rdata <= r_ctrlr_cap;

                            9'h100: r_rdata <= r_wr_start_addr;
                            9'h104: r_rdata <= r_wr_stride_0;
                            9'h108: r_rdata <= r_wr_stride_1;
                            9'h10C: r_rdata <= r_wr_wrap_mask_0;
                            9'h110: r_rdata <= r_wr_wrap_mask_1;
                            9'h114: r_rdata <= r_wr_blen_txn;
                            9'h118: r_rdata <= r_wr_axi_attr;
                            9'h11C: r_rdata <= r_wr_lfsr_seed;
                            9'h120: r_rdata <= r_wr_hash_seed0;
                            9'h124: r_rdata <= r_wr_hash_seed1;
                            9'h128: r_rdata <= r_wr_hash_seed2;

                            9'h180: r_rdata <= r_rd_start_addr;
                            9'h184: r_rdata <= r_rd_stride_0;
                            9'h188: r_rdata <= r_rd_stride_1;
                            9'h18C: r_rdata <= r_rd_wrap_mask_0;
                            9'h190: r_rdata <= r_rd_wrap_mask_1;
                            9'h194: r_rdata <= r_rd_blen_txn;
                            9'h198: r_rdata <= r_rd_axi_attr;
                            9'h19C: r_rdata <= r_rd_lfsr_seed;
                            9'h1A0: r_rdata <= r_rd_hash_seed0;
                            9'h1A4: r_rdata <= r_rd_hash_seed1;
                            9'h1A8: r_rdata <= r_rd_hash_seed2;

                            default: r_rdata <= 32'h0;
                        endcase
                        r_rstate <= R_RRESP;
                    end
                end
                R_RRESP: if (int_rready) r_rstate <= R_IDLE;
                default: r_rstate <= R_IDLE;
            endcase
        end
    )

    assign int_arready = (r_rstate == R_IDLE);
    assign int_rvalid  = (r_rstate == R_RRESP);
    assign int_r_pkt   = {r_rdata, 2'b00};

    // =========================================================================
    // Output assignment
    // =========================================================================
    assign o_start_wr_pulse    = r_start_wr_pulse;
    assign o_start_rd_pulse    = r_start_rd_pulse;
    assign o_clear_stats_pulse = r_clear_stats_pulse;
    assign o_freeze_trace      = r_freeze_trace;
    assign o_soft_reset_pulse  = r_soft_reset_pulse;

    assign o_timer_clear_pulse    = r_timer_clear_pulse;
    assign o_timer_expected_beats = r_timer_expected_beats;
    assign o_rd_resp_delay_cyc    = r_rd_resp_delay_cyc;
    assign o_wr_resp_delay_cyc    = r_wr_resp_delay_cyc;

    // Controller runtime cfg unpack
    // r_ctrlr_cfg: [0]memtype [15:8]t_phy_wrlat [23:16]t_rddata_en [24]rd_in_order
    assign o_memtype           = memtype_e'(r_ctrlr_cfg[0]);
    assign o_t_phy_wrlat       = r_ctrlr_cfg[15:8];
    assign o_t_rddata_en       = r_ctrlr_cfg[23:16];
    assign o_rd_in_order       = r_ctrlr_cfg[24];
    // r_ctrlr_cap: [3:0]cap_lookahead_max [7:4]cap_synth_mask
    assign o_cap_lookahead_max = r_ctrlr_cap[3:0];
    assign o_cap_synth_mask    = r_ctrlr_cap[7:4];

    // WR-engine cfg unpack
    assign o_cfg_wr_start_addr  = r_wr_start_addr[AW-1:0];
    assign o_cfg_wr_stride_0    = r_wr_stride_0[STRIDE_WIDTH-1:0];
    assign o_cfg_wr_stride_1    = r_wr_stride_1[STRIDE_WIDTH-1:0];
    assign o_cfg_wr_wrap_mask_0 = r_wr_wrap_mask_0[AW-1:0];
    assign o_cfg_wr_wrap_mask_1 = r_wr_wrap_mask_1[AW-1:0];
    assign o_cfg_wr_burst_len   = r_wr_blen_txn[BURST_LEN_WIDTH-1:0];
    assign o_cfg_wr_txn_count   = r_wr_blen_txn[TXN_COUNT_WIDTH+7:8];
    assign o_cfg_wr_gap         = r_wr_blen_txn[27:24];
    assign o_cfg_wr_axi_id      = r_wr_axi_attr[AXI_ID_WIDTH-1:0];
    assign o_cfg_wr_id_mode     = r_wr_axi_attr[5:4];
    assign o_cfg_wr_axi_size    = r_wr_axi_attr[8:6];
    assign o_cfg_wr_axi_burst   = r_wr_axi_attr[10:9];
    assign o_cfg_wr_data_mode   = r_wr_axi_attr[11];
    assign o_cfg_wr_lfsr_seed   = r_wr_lfsr_seed;
    assign o_cfg_wr_hash_seed0  = r_wr_hash_seed0;
    assign o_cfg_wr_hash_seed1  = r_wr_hash_seed1;
    assign o_cfg_wr_hash_seed2  = r_wr_hash_seed2;

    // RD-engine cfg unpack
    assign o_cfg_rd_start_addr  = r_rd_start_addr[AW-1:0];
    assign o_cfg_rd_stride_0    = r_rd_stride_0[STRIDE_WIDTH-1:0];
    assign o_cfg_rd_stride_1    = r_rd_stride_1[STRIDE_WIDTH-1:0];
    assign o_cfg_rd_wrap_mask_0 = r_rd_wrap_mask_0[AW-1:0];
    assign o_cfg_rd_wrap_mask_1 = r_rd_wrap_mask_1[AW-1:0];
    assign o_cfg_rd_burst_len   = r_rd_blen_txn[BURST_LEN_WIDTH-1:0];
    assign o_cfg_rd_txn_count   = r_rd_blen_txn[TXN_COUNT_WIDTH+7:8];
    assign o_cfg_rd_gap         = r_rd_blen_txn[27:24];
    assign o_cfg_rd_axi_id      = r_rd_axi_attr[AXI_ID_WIDTH-1:0];
    assign o_cfg_rd_id_mode     = r_rd_axi_attr[5:4];
    assign o_cfg_rd_axi_size    = r_rd_axi_attr[8:6];
    assign o_cfg_rd_axi_burst   = r_rd_axi_attr[10:9];
    assign o_cfg_rd_data_mode   = r_rd_axi_attr[11];
    assign o_cfg_rd_lfsr_seed   = r_rd_lfsr_seed;
    assign o_cfg_rd_hash_seed0  = r_rd_hash_seed0;
    assign o_cfg_rd_hash_seed1  = r_rd_hash_seed1;
    assign o_cfg_rd_hash_seed2  = r_rd_hash_seed2;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_wstrb, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : harness_csr
