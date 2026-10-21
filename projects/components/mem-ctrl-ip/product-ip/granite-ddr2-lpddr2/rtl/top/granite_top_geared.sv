// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: granite_top_geared
// Purpose: granite_top with a free host AXI data width. The controller core is
//          fixed at its natural width DW = DRAM_BEAT_WIDTH * DFI_RATE. This
//          wrapper places the repo's formally-verified AXI data-width converters
//          (axi4_dwidth_converter_wr / _rd) between a host-width AXI slave and
//          the DW-width controller, mirroring the pumice family gearing path.
//
//          This is the Granite (v2 DDR2/LPDDR2 product) top: it instantiates the
//          PeakRDL-generated granite_csr register block and drives the core's
//          timer/config ports from the CSR. Telemetry that Granite's lite SKU
//          core does not export (command history, stall/page statistics) is
//          tied off rather than wired.
//
//          GEAR-1 (HOST_AXI_DATA_WIDTH == DW): the converters are BYPASSED via a
//          generate — the host AXI connects directly to the core.
//
// Documentation: config/product_config.md ; HAS ch03/ch04, MAS AXI-DRAM gearing.
`timescale 1ns / 1ps

module granite_top_geared
    import granite_pkg::*;
    import mc_common_pkg::*;
#(
    // ---- host AXI data width (free) ----
    parameter int HOST_AXI_DATA_WIDTH = 128,
    parameter int AXI_USER_WIDTH  = 8,

    // ---- core geometry (mirror granite_core) ----
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int DRAM_BL         = 8,
    parameter int NUM_ENTRIES     = GRANITE_SEAM_N,
    parameter int RD_RET_DEPTH    = 32,
    parameter int CMD_DELAY       = 0,
    parameter int AGE_WIDTH       = 16,

    // ---- derived ----
    parameter int DW   = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int CSW  = DW / 8,
    parameter int HSW  = HOST_AXI_DATA_WIDTH / 8,
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int DFI_DATA_WIDTH = DW,
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE,
    parameter int CSR_ADDR_W     = 12,
    parameter int PHW            = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    // Granite CSR has no gear_ratio field; the A7 build is fixed at 1:2.
    parameter int GEAR_RATIO     = 1
) (
    input  logic aclk, aresetn, dfi_clk, dfi_rstn,

    // ---- register cpuif (PeakRDL passthrough) ----
    input  logic                    s_cpuif_req,
    input  logic                    s_cpuif_req_is_wr,
    input  logic [CSR_ADDR_W-1:0]   s_cpuif_addr,
    input  logic [31:0]             s_cpuif_wr_data,
    input  logic [31:0]             s_cpuif_wr_biten,
    output logic                    s_cpuif_req_stall_wr,
    output logic                    s_cpuif_req_stall_rd,
    output logic                    s_cpuif_rd_ack,
    output logic                    s_cpuif_rd_err,
    output logic [31:0]             s_cpuif_rd_data,
    output logic                    s_cpuif_wr_ack,
    output logic                    s_cpuif_wr_err,

    output logic                    init_done_o,

    // ---- host AXI4 (HOST_AXI_DATA_WIDTH) ----
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_awuser, input logic s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [HOST_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [HSW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic [AXI_USER_WIDTH-1:0] s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0] s_axi_buser, output logic s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_aruser, input logic s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [HOST_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0] s_axi_ruser, output logic s_axi_rvalid,
    input  logic           s_axi_rready,

    // ---- DFI 2.1 pin bus (straight through) ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o, dfi_ras_n_o, dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o, dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    // ===================================================================
    // HARD WIDTH CONSTRAINT — HOST_AXI_DATA_WIDTH : DFI word DW must be a
    // power-of-two ratio. Same rule and rationale as pumice_top_geared.
    // ===================================================================
    localparam int W_HI  = (HOST_AXI_DATA_WIDTH >= DW) ? HOST_AXI_DATA_WIDTH : DW;
    localparam int W_LO  = (HOST_AXI_DATA_WIDTH >= DW) ? DW : HOST_AXI_DATA_WIDTH;
    localparam int W_RAT = W_HI / W_LO;
    initial begin
        assert ((W_LO >= 1) && (W_HI % W_LO == 0) && (W_RAT == (1 << $clog2(W_RAT))))
            else $fatal(1, "granite_top_geared: HOST_AXI_DATA_WIDTH=%0d and DFI word DW=%0d must relate by a power-of-two ratio (AXI:DFI = G:1 or 1:G); got %0d:%0d.",
                HOST_AXI_DATA_WIDTH, DW, W_HI, W_LO);
    end

    // ---- core-side (DW-width) AXI nets between converters and granite_core ----
    logic [IW-1:0]  c_awid;   logic [AW-1:0] c_awaddr;
    logic [7:0]     c_awlen;  logic [2:0]    c_awsize;
    logic [1:0]     c_awburst;logic          c_awlock;
    logic [3:0]     c_awcache;logic [2:0]    c_awprot;
    logic [3:0]     c_awqos;  logic [3:0]    c_awregion;
    logic [AXI_USER_WIDTH-1:0] c_awuser; logic c_awvalid, c_awready;
    logic [DW-1:0]  c_wdata;  logic [CSW-1:0] c_wstrb;
    logic           c_wlast;  logic [AXI_USER_WIDTH-1:0] c_wuser; logic c_wvalid, c_wready;
    logic [IW-1:0]  c_bid;    logic [1:0]    c_bresp;
    logic [AXI_USER_WIDTH-1:0] c_buser; logic c_bvalid, c_bready;
    logic [IW-1:0]  c_arid;   logic [AW-1:0] c_araddr;
    logic [7:0]     c_arlen;  logic [2:0]    c_arsize;
    logic [1:0]     c_arburst;logic          c_arlock;
    logic [3:0]     c_arcache;logic [2:0]    c_arprot;
    logic [3:0]     c_arqos;  logic [3:0]    c_arregion;
    logic [AXI_USER_WIDTH-1:0] c_aruser; logic c_arvalid, c_arready;
    logic [IW-1:0]  c_rid;    logic [DW-1:0] c_rdata;
    logic [1:0]     c_rresp;  logic          c_rlast;
    logic [AXI_USER_WIDTH-1:0] c_ruser; logic c_rvalid, c_rready;

    generate
    if (HOST_AXI_DATA_WIDTH == DW) begin : g_direct
        assign c_awid=s_axi_awid; assign c_awaddr=s_axi_awaddr; assign c_awlen=s_axi_awlen;
        assign c_awsize=s_axi_awsize; assign c_awburst=s_axi_awburst; assign c_awlock=s_axi_awlock;
        assign c_awcache=s_axi_awcache; assign c_awprot=s_axi_awprot; assign c_awqos=s_axi_awqos;
        assign c_awregion=s_axi_awregion; assign c_awuser=s_axi_awuser; assign c_awvalid=s_axi_awvalid;
        assign s_axi_awready=c_awready;
        assign c_wdata=s_axi_wdata; assign c_wstrb=s_axi_wstrb; assign c_wlast=s_axi_wlast;
        assign c_wuser=s_axi_wuser; assign c_wvalid=s_axi_wvalid; assign s_axi_wready=c_wready;
        assign s_axi_bid=c_bid; assign s_axi_bresp=c_bresp; assign s_axi_buser=c_buser;
        assign s_axi_bvalid=c_bvalid; assign c_bready=s_axi_bready;
        assign c_arid=s_axi_arid; assign c_araddr=s_axi_araddr; assign c_arlen=s_axi_arlen;
        assign c_arsize=s_axi_arsize; assign c_arburst=s_axi_arburst; assign c_arlock=s_axi_arlock;
        assign c_arcache=s_axi_arcache; assign c_arprot=s_axi_arprot; assign c_arqos=s_axi_arqos;
        assign c_arregion=s_axi_arregion; assign c_aruser=s_axi_aruser; assign c_arvalid=s_axi_arvalid;
        assign s_axi_arready=c_arready;
        assign s_axi_rid=c_rid; assign s_axi_rdata=c_rdata; assign s_axi_rresp=c_rresp;
        assign s_axi_rlast=c_rlast; assign s_axi_ruser=c_ruser; assign s_axi_rvalid=c_rvalid;
        assign c_rready=s_axi_rready;
    end else begin : g_conv
        axi4_dwidth_converter_wr #(
            .S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH),
            .M_AXI_DATA_WIDTH(DW),
            .AXI_ID_WIDTH    (IW),
            .AXI_ADDR_WIDTH  (AW),
            .AXI_USER_WIDTH  (AXI_USER_WIDTH)
        ) u_wr_conv (
            .aclk   (aclk),
            .aresetn(aresetn),
            .s_axi_awid    (s_axi_awid),
            .s_axi_awaddr  (s_axi_awaddr),
            .s_axi_awlen   (s_axi_awlen),
            .s_axi_awsize  (s_axi_awsize),
            .s_axi_awburst (s_axi_awburst),
            .s_axi_awlock  (s_axi_awlock),
            .s_axi_awcache (s_axi_awcache),
            .s_axi_awprot  (s_axi_awprot),
            .s_axi_awqos   (s_axi_awqos),
            .s_axi_awregion(s_axi_awregion),
            .s_axi_awuser  (s_axi_awuser),
            .s_axi_awvalid (s_axi_awvalid),
            .s_axi_awready (s_axi_awready),
            .s_axi_wdata   (s_axi_wdata),
            .s_axi_wstrb   (s_axi_wstrb),
            .s_axi_wlast   (s_axi_wlast),
            .s_axi_wuser   (s_axi_wuser),
            .s_axi_wvalid  (s_axi_wvalid),
            .s_axi_wready  (s_axi_wready),
            .s_axi_bid     (s_axi_bid),
            .s_axi_bresp   (s_axi_bresp),
            .s_axi_buser   (s_axi_buser),
            .s_axi_bvalid  (s_axi_bvalid),
            .s_axi_bready  (s_axi_bready),
            .m_axi_awid    (c_awid),
            .m_axi_awaddr  (c_awaddr),
            .m_axi_awlen   (c_awlen),
            .m_axi_awsize  (c_awsize),
            .m_axi_awburst (c_awburst),
            .m_axi_awlock  (c_awlock),
            .m_axi_awcache (c_awcache),
            .m_axi_awprot  (c_awprot),
            .m_axi_awqos   (c_awqos),
            .m_axi_awregion(c_awregion),
            .m_axi_awuser  (c_awuser),
            .m_axi_awvalid (c_awvalid),
            .m_axi_awready (c_awready),
            .m_axi_wdata   (c_wdata),
            .m_axi_wstrb   (c_wstrb),
            .m_axi_wlast   (c_wlast),
            .m_axi_wuser   (c_wuser),
            .m_axi_wvalid  (c_wvalid),
            .m_axi_wready  (c_wready),
            .m_axi_bid     (c_bid),
            .m_axi_bresp   (c_bresp),
            .m_axi_buser   (c_buser),
            .m_axi_bvalid  (c_bvalid),
            .m_axi_bready  (c_bready)
        );

        axi4_dwidth_converter_rd #(
            .S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH),
            .M_AXI_DATA_WIDTH(DW),
            .AXI_ID_WIDTH    (IW),
            .AXI_ADDR_WIDTH  (AW),
            .AXI_USER_WIDTH  (AXI_USER_WIDTH)
        ) u_rd_conv (
            .aclk   (aclk),
            .aresetn(aresetn),
            .s_axi_arid    (s_axi_arid),
            .s_axi_araddr  (s_axi_araddr),
            .s_axi_arlen   (s_axi_arlen),
            .s_axi_arsize  (s_axi_arsize),
            .s_axi_arburst (s_axi_arburst),
            .s_axi_arlock  (s_axi_arlock),
            .s_axi_arcache (s_axi_arcache),
            .s_axi_arprot  (s_axi_arprot),
            .s_axi_arqos   (s_axi_arqos),
            .s_axi_arregion(s_axi_arregion),
            .s_axi_aruser  (s_axi_aruser),
            .s_axi_arvalid (s_axi_arvalid),
            .s_axi_arready (s_axi_arready),
            .s_axi_rid     (s_axi_rid),
            .s_axi_rdata   (s_axi_rdata),
            .s_axi_rresp   (s_axi_rresp),
            .s_axi_rlast   (s_axi_rlast),
            .s_axi_ruser   (s_axi_ruser),
            .s_axi_rvalid  (s_axi_rvalid),
            .s_axi_rready  (s_axi_rready),
            .m_axi_arid    (c_arid),
            .m_axi_araddr  (c_araddr),
            .m_axi_arlen   (c_arlen),
            .m_axi_arsize  (c_arsize),
            .m_axi_arburst (c_arburst),
            .m_axi_arlock  (c_arlock),
            .m_axi_arcache (c_arcache),
            .m_axi_arprot  (c_arprot),
            .m_axi_arqos   (c_arqos),
            .m_axi_arregion(c_arregion),
            .m_axi_aruser  (c_aruser),
            .m_axi_arvalid (c_arvalid),
            .m_axi_arready (c_arready),
            .m_axi_rid     (c_rid),
            .m_axi_rdata   (c_rdata),
            .m_axi_rresp   (c_rresp),
            .m_axi_rlast   (c_rlast),
            .m_axi_ruser   (c_ruser),
            .m_axi_rvalid  (c_rvalid),
            .m_axi_rready  (c_rready)
        );
    end
    endgenerate

    // ---- CSR register block (PeakRDL) ----
    granite_csr_pkg::granite_csr__in_t  hwif_in;
    granite_csr_pkg::granite_csr__out_t hwif_out;

    logic [DFI_DATA_WIDTH-1:0] w_mrr32_data, w_mrr40_data;
    logic                      w_cal_busy, w_cal_done, w_cal_err;
    logic                      w_zq_busy, w_zq_overdue;
    logic [15:0]               w_zqcs_total;

    always_comb begin
        hwif_in = '{default: '0};
        // Live status back to CSR
        hwif_in.STATUS.init_done.next      = init_done_o;
        hwif_in.CAL_STATUS.zq_busy.next    = w_zq_busy;
        hwif_in.CAL_STATUS.cal_busy.next   = w_cal_busy;
        hwif_in.CAL_STATUS.cal_done.next   = w_cal_done;
        hwif_in.CAL_STATUS.cal_err.next    = w_cal_err;
        hwif_in.CAL_STATUS.zq_overdue.next = w_zq_overdue;
        hwif_in.CAL_STATUS.zqcs_total.next = w_zqcs_total;
        for (int b = 0; b < (DFI_DATA_WIDTH / 32); b++) begin
            hwif_in.CAL_MRR32_DATA[b].VAL.VAL.next = w_mrr32_data[b*32 +: 32];
            hwif_in.CAL_MRR40_DATA[b].VAL.VAL.next = w_mrr40_data[b*32 +: 32];
        end
        // Telemetry/statistics that Granite core does not export: read as zero.
    end

    granite_csr u_csr (
        .clk                 (aclk),
        .rst                 (~aresetn),
        .s_cpuif_req         (s_cpuif_req),
        .s_cpuif_req_is_wr   (s_cpuif_req_is_wr),
        .s_cpuif_addr        (s_cpuif_addr),
        .s_cpuif_wr_data     (s_cpuif_wr_data),
        .s_cpuif_wr_biten    (s_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr),
        .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd),
        .s_cpuif_rd_ack      (s_cpuif_rd_ack),
        .s_cpuif_rd_err      (s_cpuif_rd_err),
        .s_cpuif_rd_data     (s_cpuif_rd_data),
        .s_cpuif_wr_ack      (s_cpuif_wr_ack),
        .s_cpuif_wr_err      (s_cpuif_wr_err),
        .hwif_in             (hwif_in),
        .hwif_out            (hwif_out)
    );

    // ---- config from CSR (by-name hwif_out) ----
    memtype_e         w_memtype;
    page_policy_e     w_page_policy;

    assign w_memtype = (hwif_out.PHY_TIMING.memtype.value == 1'b0)
                       ? MEMTYPE_DDR2 : MEMTYPE_LPDDR2;

    localparam page_policy_e PAGE_POLICY_BUILD_DEFAULT = PAGE_POLICY_OPEN;
    always_comb begin
        unique case (hwif_out.REFRESH_TUNING.page_policy_or.value)
            2'd1:    w_page_policy = PAGE_POLICY_OPEN;
            2'd2:    w_page_policy = PAGE_POLICY_CLOSE;
            default: w_page_policy = PAGE_POLICY_BUILD_DEFAULT;
        endcase
    end

    // ---- tRTW FLOOR: same protection as pumice_top (BUG-014) ----
    localparam int RD_EN_CYC_TOP = (DRAM_BL + DFI_RATE - 1) / DFI_RATE;
    logic [7:0] w_t_rtw_floor, w_t_rtw_eff;
    assign w_t_rtw_floor = 8'(hwif_out.PHY_TIMING.t_rddata_en.value)
                         + 8'(RD_EN_CYC_TOP)
                         - 8'(hwif_out.PHY_TIMING.t_phy_wrlat.value);
    assign w_t_rtw_eff   = (8'(hwif_out.TIMINGS_RTP_RTW.tRTW.value) > w_t_rtw_floor)
                         ?  8'(hwif_out.TIMINGS_RTP_RTW.tRTW.value)
                         :  w_t_rtw_floor;

    // ---- controller core (fixed DW width) ----
    granite_core #(
        .AXI_ID_WIDTH     (IW),
        .AXI_ADDR_WIDTH   (AW),
        .UW               (AXI_USER_WIDTH),   // was left at the core's 1: user bits cut to 1, B/R user's upper bits undriven
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .DFI_RATE         (DFI_RATE),
        .DRAM_BEAT_WIDTH  (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH(DRAM_DEVICE_WIDTH),
        .DRAM_BL          (DRAM_BL),
        .NUM_ENTRIES      (NUM_ENTRIES),
        .RD_RET_DEPTH     (RD_RET_DEPTH),
        .CMD_DELAY        (CMD_DELAY),
        .AGE_WIDTH        (AGE_WIDTH)
    ) u_core (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .dfi_clk            (dfi_clk),
        .dfi_rstn           (dfi_rstn),
        .memtype_i          (w_memtype),
        .page_policy_i      (w_page_policy),
        .page_mode_i        (hwif_out.PAGE_POLICY_CFG.policy_mode.value),
        .page_tr_init_i     (hwif_out.PAGE_TIMEOUT_CFG.tr_init.value),
        .sched_order_mode_i (hwif_out.SCHED_POLICY.order_mode.value),
        .sched_row_sel_i    (hwif_out.SCHED_POLICY.row_sel.value),
        .sched_col_sel_i    (hwif_out.SCHED_POLICY.col_sel.value),
        .sched_access_pref_i(hwif_out.SCHED_POLICY.access_pref.value),
        .sched_wr_high_wm_i (hwif_out.SCHED_WR_WM.wr_high_wm.value),
        .sched_wr_batch_max_i(8'd0),   // no field in Granite CSR
        .sched_wr_low_wm_i  (hwif_out.SCHED_WR_WM.wr_low_wm.value),
        .sched_prio_sub_i   (hwif_out.SCHED_POLICY.prio_sub.value),
        .sched_qos_en_i     (hwif_out.SCHED_POLICY.qos_en.value),
        .sched_age_thresh_i (hwif_out.SCHED_POLICY.age_thresh.value),
        .bank_lsb_i         (hwif_out.ADDR_MAP.bank_lsb.value),
        .hash_en_i          (hwif_out.ADDR_MAP.hash_en.value),
        .hash_seed_i        (hwif_out.ADDR_MAP.hash_seed.value),
        .t_rcd_i            (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRCD.value),
        .t_rp_i             (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRP.value),
        .t_ras_i            (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRAS.value),
        .t_rc_i             (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRC.value),
        .t_wr_i             (hwif_out.TIMINGS_CL_CWL_WR.tWR.value),
        .t_rtp_i            (hwif_out.TIMINGS_RTP_RTW.tRTP.value),
        .t_faw_i            (hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tFAW.value),
        .t_rrd_i            (hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tRRD.value),
        .t_wtr_i            (hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tWTR.value),
        .t_rtw_i            (w_t_rtw_eff),
        .t_ccd_i            (hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tCCD.value),
        .t_refi_i           (hwif_out.TIMINGS_RFC_REFI.tREFI.value),
        .refi_reload_i      (1'b0),
        .t_rfc_i            (hwif_out.TIMINGS_RFC_REFI.tRFC.value),
        .refresh_burst_i    (hwif_out.PHY_TIMING.refresh_burst.value),
        // Granite_core already ties ref_postpone/pull-in/mode internally.
        // Granite CSR has no per-bank refresh timing window; tie off.
        .ref_trefi_pb_i     ('0),
        .ref_trfc_pb_i      ('0),
        .t_init_wait_i      (hwif_out.INIT_TIMING0.t_init_wait.value),
        .t_dll_wait_i       (hwif_out.INIT_TIMING0.t_dll_wait.value),
        .t_mrd_wait_i       (hwif_out.INIT_TIMING1.t_mrd_wait.value),
        .t_rp_wait_i        (hwif_out.INIT_TIMING1.t_rp_wait.value),
        .t_rfc_wait_i       (hwif_out.INIT_TIMING1.t_rfc_wait.value),
        .mr0_i              (hwif_out.MR0.VAL.value),
        .mr1_i              (hwif_out.MR1.VAL.value),
        .mr2_i              (hwif_out.MR2.VAL.value),
        .mr3_i              (hwif_out.MR3.VAL.value),
        .lp_mr1_op_i        (hwif_out.LP_MR1_OP.VAL.value),
        .lp_mr2_op_i        (hwif_out.LP_MR2_OP.VAL.value),
        .lp_mr3_op_i        (hwif_out.LP_MR3_OP.VAL.value),
        .init_restart_i     (hwif_out.CTRL.init_force_restart.value),
        .rd_phase_i         (hwif_out.DFI_PHASE.rd_phase.value[PHW-1:0]),
        .wr_phase_i         (hwif_out.DFI_PHASE.wr_phase.value[PHW-1:0]),
        .t_phy_wrlat_i      (hwif_out.PHY_TIMING.t_phy_wrlat.value),
        .t_rddata_en_i      (hwif_out.PHY_TIMING.t_rddata_en.value),
        .gear_i             (2'(GEAR_RATIO)),
        .bl_i               (hwif_out.DFI_PHASE.bl.value),
        .cl_o               (),
        .cwl_o              (),
        .bl_o               (),
        .init_done_o        (init_done_o),
        .zq_en_i            (hwif_out.CAL_CTRL.zq_en.value),
        .zq_defer_en_i      (hwif_out.CAL_CTRL.zq_defer_en.value),
        .zq_interval_i      (hwif_out.CAL_ZQ_INTERVAL.VAL.value),
        .t_zqcs_i           (hwif_out.CAL_ZQ_TIMING.t_zqcs.value),
        .t_zqcl_i           (hwif_out.CAL_ZQ_TIMING.t_zqcl.value),
        .zq_overdue_max_i   (hwif_out.CAL_CTRL.zq_overdue_max.value),
        .cal_start_i        (hwif_out.CAL_CTRL.cal_start.swmod),
        .cal_abort_i        (hwif_out.CAL_CTRL.cal_abort.swmod),
        .t_mrr_i            (hwif_out.CAL_TRAIN_TIMING.t_mrr.value),
        .t_readout_i        (hwif_out.CAL_TRAIN_TIMING.t_readout.value),
        .mrr32_data_o       (w_mrr32_data),
        .mrr40_data_o       (w_mrr40_data),
        .cal_busy_o         (w_cal_busy),
        .cal_done_o         (w_cal_done),
        .cal_err_o          (w_cal_err),
        .zq_busy_o          (w_zq_busy),
        .zq_overdue_o       (w_zq_overdue),
        .zqcs_total_o       (w_zqcs_total),
        .s_axi_awid         (c_awid),
        .s_axi_awaddr       (c_awaddr),
        .s_axi_awlen        (c_awlen),
        .s_axi_awsize       (c_awsize),
        .s_axi_awburst      (c_awburst),
        .s_axi_awlock       (c_awlock),
        .s_axi_awcache      (c_awcache),
        .s_axi_awprot       (c_awprot),
        .s_axi_awqos        (c_awqos),
        .s_axi_awregion     (c_awregion),
        .s_axi_awuser       (c_awuser),
        .s_axi_awvalid      (c_awvalid),
        .s_axi_awready      (c_awready),
        .s_axi_wdata        (c_wdata),
        .s_axi_wstrb        (c_wstrb),
        .s_axi_wlast        (c_wlast),
        .s_axi_wuser        (c_wuser),
        .s_axi_wvalid       (c_wvalid),
        .s_axi_wready       (c_wready),
        .s_axi_bid          (c_bid),
        .s_axi_bresp        (c_bresp),
        .s_axi_buser        (c_buser),
        .s_axi_bvalid       (c_bvalid),
        .s_axi_bready       (c_bready),
        .s_axi_arid         (c_arid),
        .s_axi_araddr       (c_araddr),
        .s_axi_arlen        (c_arlen),
        .s_axi_arsize       (c_arsize),
        .s_axi_arburst      (c_arburst),
        .s_axi_arlock       (c_arlock),
        .s_axi_arcache      (c_arcache),
        .s_axi_arprot       (c_arprot),
        .s_axi_arqos        (c_arqos),
        .s_axi_arregion     (c_arregion),
        .s_axi_aruser       (c_aruser),
        .s_axi_arvalid      (c_arvalid),
        .s_axi_arready      (c_arready),
        .s_axi_rid          (c_rid),
        .s_axi_rdata        (c_rdata),
        .s_axi_rresp        (c_rresp),
        .s_axi_rlast        (c_rlast),
        .s_axi_ruser        (c_ruser),
        .s_axi_rvalid       (c_rvalid),
        .s_axi_rready       (c_rready),
        .dfi_address_o      (dfi_address_o),
        .dfi_bank_o         (dfi_bank_o),
        .dfi_cas_n_o        (dfi_cas_n_o),
        .dfi_ras_n_o        (dfi_ras_n_o),
        .dfi_we_n_o         (dfi_we_n_o),
        .dfi_cs_n_o         (dfi_cs_n_o),
        .dfi_odt_o          (dfi_odt_o),
        .dfi_wrdata_o       (dfi_wrdata_o),
        .dfi_wrdata_en_o    (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o  (dfi_wrdata_mask_o),
        .dfi_rddata_en_o    (dfi_rddata_en_o),
        .dfi_rddata_i       (dfi_rddata_i),
        .dfi_rddata_valid_i (dfi_rddata_valid_i),
        .dfi_init_start_o   (dfi_init_start_o),
        .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : granite_top_geared
