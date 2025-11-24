`timescale 1ns / 1ps

//-----------------------------------------------------------------------------
// Module: stream_top_mon_ch8
// Description:
//   Top-level wrapper for STREAM core with 8 channels (monitors ENABLED).
//
//   Integration hierarchy:
//     APB Interface
//       → peakrdl_to_cmdrsp (APB → CMD/RSP)
//       → Address Demux (route to apbtodescr or stream_regs)
//         → apbtodescr (channel kick-off, 0x000-0x01F)
//         → stream_regs (PeakRDL registers, 0x100-0x3FF)
//       → stream_config_block (register mapping)
//       → stream_core (monitors ENABLED)
//       → MonBus output for debug/trace
//
//   Address Map:
//     0x000-0x01F: Channel kick-off (apbtodescr)
//     0x100-0x3FF: Configuration registers (PeakRDL)
//
//   Features:
//     - 8 independent channels
//     - APB4 configuration interface
//     - 3 AXI4 masters (descriptor, read data, write data)
//     - Monitors ENABLED (descriptor AXI, read engine, write engine)
//     - MonBus output for system-level monitoring
//
// Parameters:
//   NUM_CHANNELS: Number of DMA channels (fixed at 8)
//   DATA_WIDTH: AXI data bus width (512 bits)
//   ADDR_WIDTH: AXI address width (64 bits)
//   SRAM_DEPTH: Internal SRAM buffer depth (4096)
//   APB_ADDR_WIDTH: APB address width (12 bits for 4KB space)
//   APB_DATA_WIDTH: APB data width (32 bits)
//   MONBUS_WIDTH: MonBus packet width (64 bits)
//
//-----------------------------------------------------------------------------

`include "stream_imports.svh"
`include "reset_defs.svh"

module stream_top_mon_ch8 #(
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int ADDR_WIDTH = 64,
    parameter int SRAM_DEPTH = 4096,
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int MONBUS_WIDTH = 64
) (
    //-------------------------------------------------------------------------
    // Clock and Reset
    //-------------------------------------------------------------------------
    input  logic                                    aclk,
    input  logic                                    aresetn,

    // Optional separate APB clock domain
    input  logic                                    pclk,
    input  logic                                    presetn,

    //-------------------------------------------------------------------------
    // APB4 Configuration Interface
    //-------------------------------------------------------------------------
    input  logic [APB_ADDR_WIDTH-1:0]               s_apb_paddr,
    input  logic                                    s_apb_psel,
    input  logic                                    s_apb_penable,
    input  logic                                    s_apb_pwrite,
    input  logic [APB_DATA_WIDTH-1:0]               s_apb_pwdata,
    input  logic [(APB_DATA_WIDTH/8)-1:0]           s_apb_pstrb,
    output logic [APB_DATA_WIDTH-1:0]               s_apb_prdata,
    output logic                                    s_apb_pready,
    output logic                                    s_apb_pslverr,

    //-------------------------------------------------------------------------
    // AXI4 Master - Descriptor Fetch (256-bit)
    //-------------------------------------------------------------------------
    // Read Address Channel
    output logic [ADDR_WIDTH-1:0]                   m_axi_desc_araddr,
    output logic [7:0]                              m_axi_desc_arlen,
    output logic [2:0]                              m_axi_desc_arsize,
    output logic [1:0]                              m_axi_desc_arburst,
    output logic                                    m_axi_desc_arvalid,
    input  logic                                    m_axi_desc_arready,

    // Read Data Channel
    input  logic [255:0]                            m_axi_desc_rdata,
    input  logic [1:0]                              m_axi_desc_rresp,
    input  logic                                    m_axi_desc_rlast,
    input  logic                                    m_axi_desc_rvalid,
    output logic                                    m_axi_desc_rready,

    //-------------------------------------------------------------------------
    // AXI4 Master - Data Read (parameterizable width)
    //-------------------------------------------------------------------------
    // Read Address Channel
    output logic [ADDR_WIDTH-1:0]                   m_axi_rd_araddr,
    output logic [7:0]                              m_axi_rd_arlen,
    output logic [2:0]                              m_axi_rd_arsize,
    output logic [1:0]                              m_axi_rd_arburst,
    output logic                                    m_axi_rd_arvalid,
    input  logic                                    m_axi_rd_arready,

    // Read Data Channel
    input  logic [DATA_WIDTH-1:0]                   m_axi_rd_rdata,
    input  logic [1:0]                              m_axi_rd_rresp,
    input  logic                                    m_axi_rd_rlast,
    input  logic                                    m_axi_rd_rvalid,
    output logic                                    m_axi_rd_rready,

    //-------------------------------------------------------------------------
    // AXI4 Master - Data Write (parameterizable width)
    //-------------------------------------------------------------------------
    // Write Address Channel
    output logic [ADDR_WIDTH-1:0]                   m_axi_wr_awaddr,
    output logic [7:0]                              m_axi_wr_awlen,
    output logic [2:0]                              m_axi_wr_awsize,
    output logic [1:0]                              m_axi_wr_awburst,
    output logic                                    m_axi_wr_awvalid,
    input  logic                                    m_axi_wr_awready,

    // Write Data Channel
    output logic [DATA_WIDTH-1:0]                   m_axi_wr_wdata,
    output logic [(DATA_WIDTH/8)-1:0]               m_axi_wr_wstrb,
    output logic                                    m_axi_wr_wlast,
    output logic                                    m_axi_wr_wvalid,
    input  logic                                    m_axi_wr_wready,

    // Write Response Channel
    input  logic [1:0]                              m_axi_wr_bresp,
    input  logic                                    m_axi_wr_bvalid,
    output logic                                    m_axi_wr_bready,

    //-------------------------------------------------------------------------
    // MonBus Output
    //-------------------------------------------------------------------------
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output logic [MONBUS_WIDTH-1:0]                 mon_packet,

    //-------------------------------------------------------------------------
    // Interrupt Output
    //-------------------------------------------------------------------------
    output logic [NUM_CHANNELS-1:0]                 channel_interrupt
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    //-------------------------------------------------------------------------
    // APB CDC (if needed) - synchronize APB to AXI clock domain
    //-------------------------------------------------------------------------
    logic [APB_ADDR_WIDTH-1:0]  apb_cdc_paddr;
    logic                       apb_cdc_psel;
    logic                       apb_cdc_penable;
    logic                       apb_cdc_pwrite;
    logic [APB_DATA_WIDTH-1:0]  apb_cdc_pwdata;
    logic [(APB_DATA_WIDTH/8)-1:0] apb_cdc_pstrb;
    logic [APB_DATA_WIDTH-1:0]  apb_cdc_prdata;
    logic                       apb_cdc_pready;
    logic                       apb_cdc_pslverr;

    //-------------------------------------------------------------------------
    // CMD/RSP Interface - from peakrdl_to_cmdrsp
    //-------------------------------------------------------------------------
    logic                       cmd_valid;
    logic                       cmd_ready;
    logic                       cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]  cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]  cmd_pwdata;
    logic [(APB_DATA_WIDTH/8)-1:0] cmd_pstrb;

    logic                       rsp_valid;
    logic                       rsp_ready;
    logic [APB_DATA_WIDTH-1:0]  rsp_prdata;
    logic                       rsp_pslverr;

    //-------------------------------------------------------------------------
    // Routed CMD/RSP - after address demux
    //-------------------------------------------------------------------------
    // To apbtodescr (kick-off)
    logic                       kickoff_cmd_valid;
    logic                       kickoff_cmd_ready;
    logic [APB_ADDR_WIDTH-1:0]  kickoff_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]  kickoff_cmd_pwdata;
    logic                       kickoff_cmd_pwrite;
    logic [(APB_DATA_WIDTH/8)-1:0] kickoff_cmd_pstrb;

    logic                       kickoff_rsp_valid;
    logic                       kickoff_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]  kickoff_rsp_prdata;
    logic                       kickoff_rsp_pslverr;

    // To stream_regs (PeakRDL)
    logic                       regs_cmd_valid;
    logic                       regs_cmd_ready;
    logic [APB_ADDR_WIDTH-1:0]  regs_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]  regs_cmd_pwdata;
    logic                       regs_cmd_pwrite;
    logic [(APB_DATA_WIDTH/8)-1:0] regs_cmd_pstrb;

    logic                       regs_rsp_valid;
    logic                       regs_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]  regs_rsp_prdata;
    logic                       regs_rsp_pslverr;

    //-------------------------------------------------------------------------
    // Address Decode
    //-------------------------------------------------------------------------
    logic cmd_to_kickoff;
    logic cmd_to_regs;
    logic r_last_access_kickoff;  // Track which block was accessed

    //-------------------------------------------------------------------------
    // Descriptor Kick-off Signals
    //-------------------------------------------------------------------------
    logic [NUM_CHANNELS-1:0]                desc_apb_valid;
    logic [NUM_CHANNELS-1:0]                desc_apb_ready;
    logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] desc_apb_addr;

    //-------------------------------------------------------------------------
    // PeakRDL Register Outputs (placeholder - will connect once generated)
    //-------------------------------------------------------------------------
    // NOTE: These signals will be driven by stream_regs (PeakRDL-generated)
    // For now, tied to safe defaults
    logic        reg_global_ctrl_global_en;
    logic [7:0]  reg_channel_enable_ch_en;
    logic [7:0]  reg_channel_reset_ch_rst;
    // ... (see stream_config_block.sv for complete list)
    // TODO: Connect all ~89 register output signals including monitor configs

    //-------------------------------------------------------------------------
    // Configuration Signals - from stream_config_block
    //-------------------------------------------------------------------------
    // Core configuration
    logic [NUM_CHANNELS-1:0]                cfg_channel_enable;
    logic [NUM_CHANNELS-1:0]                cfg_channel_reset;
    logic [15:0]                            cfg_sched_timeout_cycles;
    logic                                   cfg_sched_timeout_enable;
    logic                                   cfg_desceng_prefetch;
    logic [3:0]                             cfg_desceng_fifo_thresh;
    logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr0_base;
    logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr1_base;
    logic [1:0]                             cfg_axi_rd_burst_type;
    logic [7:0]                             cfg_axi_rd_max_burst_len;
    logic [1:0]                             cfg_axi_wr_burst_type;
    logic [7:0]                             cfg_axi_wr_max_burst_len;
    logic [NUM_CHANNELS-1:0][7:0]           cfg_perf_channel_id;

    // Monitor configuration - Descriptor AXI
    logic                                   cfg_desc_mon_enable;
    logic                                   cfg_desc_mon_err_enable;
    logic [31:0]                            cfg_desc_mon_timeout_cycles;
    logic                                   cfg_desc_mon_timeout_enable;
    logic                                   cfg_desc_mon_perf_enable;
    logic                                   cfg_desc_mon_compl_enable;
    logic                                   cfg_desc_mon_debug_enable;
    logic [7:0]                             cfg_desc_mon_pkt_mask;
    logic [7:0]                             cfg_desc_mon_timeout_mask;
    logic [7:0]                             cfg_desc_mon_compl_mask;

    // Monitor configuration - Read Engine
    logic                                   cfg_rdeng_mon_enable;
    logic                                   cfg_rdeng_mon_err_enable;
    logic [31:0]                            cfg_rdeng_mon_timeout_cycles;
    logic                                   cfg_rdeng_mon_timeout_enable;
    logic                                   cfg_rdeng_mon_perf_enable;
    logic                                   cfg_rdeng_mon_compl_enable;
    logic                                   cfg_rdeng_mon_debug_enable;
    logic [7:0]                             cfg_rdeng_mon_pkt_mask;
    logic [7:0]                             cfg_rdeng_mon_timeout_mask;
    logic [7:0]                             cfg_rdeng_mon_compl_mask;

    // Monitor configuration - Write Engine
    logic                                   cfg_wreng_mon_enable;
    logic                                   cfg_wreng_mon_err_enable;
    logic [31:0]                            cfg_wreng_mon_timeout_cycles;
    logic                                   cfg_wreng_mon_timeout_enable;
    logic                                   cfg_wreng_mon_perf_enable;
    logic                                   cfg_wreng_mon_compl_enable;
    logic                                   cfg_wreng_mon_debug_enable;
    logic [7:0]                             cfg_wreng_mon_pkt_mask;
    logic [7:0]                             cfg_wreng_mon_timeout_mask;
    logic [7:0]                             cfg_wreng_mon_compl_mask;

    //=========================================================================
    // APB Clock Domain Crossing (if pclk != aclk)
    //=========================================================================
    // TODO: Add apb_slave_cdc instantiation when pclk != aclk
    // For now, assume same clock domain
    assign apb_cdc_paddr   = s_apb_paddr;
    assign apb_cdc_psel    = s_apb_psel;
    assign apb_cdc_penable = s_apb_penable;
    assign apb_cdc_pwrite  = s_apb_pwrite;
    assign apb_cdc_pwdata  = s_apb_pwdata;
    assign apb_cdc_pstrb   = s_apb_pstrb;
    assign s_apb_prdata    = apb_cdc_prdata;
    assign s_apb_pready    = apb_cdc_pready;
    assign s_apb_pslverr   = apb_cdc_pslverr;

    //=========================================================================
    // APB to CMD/RSP Conversion
    //=========================================================================
    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(APB_ADDR_WIDTH),
        .DATA_WIDTH(APB_DATA_WIDTH)
    ) u_peakrdl_converter (
        .clk            (aclk),
        .rst_n          (aresetn),

        // APB Interface (from CDC)
        .paddr          (apb_cdc_paddr),
        .psel           (apb_cdc_psel),
        .penable        (apb_cdc_penable),
        .pwrite         (apb_cdc_pwrite),
        .pwdata         (apb_cdc_pwdata),
        .pstrb          (apb_cdc_pstrb),
        .prdata         (apb_cdc_prdata),
        .pready         (apb_cdc_pready),
        .pslverr        (apb_cdc_pslverr),

        // CMD/RSP Interface
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_pwrite     (cmd_pwrite),
        .cmd_paddr      (cmd_paddr),
        .cmd_pwdata     (cmd_pwdata),
        .cmd_pstrb      (cmd_pstrb),

        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_prdata     (rsp_prdata),
        .rsp_pslverr    (rsp_pslverr)
    );

    //=========================================================================
    // Address Demux Logic
    //=========================================================================
    // Address Map:
    //   0x000-0x01F: Channel kick-off (apbtodescr)
    //   0x100-0x3FF: Configuration registers (PeakRDL)

    // Decode based on address bits
    assign cmd_to_kickoff = (cmd_paddr[11:5] == 7'h00);  // 0x00-0x1F
    assign cmd_to_regs    = (cmd_paddr[11:8] >= 4'h1);   // 0x100+

    // Route command valid
    assign kickoff_cmd_valid = cmd_valid && cmd_to_kickoff;
    assign regs_cmd_valid    = cmd_valid && cmd_to_regs;

    // Route command signals
    assign kickoff_cmd_paddr  = cmd_paddr;
    assign kickoff_cmd_pwdata = cmd_pwdata;
    assign kickoff_cmd_pwrite = cmd_pwrite;
    assign kickoff_cmd_pstrb  = cmd_pstrb;

    assign regs_cmd_paddr  = cmd_paddr;
    assign regs_cmd_pwdata = cmd_pwdata;
    assign regs_cmd_pwrite = cmd_pwrite;
    assign regs_cmd_pstrb  = cmd_pstrb;

    // Arbitrate command ready
    assign cmd_ready = cmd_to_kickoff ? kickoff_cmd_ready :
                       cmd_to_regs    ? regs_cmd_ready :
                       1'b0;  // Default: not ready

    // Track which block was accessed for response routing
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_last_access_kickoff <= 1'b0;
        end else begin
            if (cmd_valid && cmd_ready) begin
                r_last_access_kickoff <= cmd_to_kickoff;
            end
        end
    )

    // Response routing (mux based on last access)
    always_comb begin
        if (r_last_access_kickoff) begin
            rsp_valid   = kickoff_rsp_valid;
            rsp_prdata  = kickoff_rsp_prdata;
            rsp_pslverr = kickoff_rsp_pslverr;
            kickoff_rsp_ready = rsp_ready;
            regs_rsp_ready    = 1'b0;
        end else begin
            rsp_valid   = regs_rsp_valid;
            rsp_prdata  = regs_rsp_prdata;
            rsp_pslverr = regs_rsp_pslverr;
            regs_rsp_ready    = rsp_ready;
            kickoff_rsp_ready = 1'b0;
        end
    end

    //=========================================================================
    // Channel Kick-off Router (apbtodescr)
    //=========================================================================
    apbtodescr #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(APB_DATA_WIDTH)
    ) u_apbtodescr (
        .clk                (aclk),
        .rst_n              (aresetn),

        // CMD/RSP Interface
        .apb_cmd_valid      (kickoff_cmd_valid),
        .apb_cmd_ready      (kickoff_cmd_ready),
        .apb_cmd_addr       (kickoff_cmd_paddr),
        .apb_cmd_wdata      (kickoff_cmd_pwdata),
        .apb_cmd_write      (kickoff_cmd_pwrite),

        .apb_rsp_valid      (kickoff_rsp_valid),
        .apb_rsp_ready      (kickoff_rsp_ready),
        .apb_rsp_rdata      (kickoff_rsp_prdata),
        .apb_rsp_error      (kickoff_rsp_pslverr),

        // Descriptor Engine Outputs
        .desc_apb_valid     (desc_apb_valid),
        .desc_apb_ready     (desc_apb_ready),
        .desc_apb_addr      (desc_apb_addr)
    );

    //=========================================================================
    // PeakRDL Register Block (stream_regs)
    //=========================================================================
    // TODO: Instantiate stream_regs (PeakRDL-generated) once available
    // This will replace the placeholder assignments below

    // Placeholder: Tie register outputs to safe defaults
    assign reg_global_ctrl_global_en = 1'b1;  // Global enable
    assign reg_channel_enable_ch_en  = 8'hFF; // All channels enabled
    assign reg_channel_reset_ch_rst  = 8'h00; // No resets

    // Placeholder: Tie response to default values
    assign regs_rsp_valid  = regs_cmd_valid;  // Immediate response
    assign regs_cmd_ready  = 1'b1;            // Always ready
    assign regs_rsp_prdata = 32'hDEADBEEF;    // Placeholder data
    assign regs_rsp_pslverr = 1'b0;           // No error

    // TODO: Connect all ~89 register signals from PeakRDL to stream_config_block
    // Including all monitor configuration registers

    //=========================================================================
    // Configuration Mapping Block
    //=========================================================================
    stream_config_block #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_config_block (
        .clk                (aclk),
        .rst_n              (aresetn),

        // PeakRDL Register Outputs (placeholder connections)
        // TODO: Connect all register fields from stream_regs
        .reg_global_ctrl_global_en          (reg_global_ctrl_global_en),
        .reg_channel_enable_ch_en           (reg_channel_enable_ch_en),
        .reg_channel_reset_ch_rst           (reg_channel_reset_ch_rst),
        // ... (see stream_config_block.sv for complete port list)

        // STREAM Core Configuration Outputs (non-monitor)
        .cfg_channel_enable                 (cfg_channel_enable),
        .cfg_channel_reset                  (cfg_channel_reset),
        .cfg_sched_timeout_cycles           (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable           (cfg_sched_timeout_enable),
        .cfg_desceng_prefetch               (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh            (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base             (cfg_desceng_addr0_base),
        .cfg_desceng_addr1_base             (cfg_desceng_addr1_base),
        .cfg_axi_rd_burst_type              (cfg_axi_rd_burst_type),
        .cfg_axi_rd_max_burst_len           (cfg_axi_rd_max_burst_len),
        .cfg_axi_wr_burst_type              (cfg_axi_wr_burst_type),
        .cfg_axi_wr_max_burst_len           (cfg_axi_wr_max_burst_len),
        .cfg_perf_channel_id                (cfg_perf_channel_id),

        // Monitor Configuration Outputs - Descriptor AXI
        .cfg_desc_mon_enable                (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable            (cfg_desc_mon_err_enable),
        .cfg_desc_mon_timeout_cycles        (cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_timeout_enable        (cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_perf_enable           (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_compl_enable          (cfg_desc_mon_compl_enable),
        .cfg_desc_mon_debug_enable          (cfg_desc_mon_debug_enable),
        .cfg_desc_mon_pkt_mask              (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_timeout_mask          (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask            (cfg_desc_mon_compl_mask),

        // Monitor Configuration Outputs - Read Engine
        .cfg_rdeng_mon_enable               (cfg_rdeng_mon_enable),
        .cfg_rdeng_mon_err_enable           (cfg_rdeng_mon_err_enable),
        .cfg_rdeng_mon_timeout_cycles       (cfg_rdeng_mon_timeout_cycles),
        .cfg_rdeng_mon_timeout_enable       (cfg_rdeng_mon_timeout_enable),
        .cfg_rdeng_mon_perf_enable          (cfg_rdeng_mon_perf_enable),
        .cfg_rdeng_mon_compl_enable         (cfg_rdeng_mon_compl_enable),
        .cfg_rdeng_mon_debug_enable         (cfg_rdeng_mon_debug_enable),
        .cfg_rdeng_mon_pkt_mask             (cfg_rdeng_mon_pkt_mask),
        .cfg_rdeng_mon_timeout_mask         (cfg_rdeng_mon_timeout_mask),
        .cfg_rdeng_mon_compl_mask           (cfg_rdeng_mon_compl_mask),

        // Monitor Configuration Outputs - Write Engine
        .cfg_wreng_mon_enable               (cfg_wreng_mon_enable),
        .cfg_wreng_mon_err_enable           (cfg_wreng_mon_err_enable),
        .cfg_wreng_mon_timeout_cycles       (cfg_wreng_mon_timeout_cycles),
        .cfg_wreng_mon_timeout_enable       (cfg_wreng_mon_timeout_enable),
        .cfg_wreng_mon_perf_enable          (cfg_wreng_mon_perf_enable),
        .cfg_wreng_mon_compl_enable         (cfg_wreng_mon_compl_enable),
        .cfg_wreng_mon_debug_enable         (cfg_wreng_mon_debug_enable),
        .cfg_wreng_mon_pkt_mask             (cfg_wreng_mon_pkt_mask),
        .cfg_wreng_mon_timeout_mask         (cfg_wreng_mon_timeout_mask),
        .cfg_wreng_mon_compl_mask           (cfg_wreng_mon_compl_mask)
    );

    //=========================================================================
    // STREAM Core (Monitors ENABLED)
    //=========================================================================
    stream_core #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .SRAM_DEPTH(SRAM_DEPTH)
    ) u_stream_core (
        .clk                                (aclk),
        .rst_n                              (aresetn),

        //---------------------------------------------------------------------
        // Configuration Inputs (non-monitor)
        //---------------------------------------------------------------------
        .cfg_channel_enable                 (cfg_channel_enable),
        .cfg_channel_reset                  (cfg_channel_reset),
        .cfg_sched_timeout_cycles           (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable           (cfg_sched_timeout_enable),
        .cfg_desceng_prefetch               (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh            (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base             (cfg_desceng_addr0_base),
        .cfg_desceng_addr1_base             (cfg_desceng_addr1_base),
        .cfg_axi_rd_burst_type              (cfg_axi_rd_burst_type),
        .cfg_axi_rd_max_burst_len           (cfg_axi_rd_max_burst_len),
        .cfg_axi_wr_burst_type              (cfg_axi_wr_burst_type),
        .cfg_axi_wr_max_burst_len           (cfg_axi_wr_max_burst_len),
        .cfg_perf_channel_id                (cfg_perf_channel_id),

        //---------------------------------------------------------------------
        // Monitor Configuration - Descriptor AXI
        //---------------------------------------------------------------------
        .cfg_desc_mon_enable                (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable            (cfg_desc_mon_err_enable),
        .cfg_desc_mon_timeout_cycles        (cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_timeout_enable        (cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_perf_enable           (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_compl_enable          (cfg_desc_mon_compl_enable),
        .cfg_desc_mon_debug_enable          (cfg_desc_mon_debug_enable),
        .cfg_desc_mon_pkt_mask              (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_timeout_mask          (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask            (cfg_desc_mon_compl_mask),

        //---------------------------------------------------------------------
        // Monitor Configuration - Read Engine
        //---------------------------------------------------------------------
        .cfg_rdeng_mon_enable               (cfg_rdeng_mon_enable),
        .cfg_rdeng_mon_err_enable           (cfg_rdeng_mon_err_enable),
        .cfg_rdeng_mon_timeout_cycles       (cfg_rdeng_mon_timeout_cycles),
        .cfg_rdeng_mon_timeout_enable       (cfg_rdeng_mon_timeout_enable),
        .cfg_rdeng_mon_perf_enable          (cfg_rdeng_mon_perf_enable),
        .cfg_rdeng_mon_compl_enable         (cfg_rdeng_mon_compl_enable),
        .cfg_rdeng_mon_debug_enable         (cfg_rdeng_mon_debug_enable),
        .cfg_rdeng_mon_pkt_mask             (cfg_rdeng_mon_pkt_mask),
        .cfg_rdeng_mon_timeout_mask         (cfg_rdeng_mon_timeout_mask),
        .cfg_rdeng_mon_compl_mask           (cfg_rdeng_mon_compl_mask),

        //---------------------------------------------------------------------
        // Monitor Configuration - Write Engine
        //---------------------------------------------------------------------
        .cfg_wreng_mon_enable               (cfg_wreng_mon_enable),
        .cfg_wreng_mon_err_enable           (cfg_wreng_mon_err_enable),
        .cfg_wreng_mon_timeout_cycles       (cfg_wreng_mon_timeout_cycles),
        .cfg_wreng_mon_timeout_enable       (cfg_wreng_mon_timeout_enable),
        .cfg_wreng_mon_perf_enable          (cfg_wreng_mon_perf_enable),
        .cfg_wreng_mon_compl_enable         (cfg_wreng_mon_compl_enable),
        .cfg_wreng_mon_debug_enable         (cfg_wreng_mon_debug_enable),
        .cfg_wreng_mon_pkt_mask             (cfg_wreng_mon_pkt_mask),
        .cfg_wreng_mon_timeout_mask         (cfg_wreng_mon_timeout_mask),
        .cfg_wreng_mon_compl_mask           (cfg_wreng_mon_compl_mask),

        //---------------------------------------------------------------------
        // Descriptor APB Kick-off
        //---------------------------------------------------------------------
        .desc_apb_valid                     (desc_apb_valid),
        .desc_apb_ready                     (desc_apb_ready),
        .desc_apb_addr                      (desc_apb_addr),

        //---------------------------------------------------------------------
        // AXI4 Master - Descriptor Fetch
        //---------------------------------------------------------------------
        .m_axi_desc_araddr                  (m_axi_desc_araddr),
        .m_axi_desc_arlen                   (m_axi_desc_arlen),
        .m_axi_desc_arsize                  (m_axi_desc_arsize),
        .m_axi_desc_arburst                 (m_axi_desc_arburst),
        .m_axi_desc_arvalid                 (m_axi_desc_arvalid),
        .m_axi_desc_arready                 (m_axi_desc_arready),
        .m_axi_desc_rdata                   (m_axi_desc_rdata),
        .m_axi_desc_rresp                   (m_axi_desc_rresp),
        .m_axi_desc_rlast                   (m_axi_desc_rlast),
        .m_axi_desc_rvalid                  (m_axi_desc_rvalid),
        .m_axi_desc_rready                  (m_axi_desc_rready),

        //---------------------------------------------------------------------
        // AXI4 Master - Data Read
        //---------------------------------------------------------------------
        .m_axi_rd_araddr                    (m_axi_rd_araddr),
        .m_axi_rd_arlen                     (m_axi_rd_arlen),
        .m_axi_rd_arsize                    (m_axi_rd_arsize),
        .m_axi_rd_arburst                   (m_axi_rd_arburst),
        .m_axi_rd_arvalid                   (m_axi_rd_arvalid),
        .m_axi_rd_arready                   (m_axi_rd_arready),
        .m_axi_rd_rdata                     (m_axi_rd_rdata),
        .m_axi_rd_rresp                     (m_axi_rd_rresp),
        .m_axi_rd_rlast                     (m_axi_rd_rlast),
        .m_axi_rd_rvalid                    (m_axi_rd_rvalid),
        .m_axi_rd_rready                    (m_axi_rd_rready),

        //---------------------------------------------------------------------
        // AXI4 Master - Data Write
        //---------------------------------------------------------------------
        .m_axi_wr_awaddr                    (m_axi_wr_awaddr),
        .m_axi_wr_awlen                     (m_axi_wr_awlen),
        .m_axi_wr_awsize                    (m_axi_wr_awsize),
        .m_axi_wr_awburst                   (m_axi_wr_awburst),
        .m_axi_wr_awvalid                   (m_axi_wr_awvalid),
        .m_axi_wr_awready                   (m_axi_wr_awready),
        .m_axi_wr_wdata                     (m_axi_wr_wdata),
        .m_axi_wr_wstrb                     (m_axi_wr_wstrb),
        .m_axi_wr_wlast                     (m_axi_wr_wlast),
        .m_axi_wr_wvalid                    (m_axi_wr_wvalid),
        .m_axi_wr_wready                    (m_axi_wr_wready),
        .m_axi_wr_bresp                     (m_axi_wr_bresp),
        .m_axi_wr_bvalid                    (m_axi_wr_bvalid),
        .m_axi_wr_bready                    (m_axi_wr_bready),

        //---------------------------------------------------------------------
        // MonBus Output
        //---------------------------------------------------------------------
        .mon_valid                          (mon_valid),
        .mon_ready                          (mon_ready),
        .mon_packet                         (mon_packet),

        //---------------------------------------------------------------------
        // Interrupt Output
        //---------------------------------------------------------------------
        .channel_interrupt                  (channel_interrupt)
    );

endmodule : stream_top_mon_ch8
