//      // verilator_coverage annotation
        `timescale 1ns / 1ps
        
        //-----------------------------------------------------------------------------
        // Module: stream_top_ch8
        // Description:
        //   Top-level wrapper for STREAM core with 8 channels (configurable monitors).
        //
        //   Integration hierarchy:
        //     APB Interface
        //       → apb_slave_cdc (or apb_slave if CDC_ENABLE=0)
        //       → cmdrsp_router (address-based routing)
        //         → apbtodescr (channel kick-off, 0x000-0x03F)
        //         → peakrdl_to_cmdrsp (APB → CMD/RSP conversion)
        //           → stream_regs (PeakRDL registers, 0x100-0x3FF)
        //       → stream_config_block (register mapping)
        //       → stream_core (conditional: monitors enabled/disabled)
        //       → monbus_axil_group (monitor bus → AXI-Lite, USE_AXI_MONITORS=1)
        //
        //   APB Address Map:
        //     0x000-0x03F: Channel kick-off (apbtodescr)
        //     0x100-0x3FF: Configuration registers (PeakRDL)
        //
        //   Features:
        //     - 8 independent DMA channels
        //     - APB4 configuration interface with optional CDC
        //     - 3 AXI4 masters (descriptor fetch, read data, write data)
        //     - Configurable AXI transaction monitors (USE_AXI_MONITORS parameter)
        //     - Monitor bus to AXI-Lite conversion (error FIFO + master write)
        //     - Single interrupt output (stream_irq from monbus_axil_group)
        //     - Performance profiler interface (integrated in cmdrsp_router @ 0x040-0x0FF)
        //
        // Parameters:
        //   NUM_CHANNELS: Number of DMA channels (fixed at 8)
        //   DATA_WIDTH: AXI data bus width (512 bits default)
        //   ADDR_WIDTH: AXI address width (64 bits)
        //   SRAM_DEPTH: Internal SRAM buffer depth (4096 default)
        //   APB_ADDR_WIDTH: APB address width (12 bits for 4KB space)
        //   APB_DATA_WIDTH: APB data width (32 bits)
        //   USE_AXI_MONITORS: Enable/disable AXI monitors (0=disabled, 1=enabled)
        //   CDC_ENABLE: Enable/disable APB CDC (0=same clock, 1=different clocks)
        //
        // Interfaces:
        //   - APB4 slave (s_apb_*): Configuration interface
        //   - AXI4 master desc (m_axi_desc_*): 256-bit descriptor fetch
        //   - AXI4 master rd (m_axi_rd_*): Parameterizable read data
        //   - AXI4 master wr (m_axi_wr_*): Parameterizable write data
        //   - AXI4-Lite slave (s_axil_err_*): Monitor error/interrupt FIFO reads
        //   - AXI4-Lite master (m_axil_mon_*): Monitor data writes
        //   - Interrupt (stream_irq): Single interrupt output
        //
        //-----------------------------------------------------------------------------
        
        `include "stream_imports.svh"
        `include "reset_defs.svh"
        
        module stream_top_ch8 #(
            parameter int NUM_CHANNELS = 8,
            parameter int DATA_WIDTH = 512,
            parameter int ADDR_WIDTH = 64,
            parameter int SRAM_DEPTH = 4096,
            parameter int APB_ADDR_WIDTH = 12,
            parameter int APB_DATA_WIDTH = 32,
            parameter int AXI_ID_WIDTH = 8,
            parameter int AXI_USER_WIDTH = 3,    // $clog2(NUM_CHANNELS) for channel ID
            parameter int USE_AXI_MONITORS = 0,  // 0 = Disable monitors, 1 = Enable monitors
            parameter int CDC_ENABLE = 1         // 0 = Same clock (pclk=aclk), 1 = Different clocks (CDC)
        ) (
            //-------------------------------------------------------------------------
            // Clock and Reset
            //-------------------------------------------------------------------------
 002323     input  logic                                    aclk,
%000001     input  logic                                    aresetn,
        
            // Optional separate APB clock domain
 002322     input  logic                                    pclk,
%000001     input  logic                                    presetn,
        
            //-------------------------------------------------------------------------
            // APB4 Configuration Interface
            //-------------------------------------------------------------------------
%000000     input  logic [APB_ADDR_WIDTH-1:0]               s_apb_paddr,
 000024     input  logic                                    s_apb_psel,
 000024     input  logic                                    s_apb_penable,
 000014     input  logic                                    s_apb_pwrite,
%000000     input  logic [APB_DATA_WIDTH-1:0]               s_apb_pwdata,
 000024     input  logic [(APB_DATA_WIDTH/8)-1:0]           s_apb_pstrb,
%000000     output logic [APB_DATA_WIDTH-1:0]               s_apb_prdata,
 000024     output logic                                    s_apb_pready,
%000000     output logic                                    s_apb_pslverr,
        
            //-------------------------------------------------------------------------
            // AXI4 Master - Descriptor Fetch (256-bit)
            //-------------------------------------------------------------------------
            // Read Address Channel
%000000     output logic [AXI_ID_WIDTH-1:0]                 m_axi_desc_arid,
%000000     output logic [ADDR_WIDTH-1:0]                   m_axi_desc_araddr,
%000000     output logic [7:0]                              m_axi_desc_arlen,
%000000     output logic [2:0]                              m_axi_desc_arsize,
%000000     output logic [1:0]                              m_axi_desc_arburst,
%000000     output logic                                    m_axi_desc_arlock,
%000000     output logic [3:0]                              m_axi_desc_arcache,
%000000     output logic [2:0]                              m_axi_desc_arprot,
%000000     output logic [3:0]                              m_axi_desc_arqos,
%000000     output logic [3:0]                              m_axi_desc_arregion,
%000000     output logic [AXI_USER_WIDTH-1:0]               m_axi_desc_aruser,
%000004     output logic                                    m_axi_desc_arvalid,
%000004     input  logic                                    m_axi_desc_arready,
        
            // Read Data Channel
%000000     input  logic [AXI_ID_WIDTH-1:0]                 m_axi_desc_rid,
%000000     input  logic [255:0]                            m_axi_desc_rdata,
%000000     input  logic [1:0]                              m_axi_desc_rresp,
%000004     input  logic                                    m_axi_desc_rlast,
%000000     input  logic [AXI_USER_WIDTH-1:0]               m_axi_desc_ruser,
%000004     input  logic                                    m_axi_desc_rvalid,
%000001     output logic                                    m_axi_desc_rready,
        
            //-------------------------------------------------------------------------
            // AXI4 Master - Data Read (parameterizable width)
            //-------------------------------------------------------------------------
            // Read Address Channel
%000000     output logic [AXI_ID_WIDTH-1:0]                 m_axi_rd_arid,
%000000     output logic [ADDR_WIDTH-1:0]                   m_axi_rd_araddr,
%000000     output logic [7:0]                              m_axi_rd_arlen,
%000000     output logic [2:0]                              m_axi_rd_arsize,
%000000     output logic [1:0]                              m_axi_rd_arburst,
%000000     output logic                                    m_axi_rd_arlock,
%000000     output logic [3:0]                              m_axi_rd_arcache,
%000000     output logic [2:0]                              m_axi_rd_arprot,
%000000     output logic [3:0]                              m_axi_rd_arqos,
%000000     output logic [3:0]                              m_axi_rd_arregion,
%000000     output logic [AXI_USER_WIDTH-1:0]               m_axi_rd_aruser,
%000004     output logic                                    m_axi_rd_arvalid,
 000016     input  logic                                    m_axi_rd_arready,
        
            // Read Data Channel
%000000     input  logic [AXI_ID_WIDTH-1:0]                 m_axi_rd_rid,
            input  logic [DATA_WIDTH-1:0]                   m_axi_rd_rdata,
%000000     input  logic [1:0]                              m_axi_rd_rresp,
 000016     input  logic                                    m_axi_rd_rlast,
%000000     input  logic [AXI_USER_WIDTH-1:0]               m_axi_rd_ruser,
%000004     input  logic                                    m_axi_rd_rvalid,
%000001     output logic                                    m_axi_rd_rready,
        
            //-------------------------------------------------------------------------
            // AXI4 Master - Data Write (parameterizable width)
            //-------------------------------------------------------------------------
            // Write Address Channel
%000000     output logic [AXI_ID_WIDTH-1:0]                 m_axi_wr_awid,
%000000     output logic [ADDR_WIDTH-1:0]                   m_axi_wr_awaddr,
%000000     output logic [7:0]                              m_axi_wr_awlen,
%000000     output logic [2:0]                              m_axi_wr_awsize,
%000000     output logic [1:0]                              m_axi_wr_awburst,
%000000     output logic                                    m_axi_wr_awlock,
%000000     output logic [3:0]                              m_axi_wr_awcache,
%000000     output logic [2:0]                              m_axi_wr_awprot,
%000000     output logic [3:0]                              m_axi_wr_awqos,
%000000     output logic [3:0]                              m_axi_wr_awregion,
%000000     output logic [AXI_USER_WIDTH-1:0]               m_axi_wr_awuser,
 000014     output logic                                    m_axi_wr_awvalid,
 000016     input  logic                                    m_axi_wr_awready,
        
            // Write Data Channel
            output logic [DATA_WIDTH-1:0]                   m_axi_wr_wdata,
%000004     output logic [(DATA_WIDTH/8)-1:0]               m_axi_wr_wstrb,
 000016     output logic                                    m_axi_wr_wlast,
%000000     output logic [AXI_USER_WIDTH-1:0]               m_axi_wr_wuser,
%000004     output logic                                    m_axi_wr_wvalid,
 000256     input  logic                                    m_axi_wr_wready,
        
            // Write Response Channel
%000000     input  logic [AXI_ID_WIDTH-1:0]                 m_axi_wr_bid,
%000000     input  logic [1:0]                              m_axi_wr_bresp,
%000000     input  logic [AXI_USER_WIDTH-1:0]               m_axi_wr_buser,
 000016     input  logic                                    m_axi_wr_bvalid,
%000001     output logic                                    m_axi_wr_bready,
        
            //-------------------------------------------------------------------------
            // AXI4-Lite Slave - MonBus Error/Interrupt FIFO Read Interface
            //-------------------------------------------------------------------------
            // Slave read interface for error/interrupt FIFO
%000000     input  logic                                    s_axil_err_arvalid,
%000001     output logic                                    s_axil_err_arready,
%000000     input  logic [31:0]                             s_axil_err_araddr,
%000000     input  logic [2:0]                              s_axil_err_arprot,
%000000     output logic                                    s_axil_err_rvalid,
%000000     input  logic                                    s_axil_err_rready,
%000000     output logic [31:0]                             s_axil_err_rdata,
%000000     output logic [1:0]                              s_axil_err_rresp,
        
            //-------------------------------------------------------------------------
            // AXI4-Lite Master - MonBus Master Write Interface
            //-------------------------------------------------------------------------
            // Master write interface for monitor data
%000000     output logic                                    m_axil_mon_awvalid,
%000000     input  logic                                    m_axil_mon_awready,
%000000     output logic [31:0]                             m_axil_mon_awaddr,
%000000     output logic [2:0]                              m_axil_mon_awprot,
%000000     output logic                                    m_axil_mon_wvalid,
%000000     input  logic                                    m_axil_mon_wready,
%000000     output logic [31:0]                             m_axil_mon_wdata,
%000000     output logic [3:0]                              m_axil_mon_wstrb,
%000000     input  logic                                    m_axil_mon_bvalid,
%000000     output logic                                    m_axil_mon_bready,
%000000     input  logic [1:0]                              m_axil_mon_bresp,
        
            //-------------------------------------------------------------------------
            // Interrupt Output
            //-------------------------------------------------------------------------
%000000     output logic                                    stream_irq,
        
            //-------------------------------------------------------------------------
            // Debug Outputs - expose hwif_in values for testbench probing
            //-------------------------------------------------------------------------
%000001     output logic [7:0]                              debug_hwif_scheduler_idle,
%000001     output logic [7:0]                              debug_hwif_desc_engine_idle,
%000001     output logic [7:0]                              debug_hwif_channel_idle,
            // Debug outputs for stream_regs interface
 000020     output logic                                    debug_regblk_req,
 000014     output logic                                    debug_regblk_req_is_wr,
%000000     output logic [11:0]                             debug_regblk_addr,
%000000     output logic [31:0]                             debug_regblk_rd_data,
 000010     output logic                                    debug_regblk_rd_ack,
            // Debug outputs for command path to peakrdl_to_cmdrsp
 000020     output logic                                    debug_peakrdl_cmd_valid,
%000000     output logic [11:0]                             debug_peakrdl_cmd_paddr,
 000020     output logic                                    debug_peakrdl_rsp_valid,
%000000     output logic [31:0]                             debug_peakrdl_rsp_prdata,
            // Registered debug capture - holds last read transaction values
%000000     output logic [9:0]                              debug_last_cpuif_addr,
%000000     output logic [31:0]                             debug_last_cpuif_rd_data,
%000001     output logic                                    debug_last_cpuif_rd_ack,
            // Debug outputs for APB command path (from apb_slave_cdc)
 000024     output logic                                    debug_apb_cmd_valid,
%000005     output logic                                    debug_apb_cmd_ready,
 000014     output logic                                    debug_apb_cmd_pwrite,
%000000     output logic [11:0]                             debug_apb_cmd_paddr,
            // Debug outputs for APB response path
 000024     output logic                                    debug_apb_rsp_valid,
%000001     output logic                                    debug_apb_rsp_ready,
%000000     output logic [31:0]                             debug_apb_rsp_prdata,
            // Registered debug captures (hold values after transaction)
%000001     output logic                                    debug_apb_rd_cmd_seen,
%000000     output logic [11:0]                             debug_apb_rd_cmd_addr,
%000000     output logic [31:0]                             debug_apb_rsp_prdata_captured,
            // Sticky counters - count total reads at each stage
%000000     output logic [7:0]                              debug_apb_rd_count,
%000000     output logic [7:0]                              debug_peakrdl_rd_count,
%000000     output logic [7:0]                              debug_regblk_rd_count
        );
        
            //=========================================================================
            // Internal Signals
            //=========================================================================
        
            //-------------------------------------------------------------------------
            // APB CDC (if needed) - synchronize APB to AXI clock domain
            //-------------------------------------------------------------------------
%000000     logic [APB_ADDR_WIDTH-1:0]  apb_cdc_paddr;
%000000     logic                       apb_cdc_psel;
%000000     logic                       apb_cdc_penable;
%000000     logic                       apb_cdc_pwrite;
%000000     logic [APB_DATA_WIDTH-1:0]  apb_cdc_pwdata;
%000000     logic [(APB_DATA_WIDTH/8)-1:0] apb_cdc_pstrb;
%000000     logic [APB_DATA_WIDTH-1:0]  apb_cdc_prdata;
%000000     logic                       apb_cdc_pready;
%000000     logic                       apb_cdc_pslverr;
        
            //-------------------------------------------------------------------------
            // CMD/RSP Interface - from peakrdl_to_cmdrsp
            //-------------------------------------------------------------------------
%000000     logic                       cmd_valid;
%000000     logic                       cmd_ready;
%000000     logic                       cmd_pwrite;
%000000     logic [APB_ADDR_WIDTH-1:0]  cmd_paddr;
%000000     logic [APB_DATA_WIDTH-1:0]  cmd_pwdata;
%000000     logic [(APB_DATA_WIDTH/8)-1:0] cmd_pstrb;
        
%000000     logic                       rsp_valid;
%000000     logic                       rsp_ready;
%000000     logic [APB_DATA_WIDTH-1:0]  rsp_prdata;
%000000     logic                       rsp_pslverr;
        
            //-------------------------------------------------------------------------
            // Routed CMD/RSP - after address demux
            //-------------------------------------------------------------------------
            // To apbtodescr (kick-off)
%000004     logic                       kickoff_cmd_valid;
%000005     logic                       kickoff_cmd_ready;
%000000     logic [APB_ADDR_WIDTH-1:0]  kickoff_cmd_paddr;
%000000     logic [APB_DATA_WIDTH-1:0]  kickoff_cmd_pwdata;
 000014     logic                       kickoff_cmd_pwrite;
%000000     logic [(APB_DATA_WIDTH/8)-1:0] kickoff_cmd_pstrb;
        
%000004     logic                       kickoff_rsp_valid;
%000004     logic                       kickoff_rsp_ready;
%000000     logic [APB_DATA_WIDTH-1:0]  kickoff_rsp_prdata;
%000000     logic                       kickoff_rsp_pslverr;
        
            // To stream_regs (PeakRDL)
%000000     logic                       regs_cmd_valid;
%000000     logic                       regs_cmd_ready;
%000000     logic [APB_ADDR_WIDTH-1:0]  regs_cmd_paddr;
%000000     logic [APB_DATA_WIDTH-1:0]  regs_cmd_pwdata;
%000000     logic                       regs_cmd_pwrite;
%000000     logic [(APB_DATA_WIDTH/8)-1:0] regs_cmd_pstrb;
        
%000000     logic                       regs_rsp_valid;
%000000     logic                       regs_rsp_ready;
%000000     logic [APB_DATA_WIDTH-1:0]  regs_rsp_prdata;
%000000     logic                       regs_rsp_pslverr;
        
            //-------------------------------------------------------------------------
            // Address Decode
            //-------------------------------------------------------------------------
%000000     logic cmd_to_kickoff;
%000000     logic cmd_to_regs;
%000000     logic r_last_access_kickoff;  // Track which block was accessed
        
            //-------------------------------------------------------------------------
            // Descriptor Kick-off Signals (renamed to match stream_core)
            //-------------------------------------------------------------------------
%000000     logic [NUM_CHANNELS-1:0]                 apb_valid;
%000001     logic [NUM_CHANNELS-1:0]                 apb_ready;
            logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] apb_addr;
        
            //-------------------------------------------------------------------------
            // Status Signals from stream_core
            //-------------------------------------------------------------------------
%000003     logic                                   system_idle;
%000001     logic [NUM_CHANNELS-1:0]                descriptor_engine_idle;
%000001     logic [NUM_CHANNELS-1:0]                scheduler_idle;
%000000     logic [NUM_CHANNELS-1:0][6:0]           scheduler_state;
%000000     logic [NUM_CHANNELS-1:0]                sched_error;
%000001     logic [NUM_CHANNELS-1:0]                axi_rd_all_complete;
%000001     logic [NUM_CHANNELS-1:0]                axi_wr_all_complete;
        
            //-------------------------------------------------------------------------
            // Monitor Status Signals from stream_core
            //-------------------------------------------------------------------------
%000008     logic                                   cfg_sts_desc_mon_busy;
%000000     logic [7:0]                             cfg_sts_desc_mon_active_txns;
%000000     logic [15:0]                            cfg_sts_desc_mon_error_count;
%000000     logic [31:0]                            cfg_sts_desc_mon_txn_count;
%000000     logic                                   cfg_sts_desc_mon_conflict_error;
        
%000004     logic                                   cfg_sts_rdeng_skid_busy;
%000000     logic [7:0]                             cfg_sts_rdeng_mon_active_txns;
%000000     logic [15:0]                            cfg_sts_rdeng_mon_error_count;
%000000     logic [31:0]                            cfg_sts_rdeng_mon_txn_count;
%000000     logic                                   cfg_sts_rdeng_mon_conflict_error;
        
%000008     logic                                   cfg_sts_wreng_skid_busy;
%000000     logic [7:0]                             cfg_sts_wreng_mon_active_txns;
%000000     logic [15:0]                            cfg_sts_wreng_mon_error_count;
%000000     logic [31:0]                            cfg_sts_wreng_mon_txn_count;
%000000     logic                                   cfg_sts_wreng_mon_conflict_error;
        
            //-------------------------------------------------------------------------
            // Performance Profiler Interface
            //-------------------------------------------------------------------------
            // Performance profiler configuration signals
%000000     logic                                   perf_cfg_enable;
%000000     logic                                   perf_cfg_mode;
%000000     logic                                   perf_cfg_clear;
        
            // Performance profiler FIFO interface signals
%000001     logic                                   perf_fifo_empty;
%000000     logic                                   perf_fifo_full;
%000000     logic [15:0]                            perf_fifo_count;
%000000     logic                                   perf_fifo_rd;
%000000     logic [31:0]                            perf_fifo_data_low;
%000000     logic [31:0]                            perf_fifo_data_high;
        
            //-------------------------------------------------------------------------
            // Monitor Bus AXI-Lite Group Status
            //-------------------------------------------------------------------------
%000000     logic                                   mon_err_fifo_full;
%000000     logic                                   mon_write_fifo_full;
%000000     logic [7:0]                             mon_err_fifo_count;
%000000     logic [7:0]                             mon_write_fifo_count;
        
            //-------------------------------------------------------------------------
            // Monitor Bus (to monbus_axil_group)
            //-------------------------------------------------------------------------
 000012     logic                                   mon_valid;
%000001     logic                                   mon_ready;
%000000     logic [63:0]                            mon_packet;
        
            //-------------------------------------------------------------------------
            // Configuration Signals - from stream_config_block
            //-------------------------------------------------------------------------
            // Global and Channel Control
%000001     logic [NUM_CHANNELS-1:0]                cfg_channel_enable;
%000000     logic [NUM_CHANNELS-1:0]                cfg_channel_reset;
        
            // Scheduler Configuration
%000001     logic                                   cfg_sched_enable;
%000000     logic [15:0]                            cfg_sched_timeout_cycles;
%000001     logic                                   cfg_sched_timeout_enable;
%000001     logic                                   cfg_sched_err_enable;
%000001     logic                                   cfg_sched_compl_enable;
%000000     logic                                   cfg_sched_perf_enable;
        
            // Descriptor Engine Configuration
%000001     logic                                   cfg_desceng_enable;
%000000     logic                                   cfg_desceng_prefetch;
%000000     logic [3:0]                             cfg_desceng_fifo_thresh;
%000000     logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr0_base;
%000000     logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr0_limit;
%000000     logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr1_base;
%000000     logic [ADDR_WIDTH-1:0]                  cfg_desceng_addr1_limit;
        
            // Monitor Configuration (output by stream_config_block but tied off by stream_core when USE_AXI_MONITORS=0)
%000001     logic                                   cfg_desc_mon_enable;
%000001     logic                                   cfg_desc_mon_err_enable;
%000000     logic                                   cfg_desc_mon_perf_enable;
%000001     logic                                   cfg_desc_mon_timeout_enable;
%000000     logic [31:0]                            cfg_desc_mon_timeout_cycles;
%000000     logic [31:0]                            cfg_desc_mon_latency_thresh;
%000001     logic [15:0]                            cfg_desc_mon_pkt_mask;
%000000     logic [3:0]                             cfg_desc_mon_err_select;
%000001     logic [7:0]                             cfg_desc_mon_err_mask;
%000001     logic [7:0]                             cfg_desc_mon_timeout_mask;
%000000     logic [7:0]                             cfg_desc_mon_compl_mask;
%000001     logic [7:0]                             cfg_desc_mon_thresh_mask;
%000000     logic [7:0]                             cfg_desc_mon_perf_mask;
%000001     logic [7:0]                             cfg_desc_mon_addr_mask;
%000000     logic [7:0]                             cfg_desc_mon_debug_mask;
        
%000001     logic                                   cfg_rdeng_mon_enable;
%000001     logic                                   cfg_rdeng_mon_err_enable;
%000000     logic                                   cfg_rdeng_mon_perf_enable;
%000001     logic                                   cfg_rdeng_mon_timeout_enable;
%000000     logic [31:0]                            cfg_rdeng_mon_timeout_cycles;
%000000     logic [31:0]                            cfg_rdeng_mon_latency_thresh;
%000001     logic [15:0]                            cfg_rdeng_mon_pkt_mask;
%000000     logic [3:0]                             cfg_rdeng_mon_err_select;
%000001     logic [7:0]                             cfg_rdeng_mon_err_mask;
%000001     logic [7:0]                             cfg_rdeng_mon_timeout_mask;
%000000     logic [7:0]                             cfg_rdeng_mon_compl_mask;
%000001     logic [7:0]                             cfg_rdeng_mon_thresh_mask;
%000000     logic [7:0]                             cfg_rdeng_mon_perf_mask;
%000001     logic [7:0]                             cfg_rdeng_mon_addr_mask;
%000000     logic [7:0]                             cfg_rdeng_mon_debug_mask;
        
%000001     logic                                   cfg_wreng_mon_enable;
%000001     logic                                   cfg_wreng_mon_err_enable;
%000000     logic                                   cfg_wreng_mon_perf_enable;
%000001     logic                                   cfg_wreng_mon_timeout_enable;
%000000     logic [31:0]                            cfg_wreng_mon_timeout_cycles;
%000000     logic [31:0]                            cfg_wreng_mon_latency_thresh;
%000001     logic [15:0]                            cfg_wreng_mon_pkt_mask;
%000000     logic [3:0]                             cfg_wreng_mon_err_select;
%000001     logic [7:0]                             cfg_wreng_mon_err_mask;
%000001     logic [7:0]                             cfg_wreng_mon_timeout_mask;
%000000     logic [7:0]                             cfg_wreng_mon_compl_mask;
%000001     logic [7:0]                             cfg_wreng_mon_thresh_mask;
%000000     logic [7:0]                             cfg_wreng_mon_perf_mask;
%000001     logic [7:0]                             cfg_wreng_mon_addr_mask;
%000000     logic [7:0]                             cfg_wreng_mon_debug_mask;
        
            // AXI Transfer Configuration
%000000     logic [7:0]                             cfg_axi_rd_xfer_beats;
%000000     logic [7:0]                             cfg_axi_wr_xfer_beats;
        
            // Performance Profiler Configuration
%000000     logic                                   cfg_perf_enable;
%000000     logic                                   cfg_perf_mode;
%000000     logic                                   cfg_perf_clear;
        
            //=========================================================================
            // APB Clock Domain Crossing (APB → CMD/RSP)
            //=========================================================================
            // Conditional CDC based on CDC_ENABLE parameter:
            //   CDC_ENABLE=1: apb_slave_cdc (pclk ≠ aclk, clock domain crossing)
            //   CDC_ENABLE=0: apb_slave (pclk = aclk, same clock domain)
 000024     logic                       apb_cmd_valid;
%000005     logic                       apb_cmd_ready;
 000014     logic                       apb_cmd_pwrite;
%000000     logic [APB_ADDR_WIDTH-1:0]  apb_cmd_paddr;
%000000     logic [APB_DATA_WIDTH-1:0]  apb_cmd_pwdata;
 000024     logic [(APB_DATA_WIDTH/8)-1:0] apb_cmd_pstrb;
 000024     logic                       apb_rsp_valid;
%000001     logic                       apb_rsp_ready;
%000000     logic [APB_DATA_WIDTH-1:0]  apb_rsp_prdata;
%000000     logic                       apb_rsp_pslverr;
        
            generate
                if (CDC_ENABLE != 0) begin : g_apb_slave_cdc
                    // Clock Domain Crossing version for async clocks
                    apb_slave_cdc #(
                        .ADDR_WIDTH(APB_ADDR_WIDTH),
                        .DATA_WIDTH(APB_DATA_WIDTH)
                    ) u_apb_slave_cdc (
                        .aclk                   (aclk),
                        .aresetn                (aresetn),
                        .pclk                   (pclk),
                        .presetn                (presetn),
        
                        // APB Slave (from external interface, pclk domain)
                        .s_apb_PSEL             (s_apb_psel),
                        .s_apb_PENABLE          (s_apb_penable),
                        .s_apb_PREADY           (s_apb_pready),
                        .s_apb_PADDR            (s_apb_paddr),
                        .s_apb_PWRITE           (s_apb_pwrite),
                        .s_apb_PWDATA           (s_apb_pwdata),
                        .s_apb_PSTRB            (s_apb_pstrb),
                        .s_apb_PPROT            (3'b000),  // Unused
                        .s_apb_PRDATA           (s_apb_prdata),
                        .s_apb_PSLVERR          (s_apb_pslverr),
        
                        // CMD/RSP Master (to cmdrsp_router, aclk domain)
                        .cmd_valid              (apb_cmd_valid),
                        .cmd_ready              (apb_cmd_ready),
                        .cmd_pwrite             (apb_cmd_pwrite),
                        .cmd_paddr              (apb_cmd_paddr),
                        .cmd_pwdata             (apb_cmd_pwdata),
                        .cmd_pstrb              (apb_cmd_pstrb),
                        .cmd_pprot              (),  // Unused
                        .rsp_valid              (apb_rsp_valid),
                        .rsp_ready              (apb_rsp_ready),
                        .rsp_prdata             (apb_rsp_prdata),
                        .rsp_pslverr            (apb_rsp_pslverr)
                    );
                end else begin : g_apb_passthrough
                    // Same clock domain version (pclk = aclk)
                    apb_slave #(
                        .ADDR_WIDTH(APB_ADDR_WIDTH),
                        .DATA_WIDTH(APB_DATA_WIDTH)
                    ) u_apb_slave (
                        .pclk                   (aclk),         // Use aclk (pclk = aclk when CDC disabled)
                        .presetn                (aresetn),      // Use aresetn (presetn = aresetn)
        
                        // APB Slave (from external interface)
                        .s_apb_PSEL             (s_apb_psel),
                        .s_apb_PENABLE          (s_apb_penable),
                        .s_apb_PREADY           (s_apb_pready),
                        .s_apb_PADDR            (s_apb_paddr),
                        .s_apb_PWRITE           (s_apb_pwrite),
                        .s_apb_PWDATA           (s_apb_pwdata),
                        .s_apb_PSTRB            (s_apb_pstrb),
                        .s_apb_PPROT            (3'b000),       // Unused
                        .s_apb_PRDATA           (s_apb_prdata),
                        .s_apb_PSLVERR          (s_apb_pslverr),
        
                        // CMD/RSP Master (to cmdrsp_router, same clock domain)
                        .cmd_valid              (apb_cmd_valid),
                        .cmd_ready              (apb_cmd_ready),
                        .cmd_pwrite             (apb_cmd_pwrite),
                        .cmd_paddr              (apb_cmd_paddr),
                        .cmd_pwdata             (apb_cmd_pwdata),
                        .cmd_pstrb              (apb_cmd_pstrb),
                        .cmd_pprot              (),             // Unused
                        .rsp_valid              (apb_rsp_valid),
                        .rsp_ready              (apb_rsp_ready),
                        .rsp_prdata             (apb_rsp_prdata),
                        .rsp_pslverr            (apb_rsp_pslverr)
                    );
                end
            endgenerate
        
            //=========================================================================
            // CMD/RSP Address Router
            //=========================================================================
            // Routes CMD/RSP transactions (from apb_slave_cdc) based on address:
            //   0x000-0x03F: apbtodescr (channel kick-off)
            //   0x100-0x3FF: peakrdl_to_cmdrsp (configuration registers)
        
            // CMD/RSP signals to peakrdl_to_cmdrsp (m1 master)
 000020     logic                       peakrdl_cmd_valid;
 000021     logic                       peakrdl_cmd_ready;
 000014     logic                       peakrdl_cmd_pwrite;
%000000     logic [APB_ADDR_WIDTH-1:0]  peakrdl_cmd_paddr;
%000000     logic [APB_DATA_WIDTH-1:0]  peakrdl_cmd_pwdata;
 000020     logic                       peakrdl_rsp_valid;
 000020     logic                       peakrdl_rsp_ready;
%000000     logic [APB_DATA_WIDTH-1:0]  peakrdl_rsp_prdata;
%000000     logic                       peakrdl_rsp_pslverr;
        
            cmdrsp_router #(
                .ADDR_WIDTH(APB_ADDR_WIDTH),
                .DATA_WIDTH(APB_DATA_WIDTH)
            ) u_cmdrsp_router (
                .clk                        (aclk),
                .rst_n                      (aresetn),
        
                // CMD/RSP Slave (from apb_slave_cdc)
                .s_cmd_valid                (apb_cmd_valid),
                .s_cmd_ready                (apb_cmd_ready),
                .s_cmd_pwrite               (apb_cmd_pwrite),
                .s_cmd_paddr                (apb_cmd_paddr),
                .s_cmd_pwdata               (apb_cmd_pwdata),
                .s_rsp_valid                (apb_rsp_valid),
                .s_rsp_ready                (apb_rsp_ready),
                .s_rsp_prdata               (apb_rsp_prdata),
                .s_rsp_pslverr              (apb_rsp_pslverr),
        
                // CMD/RSP Master 0: apbtodescr (0x000-0x03F)
                .m0_cmd_valid               (kickoff_cmd_valid),
                .m0_cmd_ready               (kickoff_cmd_ready),
                .m0_cmd_pwrite              (kickoff_cmd_pwrite),
                .m0_cmd_paddr               (kickoff_cmd_paddr),
                .m0_cmd_pwdata              (kickoff_cmd_pwdata),
                .m0_rsp_valid               (kickoff_rsp_valid),
                .m0_rsp_ready               (kickoff_rsp_ready),
                .m0_rsp_prdata              (kickoff_rsp_prdata),
                .m0_rsp_pslverr             (kickoff_rsp_pslverr),
        
                // CMD/RSP Master 1: peakrdl_to_cmdrsp (0x100-0x3FF)
                .m1_cmd_valid               (peakrdl_cmd_valid),
                .m1_cmd_ready               (peakrdl_cmd_ready),
                .m1_cmd_pwrite              (peakrdl_cmd_pwrite),
                .m1_cmd_paddr               (peakrdl_cmd_paddr),
                .m1_cmd_pwdata              (peakrdl_cmd_pwdata),
                .m1_rsp_valid               (peakrdl_rsp_valid),
                .m1_rsp_ready               (peakrdl_rsp_ready),
                .m1_rsp_prdata              (peakrdl_rsp_prdata),
                .m1_rsp_pslverr             (peakrdl_rsp_pslverr),
        
                // Performance Profiler Interface (0x040-0x0FF, integrated registers)
                .perf_cfg_enable            (perf_cfg_enable),
                .perf_cfg_mode              (perf_cfg_mode),
                .perf_cfg_clear             (perf_cfg_clear),
                .perf_fifo_data_low         (perf_fifo_data_low),
                .perf_fifo_data_high        (perf_fifo_data_high),
                .perf_fifo_empty            (perf_fifo_empty),
                .perf_fifo_full             (perf_fifo_full),
                .perf_fifo_count            (perf_fifo_count),
                .perf_fifo_rd               (perf_fifo_rd)
            );
        
            //=========================================================================
            // Channel Kick-off Router (apbtodescr)
            //=========================================================================
            apbtodescr #(
                .NUM_CHANNELS(NUM_CHANNELS),
                .ADDR_WIDTH(APB_ADDR_WIDTH),
                .DATA_WIDTH(APB_DATA_WIDTH)
            ) u_apbtodescr (
                .clk                            (aclk),
                .rst_n                          (aresetn),
        
                // CMD/RSP Interface (from cmdrsp_router m0)
                .apb_cmd_valid                  (kickoff_cmd_valid),
                .apb_cmd_ready                  (kickoff_cmd_ready),
                .apb_cmd_addr                   (kickoff_cmd_paddr),
                .apb_cmd_wdata                  (kickoff_cmd_pwdata),
                .apb_cmd_write                  (kickoff_cmd_pwrite),
        
                .apb_rsp_valid                  (kickoff_rsp_valid),
                .apb_rsp_ready                  (kickoff_rsp_ready),
                .apb_rsp_rdata                  (kickoff_rsp_prdata),
                .apb_rsp_error                  (kickoff_rsp_pslverr),
        
                // Descriptor Engine Outputs
                .desc_apb_valid                 (apb_valid),
                .desc_apb_ready                 (apb_ready),
                .desc_apb_addr                  (apb_addr),
        
                // Debug output (unused)
                .apb_descriptor_kickoff_hit     ()
            );
        
            //=========================================================================
            // CMD/RSP to Passthrough Adapter (peakrdl_to_cmdrsp)
            //=========================================================================
            // Converts CMD/RSP protocol to PeakRDL passthrough interface
        
            // Passthrough interface signals to stream_regs
 000020     logic                       regblk_req;
 000014     logic                       regblk_req_is_wr;
%000000     logic [APB_ADDR_WIDTH-1:0]  regblk_addr;
%000000     logic [APB_DATA_WIDTH-1:0]  regblk_wr_data;
%000001     logic [APB_DATA_WIDTH-1:0]  regblk_wr_biten;
%000000     logic                       regblk_req_stall_wr;
%000000     logic                       regblk_req_stall_rd;
 000010     logic                       regblk_rd_ack;
%000000     logic                       regblk_rd_err;
%000000     logic [APB_DATA_WIDTH-1:0]  regblk_rd_data;
 000010     logic                       regblk_wr_ack;
%000000     logic                       regblk_wr_err;
        
            peakrdl_to_cmdrsp #(
                .ADDR_WIDTH(APB_ADDR_WIDTH),
                .DATA_WIDTH(APB_DATA_WIDTH)
            ) u_peakrdl_adapter (
                .aclk                   (aclk),
                .aresetn                (aresetn),
        
                // CMD/RSP input (from cmdrsp_router m1)
                .cmd_valid              (peakrdl_cmd_valid),
                .cmd_ready              (peakrdl_cmd_ready),
                .cmd_pwrite             (peakrdl_cmd_pwrite),
                .cmd_paddr              (peakrdl_cmd_paddr),
                .cmd_pwdata             (peakrdl_cmd_pwdata),
                .cmd_pstrb              ({(APB_DATA_WIDTH/8){1'b1}}),  // All bytes valid
                .rsp_valid              (peakrdl_rsp_valid),
                .rsp_ready              (peakrdl_rsp_ready),
                .rsp_prdata             (peakrdl_rsp_prdata),
                .rsp_pslverr            (peakrdl_rsp_pslverr),
        
                // Passthrough interface (to stream_regs)
                .regblk_req             (regblk_req),
                .regblk_req_is_wr       (regblk_req_is_wr),
                .regblk_addr            (regblk_addr),
                .regblk_wr_data         (regblk_wr_data),
                .regblk_wr_biten        (regblk_wr_biten),
                .regblk_req_stall_wr    (regblk_req_stall_wr),
                .regblk_req_stall_rd    (regblk_req_stall_rd),
                .regblk_rd_ack          (regblk_rd_ack),
                .regblk_rd_err          (regblk_rd_err),
                .regblk_rd_data         (regblk_rd_data),
                .regblk_wr_ack          (regblk_wr_ack),
                .regblk_wr_err          (regblk_wr_err)
            );
        
            //=========================================================================
            // PeakRDL Register Block (stream_regs)
            //=========================================================================
            // PeakRDL generated register file with passthrough interface
            // Import register package
            import stream_regs_pkg::*;
        
            // Hardware interface to/from register file
            stream_regs__in_t  hwif_in;
            stream_regs__out_t hwif_out;
        
            // Intermediate signals for hwif_in fields
            // Use explicit signals before struct assignment for better simulator struct handling
%000003     logic          hwif_system_idle;
%000001     logic [7:0]    hwif_channel_idle;
%000001     logic [7:0]    hwif_desc_engine_idle;
%000001     logic [7:0]    hwif_scheduler_idle;
%000000     logic [6:0]    hwif_ch_state [NUM_CHANNELS];
        
            // Compute intermediate signals
            assign hwif_system_idle = system_idle;
            assign hwif_channel_idle = scheduler_idle & descriptor_engine_idle;
            assign hwif_desc_engine_idle = descriptor_engine_idle;
            assign hwif_scheduler_idle = scheduler_idle;
        
            generate
                for (genvar i = 0; i < NUM_CHANNELS; i++) begin : g_hwif_state
                    assign hwif_ch_state[i] = scheduler_state[i];
                end
            endgenerate
        
            // Use combinational assignment for hwif_in struct
            // Note: registered struct member assignments through ports may have simulation issues
%000001     always_comb begin
%000001         hwif_in.GLOBAL_STATUS.SYSTEM_IDLE.next = hwif_system_idle;
%000001         hwif_in.CHANNEL_IDLE.CH_IDLE.next = hwif_channel_idle;
%000001         hwif_in.DESC_ENGINE_IDLE.DESC_IDLE.next = hwif_desc_engine_idle;
%000001         hwif_in.SCHEDULER_IDLE.SCHED_IDLE.next = hwif_scheduler_idle;
%000001         for (int i = 0; i < NUM_CHANNELS; i++) begin
%000008             hwif_in.CH_STATE[i].STATE.STATE.next = hwif_ch_state[i];
                end
            end
        
            // Debug outputs - expose what stream_regs should see for hwif_in values
            assign debug_hwif_scheduler_idle = hwif_in.SCHEDULER_IDLE.SCHED_IDLE.next;
            assign debug_hwif_desc_engine_idle = hwif_in.DESC_ENGINE_IDLE.DESC_IDLE.next;
            assign debug_hwif_channel_idle = hwif_in.CHANNEL_IDLE.CH_IDLE.next;
        
            // Debug outputs for stream_regs interface - trace the regblk signals
            assign debug_regblk_req = regblk_req;
            assign debug_regblk_req_is_wr = regblk_req_is_wr;
            assign debug_regblk_addr = regblk_addr;
            assign debug_regblk_rd_data = regblk_rd_data;
            assign debug_regblk_rd_ack = regblk_rd_ack;
        
            // Additional debug: probe peakrdl_to_cmdrsp response
            // This lets us compare what peakrdl_to_cmdrsp receives vs what it outputs
            assign debug_peakrdl_cmd_valid = peakrdl_cmd_valid;
            assign debug_peakrdl_cmd_paddr = peakrdl_cmd_paddr;
            assign debug_peakrdl_rsp_valid = peakrdl_rsp_valid;
            assign debug_peakrdl_rsp_prdata = peakrdl_rsp_prdata;
        
            // Registered debug capture - captures transaction values when read ack occurs
            // This preserves the values for probing after the transaction completes
%000000     logic [9:0] r_debug_last_cpuif_addr;
%000000     logic [31:0] r_debug_last_cpuif_rd_data;
%000001     logic r_debug_last_cpuif_rd_ack;
        
            // STICKY counter: counts every time regblk_req fires for a read
%000000     logic [7:0] r_debug_regblk_rd_count;
            // STICKY counter: counts every time peakrdl_cmd_valid fires for a read
%000000     logic [7:0] r_debug_peakrdl_rd_count;
            // STICKY counter: counts every time apb_cmd_valid fires for a read
%000000     logic [7:0] r_debug_apb_rd_count;
        
 001162     always_ff @(posedge aclk or negedge aresetn) begin
 000011         if (!aresetn) begin
 000011             r_debug_last_cpuif_addr <= '0;
 000011             r_debug_last_cpuif_rd_data <= '0;
 000011             r_debug_last_cpuif_rd_ack <= '0;
 000011             r_debug_regblk_rd_count <= '0;
 000011             r_debug_peakrdl_rd_count <= '0;
 000011             r_debug_apb_rd_count <= '0;
 001151         end else begin
                    // Capture when a read request occurs (regblk_req && !regblk_req_is_wr)
 000010             if (regblk_req && !regblk_req_is_wr) begin
 000010                 r_debug_last_cpuif_addr <= regblk_addr[9:0];
 000010                 r_debug_last_cpuif_rd_data <= regblk_rd_data;
 000010                 r_debug_last_cpuif_rd_ack <= regblk_rd_ack;
 000010                 r_debug_regblk_rd_count <= r_debug_regblk_rd_count + 1'b1;
                    end
                    // Count peakrdl read commands
%000005             if (peakrdl_cmd_valid && !peakrdl_cmd_pwrite) begin
%000005                 r_debug_peakrdl_rd_count <= r_debug_peakrdl_rd_count + 1'b1;
                    end
                    // Count apb read commands
%000005             if (apb_cmd_valid && !apb_cmd_pwrite) begin
%000005                 r_debug_apb_rd_count <= r_debug_apb_rd_count + 1'b1;
                    end
                end
            end
        
            assign debug_last_cpuif_addr = r_debug_last_cpuif_addr;
            assign debug_last_cpuif_rd_data = r_debug_last_cpuif_rd_data;
            assign debug_last_cpuif_rd_ack = r_debug_last_cpuif_rd_ack;
        
            // Registered debug capture for APB read commands (captures when read cmd is accepted)
%000001     logic r_debug_apb_rd_cmd_seen;
%000000     logic [11:0] r_debug_apb_rd_cmd_addr;
%000000     logic [31:0] r_debug_apb_rsp_prdata_captured;
        
 001162     always_ff @(posedge aclk or negedge aresetn) begin
 000011         if (!aresetn) begin
 000011             r_debug_apb_rd_cmd_seen <= 1'b0;
 000011             r_debug_apb_rd_cmd_addr <= '0;
 000011             r_debug_apb_rsp_prdata_captured <= '0;
 001151         end else begin
                    // Capture when a read command is accepted (cmd_valid && cmd_ready && !cmd_pwrite)
%000005             if (apb_cmd_valid && apb_cmd_ready && !apb_cmd_pwrite) begin
%000005                 r_debug_apb_rd_cmd_seen <= 1'b1;
%000005                 r_debug_apb_rd_cmd_addr <= apb_cmd_paddr;
                    end
                    // Capture response data when response is valid
 000012             if (apb_rsp_valid) begin
 000012                 r_debug_apb_rsp_prdata_captured <= apb_rsp_prdata;
                    end
                end
            end
        
            // Debug outputs for APB command/response path (direct combinational)
            assign debug_apb_cmd_valid = apb_cmd_valid;
            assign debug_apb_cmd_ready = apb_cmd_ready;
            assign debug_apb_cmd_pwrite = apb_cmd_pwrite;
            assign debug_apb_cmd_paddr = apb_cmd_paddr;
            assign debug_apb_rsp_valid = apb_rsp_valid;
            assign debug_apb_rsp_ready = apb_rsp_ready;
            assign debug_apb_rsp_prdata = apb_rsp_prdata;
            // Registered debug captures
            assign debug_apb_rd_cmd_seen = r_debug_apb_rd_cmd_seen;
            assign debug_apb_rd_cmd_addr = r_debug_apb_rd_cmd_addr;
            assign debug_apb_rsp_prdata_captured = r_debug_apb_rsp_prdata_captured;
            // Sticky counters - count reads at each pipeline stage
            assign debug_apb_rd_count = r_debug_apb_rd_count;
            assign debug_peakrdl_rd_count = r_debug_peakrdl_rd_count;
            assign debug_regblk_rd_count = r_debug_regblk_rd_count;
        
            stream_regs u_stream_regs (
                .clk                    (aclk),
                .rst                    (~aresetn),  // Active-high reset for PeakRDL
        
                // Passthrough CPU interface
                .s_cpuif_req            (regblk_req),
                .s_cpuif_req_is_wr      (regblk_req_is_wr),
                .s_cpuif_addr           (regblk_addr[9:0]),  // PeakRDL uses 10-bit address
                .s_cpuif_wr_data        (regblk_wr_data),
                .s_cpuif_wr_biten       (regblk_wr_biten),
                .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
                .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
                .s_cpuif_rd_ack         (regblk_rd_ack),
                .s_cpuif_rd_err         (regblk_rd_err),
                .s_cpuif_rd_data        (regblk_rd_data),
                .s_cpuif_wr_ack         (regblk_wr_ack),
                .s_cpuif_wr_err         (regblk_wr_err),
        
                // Hardware interface
                .hwif_in                (hwif_in),
                .hwif_out               (hwif_out)
            );
        
            //=========================================================================
            // Configuration Mapping Block
            //=========================================================================
            // Extracts PeakRDL register values from hwif_out and maps them to
            // stream_core configuration signals
            stream_config_block #(
                .NUM_CHANNELS(NUM_CHANNELS),
                .ADDR_WIDTH(ADDR_WIDTH)
            ) u_config_block (
                .clk                (aclk),
                .rst_n              (aresetn),
        
                //---------------------------------------------------------------------
                // PeakRDL Register Outputs (extracted from hwif_out)
                //---------------------------------------------------------------------
        
                // Global Control
                .reg_global_ctrl_global_en          (hwif_out.GLOBAL_CTRL.GLOBAL_EN.value),
                .reg_global_ctrl_global_rst         (hwif_out.GLOBAL_CTRL.GLOBAL_RST.value),
        
                // Channel Control
                .reg_channel_enable_ch_en           (hwif_out.CHANNEL_ENABLE.CH_EN.value),
                .reg_channel_reset_ch_rst           (hwif_out.CHANNEL_RESET.CH_RST.value),
        
                // Scheduler Configuration
                .reg_sched_timeout_cycles_timeout_cycles    (hwif_out.SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES.value),
                .reg_sched_config_sched_en                  (hwif_out.SCHED_CONFIG.SCHED_EN.value),
                .reg_sched_config_timeout_en                (hwif_out.SCHED_CONFIG.TIMEOUT_EN.value),
                .reg_sched_config_err_en                    (hwif_out.SCHED_CONFIG.ERR_EN.value),
                .reg_sched_config_compl_en                  (hwif_out.SCHED_CONFIG.COMPL_EN.value),
                .reg_sched_config_perf_en                   (hwif_out.SCHED_CONFIG.PERF_EN.value),
        
                // Descriptor Engine Configuration
                .reg_desceng_config_desceng_en              (hwif_out.DESCENG_CONFIG.DESCENG_EN.value),
                .reg_desceng_config_prefetch_en             (hwif_out.DESCENG_CONFIG.PREFETCH_EN.value),
                .reg_desceng_config_fifo_thresh             (hwif_out.DESCENG_CONFIG.FIFO_THRESH.value),
                .reg_desceng_addr0_base_addr0_base          (hwif_out.DESCENG_ADDR0_BASE.ADDR0_BASE.value),
                .reg_desceng_addr0_limit_addr0_limit        (hwif_out.DESCENG_ADDR0_LIMIT.ADDR0_LIMIT.value),
                .reg_desceng_addr1_base_addr1_base          (hwif_out.DESCENG_ADDR1_BASE.ADDR1_BASE.value),
                .reg_desceng_addr1_limit_addr1_limit        (hwif_out.DESCENG_ADDR1_LIMIT.ADDR1_LIMIT.value),
        
                // Descriptor AXI Monitor Configuration
                .reg_daxmon_enable_mon_en                   (hwif_out.DAXMON_ENABLE.MON_EN.value),
                .reg_daxmon_enable_err_en                   (hwif_out.DAXMON_ENABLE.ERR_EN.value),
                .reg_daxmon_enable_compl_en                 (hwif_out.DAXMON_ENABLE.COMPL_EN.value),
                .reg_daxmon_enable_timeout_en               (hwif_out.DAXMON_ENABLE.TIMEOUT_EN.value),
                .reg_daxmon_enable_perf_en                  (hwif_out.DAXMON_ENABLE.PERF_EN.value),
                .reg_daxmon_timeout_timeout_cycles          (hwif_out.DAXMON_TIMEOUT.TIMEOUT_CYCLES.value),
                .reg_daxmon_latency_thresh_latency_thresh   (hwif_out.DAXMON_LATENCY_THRESH.LATENCY_THRESH.value),
                .reg_daxmon_pkt_mask_pkt_mask               (hwif_out.DAXMON_PKT_MASK.PKT_MASK.value),
                .reg_daxmon_err_cfg_err_select              (hwif_out.DAXMON_ERR_CFG.ERR_SELECT.value),
                .reg_daxmon_err_cfg_err_mask                (hwif_out.DAXMON_ERR_CFG.ERR_MASK.value),
                .reg_daxmon_mask1_timeout_mask              (hwif_out.DAXMON_MASK1.TIMEOUT_MASK.value),
                .reg_daxmon_mask1_compl_mask                (hwif_out.DAXMON_MASK1.COMPL_MASK.value),
                .reg_daxmon_mask2_thresh_mask               (hwif_out.DAXMON_MASK2.THRESH_MASK.value),
                .reg_daxmon_mask2_perf_mask                 (hwif_out.DAXMON_MASK2.PERF_MASK.value),
                .reg_daxmon_mask3_addr_mask                 (hwif_out.DAXMON_MASK3.ADDR_MASK.value),
                .reg_daxmon_mask3_debug_mask                (hwif_out.DAXMON_MASK3.DEBUG_MASK.value),
        
                // Read Engine AXI Monitor Configuration
                .reg_rdmon_enable_mon_en                    (hwif_out.RDMON_ENABLE.MON_EN.value),
                .reg_rdmon_enable_err_en                    (hwif_out.RDMON_ENABLE.ERR_EN.value),
                .reg_rdmon_enable_compl_en                  (hwif_out.RDMON_ENABLE.COMPL_EN.value),
                .reg_rdmon_enable_timeout_en                (hwif_out.RDMON_ENABLE.TIMEOUT_EN.value),
                .reg_rdmon_enable_perf_en                   (hwif_out.RDMON_ENABLE.PERF_EN.value),
                .reg_rdmon_timeout_timeout_cycles           (hwif_out.RDMON_TIMEOUT.TIMEOUT_CYCLES.value),
                .reg_rdmon_latency_thresh_latency_thresh    (hwif_out.RDMON_LATENCY_THRESH.LATENCY_THRESH.value),
                .reg_rdmon_pkt_mask_pkt_mask                (hwif_out.RDMON_PKT_MASK.PKT_MASK.value),
                .reg_rdmon_err_cfg_err_select               (hwif_out.RDMON_ERR_CFG.ERR_SELECT.value),
                .reg_rdmon_err_cfg_err_mask                 (hwif_out.RDMON_ERR_CFG.ERR_MASK.value),
                .reg_rdmon_mask1_timeout_mask               (hwif_out.RDMON_MASK1.TIMEOUT_MASK.value),
                .reg_rdmon_mask1_compl_mask                 (hwif_out.RDMON_MASK1.COMPL_MASK.value),
                .reg_rdmon_mask2_thresh_mask                (hwif_out.RDMON_MASK2.THRESH_MASK.value),
                .reg_rdmon_mask2_perf_mask                  (hwif_out.RDMON_MASK2.PERF_MASK.value),
                .reg_rdmon_mask3_addr_mask                  (hwif_out.RDMON_MASK3.ADDR_MASK.value),
                .reg_rdmon_mask3_debug_mask                 (hwif_out.RDMON_MASK3.DEBUG_MASK.value),
        
                // Write Engine AXI Monitor Configuration
                .reg_wrmon_enable_mon_en                    (hwif_out.WRMON_ENABLE.MON_EN.value),
                .reg_wrmon_enable_err_en                    (hwif_out.WRMON_ENABLE.ERR_EN.value),
                .reg_wrmon_enable_compl_en                  (hwif_out.WRMON_ENABLE.COMPL_EN.value),
                .reg_wrmon_enable_timeout_en                (hwif_out.WRMON_ENABLE.TIMEOUT_EN.value),
                .reg_wrmon_enable_perf_en                   (hwif_out.WRMON_ENABLE.PERF_EN.value),
                .reg_wrmon_timeout_timeout_cycles           (hwif_out.WRMON_TIMEOUT.TIMEOUT_CYCLES.value),
                .reg_wrmon_latency_thresh_latency_thresh    (hwif_out.WRMON_LATENCY_THRESH.LATENCY_THRESH.value),
                .reg_wrmon_pkt_mask_pkt_mask                (hwif_out.WRMON_PKT_MASK.PKT_MASK.value),
                .reg_wrmon_err_cfg_err_select               (hwif_out.WRMON_ERR_CFG.ERR_SELECT.value),
                .reg_wrmon_err_cfg_err_mask                 (hwif_out.WRMON_ERR_CFG.ERR_MASK.value),
                .reg_wrmon_mask1_timeout_mask               (hwif_out.WRMON_MASK1.TIMEOUT_MASK.value),
                .reg_wrmon_mask1_compl_mask                 (hwif_out.WRMON_MASK1.COMPL_MASK.value),
                .reg_wrmon_mask2_thresh_mask                (hwif_out.WRMON_MASK2.THRESH_MASK.value),
                .reg_wrmon_mask2_perf_mask                  (hwif_out.WRMON_MASK2.PERF_MASK.value),
                .reg_wrmon_mask3_addr_mask                  (hwif_out.WRMON_MASK3.ADDR_MASK.value),
                .reg_wrmon_mask3_debug_mask                 (hwif_out.WRMON_MASK3.DEBUG_MASK.value),
        
                // AXI Transfer Configuration
                .reg_axi_xfer_config_rd_xfer_beats          (hwif_out.AXI_XFER_CONFIG.RD_XFER_BEATS.value),
                .reg_axi_xfer_config_wr_xfer_beats          (hwif_out.AXI_XFER_CONFIG.WR_XFER_BEATS.value),
        
                // Performance Profiler Configuration
                .reg_perf_config_perf_en                    (hwif_out.PERF_CONFIG.PERF_EN.value),
                .reg_perf_config_perf_mode                  (hwif_out.PERF_CONFIG.PERF_MODE.value),
                .reg_perf_config_perf_clear                 (hwif_out.PERF_CONFIG.PERF_CLEAR.value),
        
                //---------------------------------------------------------------------
                // STREAM Core Configuration Outputs
                //---------------------------------------------------------------------
                .cfg_channel_enable                 (cfg_channel_enable),
                .cfg_channel_reset                  (cfg_channel_reset),
                .cfg_sched_enable                   (cfg_sched_enable),
                .cfg_sched_timeout_cycles           (cfg_sched_timeout_cycles),
                .cfg_sched_timeout_enable           (cfg_sched_timeout_enable),
                .cfg_sched_err_enable               (cfg_sched_err_enable),
                .cfg_sched_compl_enable             (cfg_sched_compl_enable),
                .cfg_sched_perf_enable              (cfg_sched_perf_enable),
                .cfg_desceng_enable                 (cfg_desceng_enable),
                .cfg_desceng_prefetch               (cfg_desceng_prefetch),
                .cfg_desceng_fifo_thresh            (cfg_desceng_fifo_thresh),
                .cfg_desceng_addr0_base             (cfg_desceng_addr0_base),
                .cfg_desceng_addr0_limit            (cfg_desceng_addr0_limit),
                .cfg_desceng_addr1_base             (cfg_desceng_addr1_base),
                .cfg_desceng_addr1_limit            (cfg_desceng_addr1_limit),
                .cfg_desc_mon_enable                (cfg_desc_mon_enable),
                .cfg_desc_mon_err_enable            (cfg_desc_mon_err_enable),
                .cfg_desc_mon_perf_enable           (cfg_desc_mon_perf_enable),
                .cfg_desc_mon_timeout_enable        (cfg_desc_mon_timeout_enable),
                .cfg_desc_mon_timeout_cycles        (cfg_desc_mon_timeout_cycles),
                .cfg_desc_mon_latency_thresh        (cfg_desc_mon_latency_thresh),
                .cfg_desc_mon_pkt_mask              (cfg_desc_mon_pkt_mask),
                .cfg_desc_mon_err_select            (cfg_desc_mon_err_select),
                .cfg_desc_mon_err_mask              (cfg_desc_mon_err_mask),
                .cfg_desc_mon_timeout_mask          (cfg_desc_mon_timeout_mask),
                .cfg_desc_mon_compl_mask            (cfg_desc_mon_compl_mask),
                .cfg_desc_mon_thresh_mask           (cfg_desc_mon_thresh_mask),
                .cfg_desc_mon_perf_mask             (cfg_desc_mon_perf_mask),
                .cfg_desc_mon_addr_mask             (cfg_desc_mon_addr_mask),
                .cfg_desc_mon_debug_mask            (cfg_desc_mon_debug_mask),
                .cfg_rdeng_mon_enable               (cfg_rdeng_mon_enable),
                .cfg_rdeng_mon_err_enable           (cfg_rdeng_mon_err_enable),
                .cfg_rdeng_mon_perf_enable          (cfg_rdeng_mon_perf_enable),
                .cfg_rdeng_mon_timeout_enable       (cfg_rdeng_mon_timeout_enable),
                .cfg_rdeng_mon_timeout_cycles       (cfg_rdeng_mon_timeout_cycles),
                .cfg_rdeng_mon_latency_thresh       (cfg_rdeng_mon_latency_thresh),
                .cfg_rdeng_mon_pkt_mask             (cfg_rdeng_mon_pkt_mask),
                .cfg_rdeng_mon_err_select           (cfg_rdeng_mon_err_select),
                .cfg_rdeng_mon_err_mask             (cfg_rdeng_mon_err_mask),
                .cfg_rdeng_mon_timeout_mask         (cfg_rdeng_mon_timeout_mask),
                .cfg_rdeng_mon_compl_mask           (cfg_rdeng_mon_compl_mask),
                .cfg_rdeng_mon_thresh_mask          (cfg_rdeng_mon_thresh_mask),
                .cfg_rdeng_mon_perf_mask            (cfg_rdeng_mon_perf_mask),
                .cfg_rdeng_mon_addr_mask            (cfg_rdeng_mon_addr_mask),
                .cfg_rdeng_mon_debug_mask           (cfg_rdeng_mon_debug_mask),
                .cfg_wreng_mon_enable               (cfg_wreng_mon_enable),
                .cfg_wreng_mon_err_enable           (cfg_wreng_mon_err_enable),
                .cfg_wreng_mon_perf_enable          (cfg_wreng_mon_perf_enable),
                .cfg_wreng_mon_timeout_enable       (cfg_wreng_mon_timeout_enable),
                .cfg_wreng_mon_timeout_cycles       (cfg_wreng_mon_timeout_cycles),
                .cfg_wreng_mon_latency_thresh       (cfg_wreng_mon_latency_thresh),
                .cfg_wreng_mon_pkt_mask             (cfg_wreng_mon_pkt_mask),
                .cfg_wreng_mon_err_select           (cfg_wreng_mon_err_select),
                .cfg_wreng_mon_err_mask             (cfg_wreng_mon_err_mask),
                .cfg_wreng_mon_timeout_mask         (cfg_wreng_mon_timeout_mask),
                .cfg_wreng_mon_compl_mask           (cfg_wreng_mon_compl_mask),
                .cfg_wreng_mon_thresh_mask          (cfg_wreng_mon_thresh_mask),
                .cfg_wreng_mon_perf_mask            (cfg_wreng_mon_perf_mask),
                .cfg_wreng_mon_addr_mask            (cfg_wreng_mon_addr_mask),
                .cfg_wreng_mon_debug_mask           (cfg_wreng_mon_debug_mask),
                .cfg_axi_rd_xfer_beats              (cfg_axi_rd_xfer_beats),
                .cfg_axi_wr_xfer_beats              (cfg_axi_wr_xfer_beats),
                .cfg_perf_enable                    (cfg_perf_enable),
                .cfg_perf_mode                      (cfg_perf_mode),
                .cfg_perf_clear                     (cfg_perf_clear)
            );
        
            //=========================================================================
            // STREAM Core (Conditional: stream_core or stream_core_mon)
            //=========================================================================
            generate
                if (USE_AXI_MONITORS == 1) begin : g_stream_core_mon
                    // Instantiate stream_core_mon with monitors enabled
                    // NOTE: stream_core_mon doesn't exist yet - this is a placeholder
                    // For now, instantiate stream_core with USE_AXI_MONITORS=1
                    stream_core #(
                        .NUM_CHANNELS(NUM_CHANNELS),
                        .DATA_WIDTH(DATA_WIDTH),
                        .ADDR_WIDTH(ADDR_WIDTH),
                        .AXI_ID_WIDTH(AXI_ID_WIDTH),
                        .FIFO_DEPTH(SRAM_DEPTH),  // Pass SRAM_DEPTH as FIFO_DEPTH
                        .USE_AXI_MONITORS(1)      // Enable monitors
                    ) u_stream_core (
                        .clk                        (aclk),
                        .rst_n                      (aresetn),
        
                        //---------------------------------------------------------------------
                        // APB Programming Interface
                        //---------------------------------------------------------------------
                        .apb_valid                  (apb_valid),
                        .apb_ready                  (apb_ready),
                        .apb_addr                   (apb_addr),
        
                        //---------------------------------------------------------------------
                        // Configuration Interface
                        //---------------------------------------------------------------------
                        .cfg_channel_enable         (cfg_channel_enable),
                        .cfg_channel_reset          (cfg_channel_reset),
                        .cfg_sched_enable           (cfg_sched_enable),
                        .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
                        .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
                        .cfg_sched_err_enable       (cfg_sched_err_enable),
                        .cfg_sched_compl_enable     (cfg_sched_compl_enable),
                        .cfg_sched_perf_enable      (cfg_sched_perf_enable),
                        .cfg_desceng_enable         (cfg_desceng_enable),
                        .cfg_desceng_prefetch       (cfg_desceng_prefetch),
                        .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
                        .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
                        .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
                        .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
                        .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),
        
                        // Descriptor AXI Monitor Configuration
                        .cfg_desc_mon_enable        (cfg_desc_mon_enable),
                        .cfg_desc_mon_err_enable    (cfg_desc_mon_err_enable),
                        .cfg_desc_mon_perf_enable   (cfg_desc_mon_perf_enable),
                        .cfg_desc_mon_timeout_enable(cfg_desc_mon_timeout_enable),
                        .cfg_desc_mon_timeout_cycles(cfg_desc_mon_timeout_cycles),
                        .cfg_desc_mon_latency_thresh(cfg_desc_mon_latency_thresh),
                        .cfg_desc_mon_pkt_mask      (cfg_desc_mon_pkt_mask),
                        .cfg_desc_mon_err_select    (cfg_desc_mon_err_select),
                        .cfg_desc_mon_err_mask      (cfg_desc_mon_err_mask),
                        .cfg_desc_mon_timeout_mask  (cfg_desc_mon_timeout_mask),
                        .cfg_desc_mon_compl_mask    (cfg_desc_mon_compl_mask),
                        .cfg_desc_mon_thresh_mask   (cfg_desc_mon_thresh_mask),
                        .cfg_desc_mon_perf_mask     (cfg_desc_mon_perf_mask),
                        .cfg_desc_mon_addr_mask     (cfg_desc_mon_addr_mask),
                        .cfg_desc_mon_debug_mask    (cfg_desc_mon_debug_mask),
        
                        // Read Engine AXI Monitor Configuration
                        .cfg_rdeng_mon_enable       (cfg_rdeng_mon_enable),
                        .cfg_rdeng_mon_err_enable   (cfg_rdeng_mon_err_enable),
                        .cfg_rdeng_mon_perf_enable  (cfg_rdeng_mon_perf_enable),
                        .cfg_rdeng_mon_timeout_enable(cfg_rdeng_mon_timeout_enable),
                        .cfg_rdeng_mon_timeout_cycles(cfg_rdeng_mon_timeout_cycles),
                        .cfg_rdeng_mon_latency_thresh(cfg_rdeng_mon_latency_thresh),
                        .cfg_rdeng_mon_pkt_mask     (cfg_rdeng_mon_pkt_mask),
                        .cfg_rdeng_mon_err_select   (cfg_rdeng_mon_err_select),
                        .cfg_rdeng_mon_err_mask     (cfg_rdeng_mon_err_mask),
                        .cfg_rdeng_mon_timeout_mask (cfg_rdeng_mon_timeout_mask),
                        .cfg_rdeng_mon_compl_mask   (cfg_rdeng_mon_compl_mask),
                        .cfg_rdeng_mon_thresh_mask  (cfg_rdeng_mon_thresh_mask),
                        .cfg_rdeng_mon_perf_mask    (cfg_rdeng_mon_perf_mask),
                        .cfg_rdeng_mon_addr_mask    (cfg_rdeng_mon_addr_mask),
                        .cfg_rdeng_mon_debug_mask   (cfg_rdeng_mon_debug_mask),
        
                        // Write Engine AXI Monitor Configuration
                        .cfg_wreng_mon_enable       (cfg_wreng_mon_enable),
                        .cfg_wreng_mon_err_enable   (cfg_wreng_mon_err_enable),
                        .cfg_wreng_mon_perf_enable  (cfg_wreng_mon_perf_enable),
                        .cfg_wreng_mon_timeout_enable(cfg_wreng_mon_timeout_enable),
                        .cfg_wreng_mon_timeout_cycles(cfg_wreng_mon_timeout_cycles),
                        .cfg_wreng_mon_latency_thresh(cfg_wreng_mon_latency_thresh),
                        .cfg_wreng_mon_pkt_mask     (cfg_wreng_mon_pkt_mask),
                        .cfg_wreng_mon_err_select   (cfg_wreng_mon_err_select),
                        .cfg_wreng_mon_err_mask     (cfg_wreng_mon_err_mask),
                        .cfg_wreng_mon_timeout_mask (cfg_wreng_mon_timeout_mask),
                        .cfg_wreng_mon_compl_mask   (cfg_wreng_mon_compl_mask),
                        .cfg_wreng_mon_thresh_mask  (cfg_wreng_mon_thresh_mask),
                        .cfg_wreng_mon_perf_mask    (cfg_wreng_mon_perf_mask),
                        .cfg_wreng_mon_addr_mask    (cfg_wreng_mon_addr_mask),
                        .cfg_wreng_mon_debug_mask   (cfg_wreng_mon_debug_mask),
        
                        // AXI Transfer Configuration
                        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
                        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),
        
                        // Performance Profiler Configuration
                        .cfg_perf_enable            (cfg_perf_enable),
                        .cfg_perf_mode              (cfg_perf_mode),
                        .cfg_perf_clear             (cfg_perf_clear),
        
                        //---------------------------------------------------------------------
                        // Status Interface
                        //---------------------------------------------------------------------
                        .system_idle                (system_idle),
                        .descriptor_engine_idle     (descriptor_engine_idle),
                        .scheduler_idle             (scheduler_idle),
                        .scheduler_state            (scheduler_state),
                        .sched_error                (sched_error),
                        .axi_rd_all_complete        (axi_rd_all_complete),
                        .axi_wr_all_complete        (axi_wr_all_complete),
        
                        // Performance Profiler Status
                        .perf_fifo_empty            (perf_fifo_empty),
                        .perf_fifo_full             (perf_fifo_full),
                        .perf_fifo_count            (perf_fifo_count),
                        .perf_fifo_rd               (perf_fifo_rd),
                        .perf_fifo_data_low         (perf_fifo_data_low),
                        .perf_fifo_data_high        (perf_fifo_data_high),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Descriptor Fetch (256-bit)
                        //---------------------------------------------------------------------
                        .m_axi_desc_arid            (m_axi_desc_arid),
                        .m_axi_desc_araddr          (m_axi_desc_araddr),
                        .m_axi_desc_arlen           (m_axi_desc_arlen),
                        .m_axi_desc_arsize          (m_axi_desc_arsize),
                        .m_axi_desc_arburst         (m_axi_desc_arburst),
                        .m_axi_desc_arlock          (m_axi_desc_arlock),
                        .m_axi_desc_arcache         (m_axi_desc_arcache),
                        .m_axi_desc_arprot          (m_axi_desc_arprot),
                        .m_axi_desc_arqos           (m_axi_desc_arqos),
                        .m_axi_desc_arregion        (m_axi_desc_arregion),
                        .m_axi_desc_aruser          (m_axi_desc_aruser),
                        .m_axi_desc_arvalid         (m_axi_desc_arvalid),
                        .m_axi_desc_arready         (m_axi_desc_arready),
                        .m_axi_desc_rid             (m_axi_desc_rid),
                        .m_axi_desc_rdata           (m_axi_desc_rdata),
                        .m_axi_desc_rresp           (m_axi_desc_rresp),
                        .m_axi_desc_rlast           (m_axi_desc_rlast),
                        .m_axi_desc_ruser           (m_axi_desc_ruser),
                        .m_axi_desc_rvalid          (m_axi_desc_rvalid),
                        .m_axi_desc_rready          (m_axi_desc_rready),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Data Read
                        //---------------------------------------------------------------------
                        .m_axi_rd_arid              (m_axi_rd_arid),
                        .m_axi_rd_araddr            (m_axi_rd_araddr),
                        .m_axi_rd_arlen             (m_axi_rd_arlen),
                        .m_axi_rd_arsize            (m_axi_rd_arsize),
                        .m_axi_rd_arburst           (m_axi_rd_arburst),
                        .m_axi_rd_arlock            (m_axi_rd_arlock),
                        .m_axi_rd_arcache           (m_axi_rd_arcache),
                        .m_axi_rd_arprot            (m_axi_rd_arprot),
                        .m_axi_rd_arqos             (m_axi_rd_arqos),
                        .m_axi_rd_arregion          (m_axi_rd_arregion),
                        .m_axi_rd_aruser            (m_axi_rd_aruser),
                        .m_axi_rd_arvalid           (m_axi_rd_arvalid),
                        .m_axi_rd_arready           (m_axi_rd_arready),
                        .m_axi_rd_rid               (m_axi_rd_rid),
                        .m_axi_rd_rdata             (m_axi_rd_rdata),
                        .m_axi_rd_rresp             (m_axi_rd_rresp),
                        .m_axi_rd_rlast             (m_axi_rd_rlast),
                        .m_axi_rd_ruser             (m_axi_rd_ruser),
                        .m_axi_rd_rvalid            (m_axi_rd_rvalid),
                        .m_axi_rd_rready            (m_axi_rd_rready),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Data Write
                        //---------------------------------------------------------------------
                        .m_axi_wr_awid              (m_axi_wr_awid),
                        .m_axi_wr_awaddr            (m_axi_wr_awaddr),
                        .m_axi_wr_awlen             (m_axi_wr_awlen),
                        .m_axi_wr_awsize            (m_axi_wr_awsize),
                        .m_axi_wr_awburst           (m_axi_wr_awburst),
                        .m_axi_wr_awlock            (m_axi_wr_awlock),
                        .m_axi_wr_awcache           (m_axi_wr_awcache),
                        .m_axi_wr_awprot            (m_axi_wr_awprot),
                        .m_axi_wr_awqos             (m_axi_wr_awqos),
                        .m_axi_wr_awregion          (m_axi_wr_awregion),
                        .m_axi_wr_awuser            (m_axi_wr_awuser),
                        .m_axi_wr_awvalid           (m_axi_wr_awvalid),
                        .m_axi_wr_awready           (m_axi_wr_awready),
                        .m_axi_wr_wdata             (m_axi_wr_wdata),
                        .m_axi_wr_wstrb             (m_axi_wr_wstrb),
                        .m_axi_wr_wlast             (m_axi_wr_wlast),
                        .m_axi_wr_wuser             (m_axi_wr_wuser),
                        .m_axi_wr_wvalid            (m_axi_wr_wvalid),
                        .m_axi_wr_wready            (m_axi_wr_wready),
                        .m_axi_wr_bid               (m_axi_wr_bid),
                        .m_axi_wr_bresp             (m_axi_wr_bresp),
                        .m_axi_wr_buser             (m_axi_wr_buser),
                        .m_axi_wr_bvalid            (m_axi_wr_bvalid),
                        .m_axi_wr_bready            (m_axi_wr_bready),
        
                        //---------------------------------------------------------------------
                        // Status/Debug Outputs
                        //---------------------------------------------------------------------
                        .cfg_sts_desc_mon_busy          (cfg_sts_desc_mon_busy),
                        .cfg_sts_desc_mon_active_txns   (cfg_sts_desc_mon_active_txns),
                        .cfg_sts_desc_mon_error_count   (cfg_sts_desc_mon_error_count),
                        .cfg_sts_desc_mon_txn_count     (cfg_sts_desc_mon_txn_count),
                        .cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),
                        .cfg_sts_rdeng_skid_busy        (cfg_sts_rdeng_skid_busy),
                        .cfg_sts_rdeng_mon_active_txns  (cfg_sts_rdeng_mon_active_txns),
                        .cfg_sts_rdeng_mon_error_count  (cfg_sts_rdeng_mon_error_count),
                        .cfg_sts_rdeng_mon_txn_count    (cfg_sts_rdeng_mon_txn_count),
                        .cfg_sts_rdeng_mon_conflict_error(cfg_sts_rdeng_mon_conflict_error),
                        .cfg_sts_wreng_skid_busy        (cfg_sts_wreng_skid_busy),
                        .cfg_sts_wreng_mon_active_txns  (cfg_sts_wreng_mon_active_txns),
                        .cfg_sts_wreng_mon_error_count  (cfg_sts_wreng_mon_error_count),
                        .cfg_sts_wreng_mon_txn_count    (cfg_sts_wreng_mon_txn_count),
                        .cfg_sts_wreng_mon_conflict_error(cfg_sts_wreng_mon_conflict_error),
        
                        //---------------------------------------------------------------------
                        // Unified Monitor Bus Interface
                        //---------------------------------------------------------------------
                        .mon_valid                  (mon_valid),
                        .mon_ready                  (mon_ready),
                        .mon_packet                 (mon_packet)
                    );
                end else begin : g_stream_core
                    // Instantiate stream_core with monitors disabled
                    stream_core #(
                        .NUM_CHANNELS(NUM_CHANNELS),
                        .DATA_WIDTH(DATA_WIDTH),
                        .ADDR_WIDTH(ADDR_WIDTH),
                        .AXI_ID_WIDTH(AXI_ID_WIDTH),
                        .FIFO_DEPTH(SRAM_DEPTH),  // Pass SRAM_DEPTH as FIFO_DEPTH
                        .USE_AXI_MONITORS(0)      // Explicitly disable monitors
                    ) u_stream_core (
                        .clk                        (aclk),
                        .rst_n                      (aresetn),
        
                        //---------------------------------------------------------------------
                        // APB Programming Interface
                        //---------------------------------------------------------------------
                        .apb_valid                  (apb_valid),
                        .apb_ready                  (apb_ready),
                        .apb_addr                   (apb_addr),
        
                        //---------------------------------------------------------------------
                        // Configuration Interface
                        //---------------------------------------------------------------------
                        .cfg_channel_enable         (cfg_channel_enable),
                        .cfg_channel_reset          (cfg_channel_reset),
                        .cfg_sched_enable           (cfg_sched_enable),
                        .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
                        .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
                        .cfg_sched_err_enable       (cfg_sched_err_enable),
                        .cfg_sched_compl_enable     (cfg_sched_compl_enable),
                        .cfg_sched_perf_enable      (cfg_sched_perf_enable),
                        .cfg_desceng_enable         (cfg_desceng_enable),
                        .cfg_desceng_prefetch       (cfg_desceng_prefetch),
                        .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
                        .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
                        .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
                        .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
                        .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),
        
                        // Monitor config tied off internally when USE_AXI_MONITORS=0
                        .cfg_desc_mon_enable        (1'b0),
                        .cfg_desc_mon_err_enable    (1'b0),
                        .cfg_desc_mon_perf_enable   (1'b0),
                        .cfg_desc_mon_timeout_enable(1'b0),
                        .cfg_desc_mon_timeout_cycles(32'h0),
                        .cfg_desc_mon_latency_thresh(32'h0),
                        .cfg_desc_mon_pkt_mask      (16'h0),
                        .cfg_desc_mon_err_select    (4'h0),
                        .cfg_desc_mon_err_mask      (8'h0),
                        .cfg_desc_mon_timeout_mask  (8'h0),
                        .cfg_desc_mon_compl_mask    (8'h0),
                        .cfg_desc_mon_thresh_mask   (8'h0),
                        .cfg_desc_mon_perf_mask     (8'h0),
                        .cfg_desc_mon_addr_mask     (8'h0),
                        .cfg_desc_mon_debug_mask    (8'h0),
        
                        .cfg_rdeng_mon_enable       (1'b0),
                        .cfg_rdeng_mon_err_enable   (1'b0),
                        .cfg_rdeng_mon_perf_enable  (1'b0),
                        .cfg_rdeng_mon_timeout_enable(1'b0),
                        .cfg_rdeng_mon_timeout_cycles(32'h0),
                        .cfg_rdeng_mon_latency_thresh(32'h0),
                        .cfg_rdeng_mon_pkt_mask     (16'h0),
                        .cfg_rdeng_mon_err_select   (4'h0),
                        .cfg_rdeng_mon_err_mask     (8'h0),
                        .cfg_rdeng_mon_timeout_mask (8'h0),
                        .cfg_rdeng_mon_compl_mask   (8'h0),
                        .cfg_rdeng_mon_thresh_mask  (8'h0),
                        .cfg_rdeng_mon_perf_mask    (8'h0),
                        .cfg_rdeng_mon_addr_mask    (8'h0),
                        .cfg_rdeng_mon_debug_mask   (8'h0),
        
                        .cfg_wreng_mon_enable       (1'b0),
                        .cfg_wreng_mon_err_enable   (1'b0),
                        .cfg_wreng_mon_perf_enable  (1'b0),
                        .cfg_wreng_mon_timeout_enable(1'b0),
                        .cfg_wreng_mon_timeout_cycles(32'h0),
                        .cfg_wreng_mon_latency_thresh(32'h0),
                        .cfg_wreng_mon_pkt_mask     (16'h0),
                        .cfg_wreng_mon_err_select   (4'h0),
                        .cfg_wreng_mon_err_mask     (8'h0),
                        .cfg_wreng_mon_timeout_mask (8'h0),
                        .cfg_wreng_mon_compl_mask   (8'h0),
                        .cfg_wreng_mon_thresh_mask  (8'h0),
                        .cfg_wreng_mon_perf_mask    (8'h0),
                        .cfg_wreng_mon_addr_mask    (8'h0),
                        .cfg_wreng_mon_debug_mask   (8'h0),
        
                        // AXI Transfer Configuration
                        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
                        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),
        
                        // Performance Profiler Configuration
                        .cfg_perf_enable            (cfg_perf_enable),
                        .cfg_perf_mode              (cfg_perf_mode),
                        .cfg_perf_clear             (cfg_perf_clear),
        
                        //---------------------------------------------------------------------
                        // Status Interface
                        //---------------------------------------------------------------------
                        .system_idle                (system_idle),
                        .descriptor_engine_idle     (descriptor_engine_idle),
                        .scheduler_idle             (scheduler_idle),
                        .scheduler_state            (scheduler_state),
                        .sched_error                (sched_error),
                        .axi_rd_all_complete        (axi_rd_all_complete),
                        .axi_wr_all_complete        (axi_wr_all_complete),
        
                        // Performance Profiler Status
                        .perf_fifo_empty            (perf_fifo_empty),
                        .perf_fifo_full             (perf_fifo_full),
                        .perf_fifo_count            (perf_fifo_count),
                        .perf_fifo_rd               (perf_fifo_rd),
                        .perf_fifo_data_low         (perf_fifo_data_low),
                        .perf_fifo_data_high        (perf_fifo_data_high),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Descriptor Fetch (256-bit)
                        //---------------------------------------------------------------------
                        .m_axi_desc_arid            (m_axi_desc_arid),
                        .m_axi_desc_araddr          (m_axi_desc_araddr),
                        .m_axi_desc_arlen           (m_axi_desc_arlen),
                        .m_axi_desc_arsize          (m_axi_desc_arsize),
                        .m_axi_desc_arburst         (m_axi_desc_arburst),
                        .m_axi_desc_arlock          (m_axi_desc_arlock),
                        .m_axi_desc_arcache         (m_axi_desc_arcache),
                        .m_axi_desc_arprot          (m_axi_desc_arprot),
                        .m_axi_desc_arqos           (m_axi_desc_arqos),
                        .m_axi_desc_arregion        (m_axi_desc_arregion),
                        .m_axi_desc_aruser          (m_axi_desc_aruser),
                        .m_axi_desc_arvalid         (m_axi_desc_arvalid),
                        .m_axi_desc_arready         (m_axi_desc_arready),
                        .m_axi_desc_rid             (m_axi_desc_rid),
                        .m_axi_desc_rdata           (m_axi_desc_rdata),
                        .m_axi_desc_rresp           (m_axi_desc_rresp),
                        .m_axi_desc_rlast           (m_axi_desc_rlast),
                        .m_axi_desc_ruser           (m_axi_desc_ruser),
                        .m_axi_desc_rvalid          (m_axi_desc_rvalid),
                        .m_axi_desc_rready          (m_axi_desc_rready),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Data Read
                        //---------------------------------------------------------------------
                        .m_axi_rd_arid              (m_axi_rd_arid),
                        .m_axi_rd_araddr            (m_axi_rd_araddr),
                        .m_axi_rd_arlen             (m_axi_rd_arlen),
                        .m_axi_rd_arsize            (m_axi_rd_arsize),
                        .m_axi_rd_arburst           (m_axi_rd_arburst),
                        .m_axi_rd_arlock            (m_axi_rd_arlock),
                        .m_axi_rd_arcache           (m_axi_rd_arcache),
                        .m_axi_rd_arprot            (m_axi_rd_arprot),
                        .m_axi_rd_arqos             (m_axi_rd_arqos),
                        .m_axi_rd_arregion          (m_axi_rd_arregion),
                        .m_axi_rd_aruser            (m_axi_rd_aruser),
                        .m_axi_rd_arvalid           (m_axi_rd_arvalid),
                        .m_axi_rd_arready           (m_axi_rd_arready),
                        .m_axi_rd_rid               (m_axi_rd_rid),
                        .m_axi_rd_rdata             (m_axi_rd_rdata),
                        .m_axi_rd_rresp             (m_axi_rd_rresp),
                        .m_axi_rd_rlast             (m_axi_rd_rlast),
                        .m_axi_rd_ruser             (m_axi_rd_ruser),
                        .m_axi_rd_rvalid            (m_axi_rd_rvalid),
                        .m_axi_rd_rready            (m_axi_rd_rready),
        
                        //---------------------------------------------------------------------
                        // External AXI4 Master - Data Write
                        //---------------------------------------------------------------------
                        .m_axi_wr_awid              (m_axi_wr_awid),
                        .m_axi_wr_awaddr            (m_axi_wr_awaddr),
                        .m_axi_wr_awlen             (m_axi_wr_awlen),
                        .m_axi_wr_awsize            (m_axi_wr_awsize),
                        .m_axi_wr_awburst           (m_axi_wr_awburst),
                        .m_axi_wr_awlock            (m_axi_wr_awlock),
                        .m_axi_wr_awcache           (m_axi_wr_awcache),
                        .m_axi_wr_awprot            (m_axi_wr_awprot),
                        .m_axi_wr_awqos             (m_axi_wr_awqos),
                        .m_axi_wr_awregion          (m_axi_wr_awregion),
                        .m_axi_wr_awuser            (m_axi_wr_awuser),
                        .m_axi_wr_awvalid           (m_axi_wr_awvalid),
                        .m_axi_wr_awready           (m_axi_wr_awready),
                        .m_axi_wr_wdata             (m_axi_wr_wdata),
                        .m_axi_wr_wstrb             (m_axi_wr_wstrb),
                        .m_axi_wr_wlast             (m_axi_wr_wlast),
                        .m_axi_wr_wuser             (m_axi_wr_wuser),
                        .m_axi_wr_wvalid            (m_axi_wr_wvalid),
                        .m_axi_wr_wready            (m_axi_wr_wready),
                        .m_axi_wr_bid               (m_axi_wr_bid),
                        .m_axi_wr_bresp             (m_axi_wr_bresp),
                        .m_axi_wr_buser             (m_axi_wr_buser),
                        .m_axi_wr_bvalid            (m_axi_wr_bvalid),
                        .m_axi_wr_bready            (m_axi_wr_bready),
        
                        //---------------------------------------------------------------------
                        // Status/Debug Outputs (tied off when monitors disabled)
                        //---------------------------------------------------------------------
                        .cfg_sts_desc_mon_busy          (cfg_sts_desc_mon_busy),
                        .cfg_sts_desc_mon_active_txns   (cfg_sts_desc_mon_active_txns),
                        .cfg_sts_desc_mon_error_count   (cfg_sts_desc_mon_error_count),
                        .cfg_sts_desc_mon_txn_count     (cfg_sts_desc_mon_txn_count),
                        .cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),
                        .cfg_sts_rdeng_skid_busy        (cfg_sts_rdeng_skid_busy),
                        .cfg_sts_rdeng_mon_active_txns  (cfg_sts_rdeng_mon_active_txns),
                        .cfg_sts_rdeng_mon_error_count  (cfg_sts_rdeng_mon_error_count),
                        .cfg_sts_rdeng_mon_txn_count    (cfg_sts_rdeng_mon_txn_count),
                        .cfg_sts_rdeng_mon_conflict_error(cfg_sts_rdeng_mon_conflict_error),
                        .cfg_sts_wreng_skid_busy        (cfg_sts_wreng_skid_busy),
                        .cfg_sts_wreng_mon_active_txns  (cfg_sts_wreng_mon_active_txns),
                        .cfg_sts_wreng_mon_error_count  (cfg_sts_wreng_mon_error_count),
                        .cfg_sts_wreng_mon_txn_count    (cfg_sts_wreng_mon_txn_count),
                        .cfg_sts_wreng_mon_conflict_error(cfg_sts_wreng_mon_conflict_error),
        
                        //---------------------------------------------------------------------
                        // Unified Monitor Bus Interface (inactive when monitors disabled)
                        //---------------------------------------------------------------------
                        .mon_valid                  (mon_valid),
                        .mon_ready                  (1'b1),  // Always ready (no backpressure)
                        .mon_packet                 (mon_packet)
                    );
                end
            endgenerate
        
            //=========================================================================
            // Performance Profiler Interface Router
            //=========================================================================
            // Performance profiler interface is connected through cmdrsp_router
            // (see router instantiation above for perf_cfg_* and perf_fifo_* connections)
            //
            // Address map (via cmdrsp_router):
            //   0x040: PERF_CONFIG      - R/W configuration register
            //   0x044: PERF_DATA_LOW    - RO FIFO data (timestamp/elapsed)
            //   0x048: PERF_DATA_HIGH   - RO FIFO metadata (event_type, channel_id)
            //   0x04C: PERF_STATUS      - RO FIFO status (count, full, empty)
        
            //=========================================================================
            // MonBus AXI-Lite Group (Monitor Bus to AXI-Lite Converter)
            //=========================================================================
            // Conditional instantiation: Only when USE_AXI_MONITORS=1
            generate
                if (USE_AXI_MONITORS == 1) begin : g_monbus_axil
                    monbus_axil_group #(
                        .FIFO_DEPTH_ERR     (64),    // Error/interrupt FIFO depth
                        .FIFO_DEPTH_WRITE   (32),    // Write data FIFO depth
                        .ADDR_WIDTH         (32),    // AXI-Lite address width
                        .DATA_WIDTH         (32),    // AXI-Lite data width
                        .NUM_PROTOCOLS      (3)      // 3 protocols: desc, rd, wr
                    ) u_monbus_axil_group (
                        .axi_aclk           (aclk),
                        .axi_aresetn        (aresetn),
        
                        // Monitor Bus Input (from stream_core)
                        .monbus_valid       (mon_valid),
                        .monbus_ready       (mon_ready),
                        .monbus_packet      (mon_packet),
        
                        // Error/Interrupt FIFO - Slave Read Interface (AXI-Lite)
                        .s_axil_arvalid     (s_axil_err_arvalid),
                        .s_axil_arready     (s_axil_err_arready),
                        .s_axil_araddr      (s_axil_err_araddr),
                        .s_axil_arprot      (s_axil_err_arprot),
                        .s_axil_rvalid      (s_axil_err_rvalid),
                        .s_axil_rready      (s_axil_err_rready),
                        .s_axil_rdata       (s_axil_err_rdata),
                        .s_axil_rresp       (s_axil_err_rresp),
        
                        // Master Write Interface (AXI-Lite)
                        .m_axil_awvalid     (m_axil_mon_awvalid),
                        .m_axil_awready     (m_axil_mon_awready),
                        .m_axil_awaddr      (m_axil_mon_awaddr),
                        .m_axil_awprot      (m_axil_mon_awprot),
                        .m_axil_wvalid      (m_axil_mon_wvalid),
                        .m_axil_wready      (m_axil_mon_wready),
                        .m_axil_wdata       (m_axil_mon_wdata),
                        .m_axil_wstrb       (m_axil_mon_wstrb),
                        .m_axil_bvalid      (m_axil_mon_bvalid),
                        .m_axil_bready      (m_axil_mon_bready),
                        .m_axil_bresp       (m_axil_mon_bresp),
        
                        // Interrupt Output
                        .irq_out            (stream_irq),
        
                        // Configuration - Base/Limit Addresses
                        // TODO: Add registers for monitor write base/limit addresses
                        .cfg_base_addr      (32'h0000_0000),  // Temporary: disabled
                        .cfg_limit_addr     (32'h0000_0000),  // Temporary: disabled
        
                        //---------------------------------------------------------------------
                        // Protocol 0 Configuration - Descriptor AXI Monitor (DAXMON)
                        //---------------------------------------------------------------------
                        .cfg_axi_pkt_mask       ({8'h00, hwif_out.DAXMON_PKT_MASK.PKT_MASK.value}),
                        .cfg_axi_err_select     ({12'h000, hwif_out.DAXMON_ERR_CFG.ERR_SELECT.value}),
                        .cfg_axi_error_mask     ({8'h00, hwif_out.DAXMON_ERR_CFG.ERR_MASK.value}),
                        .cfg_axi_timeout_mask   ({8'h00, hwif_out.DAXMON_MASK1.TIMEOUT_MASK.value}),
                        .cfg_axi_compl_mask     ({8'h00, hwif_out.DAXMON_MASK1.COMPL_MASK.value}),
                        .cfg_axi_thresh_mask    ({8'h00, hwif_out.DAXMON_MASK2.THRESH_MASK.value}),
                        .cfg_axi_perf_mask      ({8'h00, hwif_out.DAXMON_MASK2.PERF_MASK.value}),
                        .cfg_axi_addr_mask      ({8'h00, hwif_out.DAXMON_MASK3.ADDR_MASK.value}),
                        .cfg_axi_debug_mask     ({8'h00, hwif_out.DAXMON_MASK3.DEBUG_MASK.value}),
        
                        //---------------------------------------------------------------------
                        // Protocol 1 Configuration - Read Engine Monitor (RDMON)
                        // Note: Using AXIS ports for read engine AXI monitor (protocol reuse)
                        //---------------------------------------------------------------------
                        .cfg_axis_pkt_mask      ({8'h00, hwif_out.RDMON_PKT_MASK.PKT_MASK.value}),
                        .cfg_axis_err_select    ({12'h000, hwif_out.RDMON_ERR_CFG.ERR_SELECT.value}),
                        .cfg_axis_error_mask    ({8'h00, hwif_out.RDMON_ERR_CFG.ERR_MASK.value}),
                        .cfg_axis_timeout_mask  ({8'h00, hwif_out.RDMON_MASK1.TIMEOUT_MASK.value}),
                        .cfg_axis_compl_mask    ({8'h00, hwif_out.RDMON_MASK1.COMPL_MASK.value}),
                        .cfg_axis_credit_mask   ({8'h00, hwif_out.RDMON_MASK2.THRESH_MASK.value}),   // Thresh → Credit
                        .cfg_axis_channel_mask  ({8'h00, hwif_out.RDMON_MASK2.PERF_MASK.value}),     // Perf → Channel
                        .cfg_axis_stream_mask   ({8'h00, hwif_out.RDMON_MASK3.ADDR_MASK.value}),     // Addr → Stream
        
                        //---------------------------------------------------------------------
                        // Protocol 2 Configuration - Write Engine Monitor (WRMON)
                        // Note: Using CORE ports for write engine AXI monitor (protocol reuse)
                        //---------------------------------------------------------------------
                        .cfg_core_pkt_mask      ({8'h00, hwif_out.WRMON_PKT_MASK.PKT_MASK.value}),
                        .cfg_core_err_select    ({12'h000, hwif_out.WRMON_ERR_CFG.ERR_SELECT.value}),
                        .cfg_core_error_mask    ({8'h00, hwif_out.WRMON_ERR_CFG.ERR_MASK.value}),
                        .cfg_core_timeout_mask  ({8'h00, hwif_out.WRMON_MASK1.TIMEOUT_MASK.value}),
                        .cfg_core_compl_mask    ({8'h00, hwif_out.WRMON_MASK1.COMPL_MASK.value}),
                        .cfg_core_thresh_mask   ({8'h00, hwif_out.WRMON_MASK2.THRESH_MASK.value}),
                        .cfg_core_perf_mask     ({8'h00, hwif_out.WRMON_MASK2.PERF_MASK.value}),
                        .cfg_core_debug_mask    ({8'h00, hwif_out.WRMON_MASK3.DEBUG_MASK.value}),
        
                        //---------------------------------------------------------------------
                        // Status Outputs
                        //---------------------------------------------------------------------
                        .err_fifo_full      (mon_err_fifo_full),
                        .write_fifo_full    (mon_write_fifo_full),
                        .err_fifo_count     (mon_err_fifo_count),
                        .write_fifo_count   (mon_write_fifo_count)
                    );
                end else begin : g_monbus_tieoff
                    // Monitors disabled - tie off monitor bus and AXI-Lite interfaces
                    assign mon_ready = 1'b1;  // Always ready (backpressure disabled)
                    assign stream_irq = 1'b0;  // No interrupts
        
                    // Tie off AXI-Lite slave interface (error FIFO reads)
                    assign s_axil_err_arready = 1'b1;
                    assign s_axil_err_rvalid = 1'b0;
                    assign s_axil_err_rdata = 32'h0;
                    assign s_axil_err_rresp = 2'b00;
        
                    // Tie off AXI-Lite master interface (monitor writes)
                    assign m_axil_mon_awvalid = 1'b0;
                    assign m_axil_mon_awaddr = 32'h0;
                    assign m_axil_mon_awprot = 3'b000;
                    assign m_axil_mon_wvalid = 1'b0;
                    assign m_axil_mon_wdata = 32'h0;
                    assign m_axil_mon_wstrb = 4'h0;
                    assign m_axil_mon_bready = 1'b0;
        
                    // Tie off status signals
                    assign mon_err_fifo_full = 1'b0;
                    assign mon_write_fifo_full = 1'b0;
                    assign mon_err_fifo_count = 8'h00;
                    assign mon_write_fifo_count = 8'h00;
                end
            endgenerate
        
        endmodule : stream_top_ch8
        
        
