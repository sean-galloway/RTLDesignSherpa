//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: stream_config_block
        // Purpose: Configuration Mapping Block - PeakRDL to STREAM Core
        //
        // Description:
        //   Maps PeakRDL-generated register outputs to stream_core configuration inputs.
        //   This module provides a clean interface layer between the register file and
        //   the STREAM DMA engine core.
        //
        //   Key Functions:
        //   1. Field extraction from packed register values
        //   2. Bit width conversion (register fields → configuration signals)
        //   3. Default value assignment for unimplemented features
        //   4. Clock domain handling (registers in APB domain, outputs in AXI domain)
        //
        //   Register Groups Mapped:
        //   - Global control and channel enables
        //   - Scheduler configuration and timeouts
        //   - Descriptor engine configuration
        //   - Monitor configuration (descriptor, read engine, write engine)
        //   - AXI transfer parameters
        //   - Performance profiler controls
        //
        // Documentation: rtl/top/INTEGRATION_ARCHITECTURE.md
        // Subsystem: stream_top
        //
        // Author: sean galloway
        // Created: 2025-11-21
        
        `timescale 1ns / 1ps
        
        `include "reset_defs.svh"
        
        module stream_config_block #(
            parameter int NUM_CHANNELS = 8,
            parameter int ADDR_WIDTH = 64
        ) (
            // Clock and Reset
 002323     input  logic                        clk,
%000001     input  logic                        rst_n,
        
            //=========================================================================
            // PeakRDL Register Outputs (from stream_regs)
            //=========================================================================
        
            // Global Control
%000001     input  logic                        reg_global_ctrl_global_en,
%000000     input  logic                        reg_global_ctrl_global_rst,
        
            // Channel Control
%000001     input  logic [7:0]                  reg_channel_enable_ch_en,
%000000     input  logic [7:0]                  reg_channel_reset_ch_rst,
        
            // Scheduler Configuration
%000000     input  logic [15:0]                 reg_sched_timeout_cycles_timeout_cycles,
%000001     input  logic                        reg_sched_config_sched_en,
%000001     input  logic                        reg_sched_config_timeout_en,
%000001     input  logic                        reg_sched_config_err_en,
%000001     input  logic                        reg_sched_config_compl_en,
%000000     input  logic                        reg_sched_config_perf_en,
        
            // Descriptor Engine Configuration
%000001     input  logic                        reg_desceng_config_desceng_en,
%000000     input  logic                        reg_desceng_config_prefetch_en,
%000000     input  logic [3:0]                  reg_desceng_config_fifo_thresh,
%000000     input  logic [31:0]                 reg_desceng_addr0_base_addr0_base,
%000001     input  logic [31:0]                 reg_desceng_addr0_limit_addr0_limit,
%000000     input  logic [31:0]                 reg_desceng_addr1_base_addr1_base,
%000001     input  logic [31:0]                 reg_desceng_addr1_limit_addr1_limit,
        
            // Descriptor AXI Monitor Configuration
%000001     input  logic                        reg_daxmon_enable_mon_en,
%000001     input  logic                        reg_daxmon_enable_err_en,
%000000     input  logic                        reg_daxmon_enable_compl_en,
%000001     input  logic                        reg_daxmon_enable_timeout_en,
%000000     input  logic                        reg_daxmon_enable_perf_en,
%000000     input  logic [31:0]                 reg_daxmon_timeout_timeout_cycles,
%000000     input  logic [31:0]                 reg_daxmon_latency_thresh_latency_thresh,
%000001     input  logic [15:0]                 reg_daxmon_pkt_mask_pkt_mask,
%000000     input  logic [3:0]                  reg_daxmon_err_cfg_err_select,
%000001     input  logic [7:0]                  reg_daxmon_err_cfg_err_mask,
%000001     input  logic [7:0]                  reg_daxmon_mask1_timeout_mask,
%000000     input  logic [7:0]                  reg_daxmon_mask1_compl_mask,
%000001     input  logic [7:0]                  reg_daxmon_mask2_thresh_mask,
%000000     input  logic [7:0]                  reg_daxmon_mask2_perf_mask,
%000001     input  logic [7:0]                  reg_daxmon_mask3_addr_mask,
%000000     input  logic [7:0]                  reg_daxmon_mask3_debug_mask,
        
            // Read Engine AXI Monitor Configuration
%000001     input  logic                        reg_rdmon_enable_mon_en,
%000001     input  logic                        reg_rdmon_enable_err_en,
%000000     input  logic                        reg_rdmon_enable_compl_en,
%000001     input  logic                        reg_rdmon_enable_timeout_en,
%000000     input  logic                        reg_rdmon_enable_perf_en,
%000000     input  logic [31:0]                 reg_rdmon_timeout_timeout_cycles,
%000000     input  logic [31:0]                 reg_rdmon_latency_thresh_latency_thresh,
%000001     input  logic [15:0]                 reg_rdmon_pkt_mask_pkt_mask,
%000000     input  logic [3:0]                  reg_rdmon_err_cfg_err_select,
%000001     input  logic [7:0]                  reg_rdmon_err_cfg_err_mask,
%000001     input  logic [7:0]                  reg_rdmon_mask1_timeout_mask,
%000000     input  logic [7:0]                  reg_rdmon_mask1_compl_mask,
%000001     input  logic [7:0]                  reg_rdmon_mask2_thresh_mask,
%000000     input  logic [7:0]                  reg_rdmon_mask2_perf_mask,
%000001     input  logic [7:0]                  reg_rdmon_mask3_addr_mask,
%000000     input  logic [7:0]                  reg_rdmon_mask3_debug_mask,
        
            // Write Engine AXI Monitor Configuration
%000001     input  logic                        reg_wrmon_enable_mon_en,
%000001     input  logic                        reg_wrmon_enable_err_en,
%000000     input  logic                        reg_wrmon_enable_compl_en,
%000001     input  logic                        reg_wrmon_enable_timeout_en,
%000000     input  logic                        reg_wrmon_enable_perf_en,
%000000     input  logic [31:0]                 reg_wrmon_timeout_timeout_cycles,
%000000     input  logic [31:0]                 reg_wrmon_latency_thresh_latency_thresh,
%000001     input  logic [15:0]                 reg_wrmon_pkt_mask_pkt_mask,
%000000     input  logic [3:0]                  reg_wrmon_err_cfg_err_select,
%000001     input  logic [7:0]                  reg_wrmon_err_cfg_err_mask,
%000001     input  logic [7:0]                  reg_wrmon_mask1_timeout_mask,
%000000     input  logic [7:0]                  reg_wrmon_mask1_compl_mask,
%000001     input  logic [7:0]                  reg_wrmon_mask2_thresh_mask,
%000000     input  logic [7:0]                  reg_wrmon_mask2_perf_mask,
%000001     input  logic [7:0]                  reg_wrmon_mask3_addr_mask,
%000000     input  logic [7:0]                  reg_wrmon_mask3_debug_mask,
        
            // AXI Transfer Configuration
%000000     input  logic [7:0]                  reg_axi_xfer_config_rd_xfer_beats,
%000000     input  logic [7:0]                  reg_axi_xfer_config_wr_xfer_beats,
        
            // Performance Profiler Configuration
%000000     input  logic                        reg_perf_config_perf_en,
%000000     input  logic                        reg_perf_config_perf_mode,
%000000     input  logic                        reg_perf_config_perf_clear,
        
            //=========================================================================
            // STREAM Core Configuration Outputs
            //=========================================================================
        
            // Global and Channel Control
%000001     output logic [NUM_CHANNELS-1:0]     cfg_channel_enable,
%000000     output logic [NUM_CHANNELS-1:0]     cfg_channel_reset,
        
            // Scheduler Configuration
%000001     output logic                        cfg_sched_enable,
%000000     output logic [15:0]                 cfg_sched_timeout_cycles,
%000001     output logic                        cfg_sched_timeout_enable,
%000001     output logic                        cfg_sched_err_enable,
%000001     output logic                        cfg_sched_compl_enable,
%000000     output logic                        cfg_sched_perf_enable,
        
            // Descriptor Engine Configuration
%000001     output logic                        cfg_desceng_enable,
%000000     output logic                        cfg_desceng_prefetch,
%000000     output logic [3:0]                  cfg_desceng_fifo_thresh,
%000000     output logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_base,
%000000     output logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_limit,
%000000     output logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_base,
%000000     output logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_limit,
        
            // Descriptor AXI Monitor Configuration
%000001     output logic                        cfg_desc_mon_enable,
%000001     output logic                        cfg_desc_mon_err_enable,
%000000     output logic                        cfg_desc_mon_perf_enable,
%000001     output logic                        cfg_desc_mon_timeout_enable,
%000000     output logic [31:0]                 cfg_desc_mon_timeout_cycles,
%000000     output logic [31:0]                 cfg_desc_mon_latency_thresh,
%000001     output logic [15:0]                 cfg_desc_mon_pkt_mask,
%000000     output logic [3:0]                  cfg_desc_mon_err_select,
%000001     output logic [7:0]                  cfg_desc_mon_err_mask,
%000001     output logic [7:0]                  cfg_desc_mon_timeout_mask,
%000000     output logic [7:0]                  cfg_desc_mon_compl_mask,
%000001     output logic [7:0]                  cfg_desc_mon_thresh_mask,
%000000     output logic [7:0]                  cfg_desc_mon_perf_mask,
%000001     output logic [7:0]                  cfg_desc_mon_addr_mask,
%000000     output logic [7:0]                  cfg_desc_mon_debug_mask,
        
            // Read Engine AXI Monitor Configuration
%000001     output logic                        cfg_rdeng_mon_enable,
%000001     output logic                        cfg_rdeng_mon_err_enable,
%000000     output logic                        cfg_rdeng_mon_perf_enable,
%000001     output logic                        cfg_rdeng_mon_timeout_enable,
%000000     output logic [31:0]                 cfg_rdeng_mon_timeout_cycles,
%000000     output logic [31:0]                 cfg_rdeng_mon_latency_thresh,
%000001     output logic [15:0]                 cfg_rdeng_mon_pkt_mask,
%000000     output logic [3:0]                  cfg_rdeng_mon_err_select,
%000001     output logic [7:0]                  cfg_rdeng_mon_err_mask,
%000001     output logic [7:0]                  cfg_rdeng_mon_timeout_mask,
%000000     output logic [7:0]                  cfg_rdeng_mon_compl_mask,
%000001     output logic [7:0]                  cfg_rdeng_mon_thresh_mask,
%000000     output logic [7:0]                  cfg_rdeng_mon_perf_mask,
%000001     output logic [7:0]                  cfg_rdeng_mon_addr_mask,
%000000     output logic [7:0]                  cfg_rdeng_mon_debug_mask,
        
            // Write Engine AXI Monitor Configuration
%000001     output logic                        cfg_wreng_mon_enable,
%000001     output logic                        cfg_wreng_mon_err_enable,
%000000     output logic                        cfg_wreng_mon_perf_enable,
%000001     output logic                        cfg_wreng_mon_timeout_enable,
%000000     output logic [31:0]                 cfg_wreng_mon_timeout_cycles,
%000000     output logic [31:0]                 cfg_wreng_mon_latency_thresh,
%000001     output logic [15:0]                 cfg_wreng_mon_pkt_mask,
%000000     output logic [3:0]                  cfg_wreng_mon_err_select,
%000001     output logic [7:0]                  cfg_wreng_mon_err_mask,
%000001     output logic [7:0]                  cfg_wreng_mon_timeout_mask,
%000000     output logic [7:0]                  cfg_wreng_mon_compl_mask,
%000001     output logic [7:0]                  cfg_wreng_mon_thresh_mask,
%000000     output logic [7:0]                  cfg_wreng_mon_perf_mask,
%000001     output logic [7:0]                  cfg_wreng_mon_addr_mask,
%000000     output logic [7:0]                  cfg_wreng_mon_debug_mask,
        
            // AXI Transfer Configuration
%000000     output logic [7:0]                  cfg_axi_rd_xfer_beats,
%000000     output logic [7:0]                  cfg_axi_wr_xfer_beats,
        
            // Performance Profiler Configuration
%000000     output logic                        cfg_perf_enable,
%000000     output logic                        cfg_perf_mode,
%000000     output logic                        cfg_perf_clear
        );
        
            //=========================================================================
            // Configuration Mapping Logic
            //=========================================================================
        
            // Most mappings are direct assignments with optional gating by global enable
        
            //-------------------------------------------------------------------------
            // Global and Channel Control
            //-------------------------------------------------------------------------
        
            // Gate all channel enables by global enable
            assign cfg_channel_enable = reg_channel_enable_ch_en & {NUM_CHANNELS{reg_global_ctrl_global_en}};
        
            // Channel resets are OR'd with global reset
            assign cfg_channel_reset = reg_channel_reset_ch_rst | {NUM_CHANNELS{reg_global_ctrl_global_rst}};
        
            //-------------------------------------------------------------------------
            // Scheduler Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_sched_enable = reg_sched_config_sched_en & reg_global_ctrl_global_en;
            assign cfg_sched_timeout_cycles = reg_sched_timeout_cycles_timeout_cycles;
            assign cfg_sched_timeout_enable = reg_sched_config_timeout_en;
            assign cfg_sched_err_enable = reg_sched_config_err_en;
            assign cfg_sched_compl_enable = reg_sched_config_compl_en;
            assign cfg_sched_perf_enable = reg_sched_config_perf_en;
        
            //-------------------------------------------------------------------------
            // Descriptor Engine Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_desceng_enable = reg_desceng_config_desceng_en & reg_global_ctrl_global_en;
            assign cfg_desceng_prefetch = reg_desceng_config_prefetch_en;
            assign cfg_desceng_fifo_thresh = reg_desceng_config_fifo_thresh;
        
            // Zero-extend 32-bit register addresses to ADDR_WIDTH (typically 64-bit)
            assign cfg_desceng_addr0_base = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr0_base_addr0_base};
            assign cfg_desceng_addr0_limit = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr0_limit_addr0_limit};
            assign cfg_desceng_addr1_base = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr1_base_addr1_base};
            assign cfg_desceng_addr1_limit = {{(ADDR_WIDTH-32){1'b0}}, reg_desceng_addr1_limit_addr1_limit};
        
            //-------------------------------------------------------------------------
            // Descriptor AXI Monitor Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_desc_mon_enable = reg_daxmon_enable_mon_en & reg_global_ctrl_global_en;
            assign cfg_desc_mon_err_enable = reg_daxmon_enable_err_en;
            assign cfg_desc_mon_perf_enable = reg_daxmon_enable_perf_en;
            assign cfg_desc_mon_timeout_enable = reg_daxmon_enable_timeout_en;
            assign cfg_desc_mon_timeout_cycles = reg_daxmon_timeout_timeout_cycles;
            assign cfg_desc_mon_latency_thresh = reg_daxmon_latency_thresh_latency_thresh;
            assign cfg_desc_mon_pkt_mask = reg_daxmon_pkt_mask_pkt_mask;
            assign cfg_desc_mon_err_select = reg_daxmon_err_cfg_err_select;
            assign cfg_desc_mon_err_mask = reg_daxmon_err_cfg_err_mask;
            assign cfg_desc_mon_timeout_mask = reg_daxmon_mask1_timeout_mask;
            assign cfg_desc_mon_compl_mask = reg_daxmon_mask1_compl_mask;
            assign cfg_desc_mon_thresh_mask = reg_daxmon_mask2_thresh_mask;
            assign cfg_desc_mon_perf_mask = reg_daxmon_mask2_perf_mask;
            assign cfg_desc_mon_addr_mask = reg_daxmon_mask3_addr_mask;
            assign cfg_desc_mon_debug_mask = reg_daxmon_mask3_debug_mask;
        
            //-------------------------------------------------------------------------
            // Read Engine AXI Monitor Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_rdeng_mon_enable = reg_rdmon_enable_mon_en & reg_global_ctrl_global_en;
            assign cfg_rdeng_mon_err_enable = reg_rdmon_enable_err_en;
            assign cfg_rdeng_mon_perf_enable = reg_rdmon_enable_perf_en;
            assign cfg_rdeng_mon_timeout_enable = reg_rdmon_enable_timeout_en;
            assign cfg_rdeng_mon_timeout_cycles = reg_rdmon_timeout_timeout_cycles;
            assign cfg_rdeng_mon_latency_thresh = reg_rdmon_latency_thresh_latency_thresh;
            assign cfg_rdeng_mon_pkt_mask = reg_rdmon_pkt_mask_pkt_mask;
            assign cfg_rdeng_mon_err_select = reg_rdmon_err_cfg_err_select;
            assign cfg_rdeng_mon_err_mask = reg_rdmon_err_cfg_err_mask;
            assign cfg_rdeng_mon_timeout_mask = reg_rdmon_mask1_timeout_mask;
            assign cfg_rdeng_mon_compl_mask = reg_rdmon_mask1_compl_mask;
            assign cfg_rdeng_mon_thresh_mask = reg_rdmon_mask2_thresh_mask;
            assign cfg_rdeng_mon_perf_mask = reg_rdmon_mask2_perf_mask;
            assign cfg_rdeng_mon_addr_mask = reg_rdmon_mask3_addr_mask;
            assign cfg_rdeng_mon_debug_mask = reg_rdmon_mask3_debug_mask;
        
            //-------------------------------------------------------------------------
            // Write Engine AXI Monitor Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_wreng_mon_enable = reg_wrmon_enable_mon_en & reg_global_ctrl_global_en;
            assign cfg_wreng_mon_err_enable = reg_wrmon_enable_err_en;
            assign cfg_wreng_mon_perf_enable = reg_wrmon_enable_perf_en;
            assign cfg_wreng_mon_timeout_enable = reg_wrmon_enable_timeout_en;
            assign cfg_wreng_mon_timeout_cycles = reg_wrmon_timeout_timeout_cycles;
            assign cfg_wreng_mon_latency_thresh = reg_wrmon_latency_thresh_latency_thresh;
            assign cfg_wreng_mon_pkt_mask = reg_wrmon_pkt_mask_pkt_mask;
            assign cfg_wreng_mon_err_select = reg_wrmon_err_cfg_err_select;
            assign cfg_wreng_mon_err_mask = reg_wrmon_err_cfg_err_mask;
            assign cfg_wreng_mon_timeout_mask = reg_wrmon_mask1_timeout_mask;
            assign cfg_wreng_mon_compl_mask = reg_wrmon_mask1_compl_mask;
            assign cfg_wreng_mon_thresh_mask = reg_wrmon_mask2_thresh_mask;
            assign cfg_wreng_mon_perf_mask = reg_wrmon_mask2_perf_mask;
            assign cfg_wreng_mon_addr_mask = reg_wrmon_mask3_addr_mask;
            assign cfg_wreng_mon_debug_mask = reg_wrmon_mask3_debug_mask;
        
            //-------------------------------------------------------------------------
            // AXI Transfer Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_axi_rd_xfer_beats = reg_axi_xfer_config_rd_xfer_beats;
            assign cfg_axi_wr_xfer_beats = reg_axi_xfer_config_wr_xfer_beats;
        
            //-------------------------------------------------------------------------
            // Performance Profiler Configuration
            //-------------------------------------------------------------------------
        
            assign cfg_perf_enable = reg_perf_config_perf_en & reg_global_ctrl_global_en;
            assign cfg_perf_mode = reg_perf_config_perf_mode;
            assign cfg_perf_clear = reg_perf_config_perf_clear;
        
        endmodule : stream_config_block
        
