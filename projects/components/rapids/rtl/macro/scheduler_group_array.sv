// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_group_array
// Purpose: Scheduler Group Array module
//
// Documentation: projects/components/rapids_macro/PRD.md
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"

module scheduler_group_array
    import monitor_pkg::*;
#(
    // Channel Configuration
    parameter int CHANNEL_COUNT = 32,
    parameter int CHAN_WIDTH = $clog2(CHANNEL_COUNT),

    // Data and Address Widths
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int CREDIT_WIDTH = 8,

    // Timing Parameters
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int EARLY_WARNING_THRESHOLD = 4,

    // AXI Skid Buffer Depths
    parameter int AXI_SKID_DEPTH_AR = 2,
    parameter int AXI_SKID_DEPTH_R  = 4,
    parameter int AXI_SKID_DEPTH_AW = 2,
    parameter int AXI_SKID_DEPTH_W  = 2,
    parameter int AXI_SKID_DEPTH_B  = 2,

    // AXI Monitor Parameters
    parameter int AXI_MAX_TRANSACTIONS = 16,
    parameter bit AXI_ENABLE_FILTERING = 1,
    parameter bit AXI_ADD_PIPELINE_STAGE = 0,

    // AXI Clock Gating Parameters
    parameter bit AXI_ENABLE_CLOCK_GATING = 1,
    parameter int AXI_CG_IDLE_CYCLES = 8,

    // Monitor Bus Parameters
    parameter int DESC_MON_AGENT_BASE = 16,     // 0x10 base for descriptor engines
    parameter int PROG_MON_AGENT_BASE = 32,     // 0x20 base for program engines
    parameter int SCHED_MON_AGENT_BASE = 48,    // 0x30 base for schedulers
    parameter int AXI_RD_MON_AGENT_ID = 10,     // 0x0A for AXI read master monitor
    parameter int AXI_WR_MON_AGENT_ID = 11,     // 0x0B for AXI write master monitor
    parameter int MON_UNIT_ID = 1,              // 0x1

    // MonBus Arbiter Parameters
    parameter int MONBUS_INPUT_SKID_ENABLE = 1,
    parameter int MONBUS_OUTPUT_SKID_ENABLE = 1,
    parameter int MONBUS_INPUT_SKID_DEPTH = 2,
    parameter int MONBUS_OUTPUT_SKID_DEPTH = 4,

    // AXI4 Control Read/Write Masters
    parameter int CTRLRD_MON_AGENT_ID = 12,     // 0x0C for control read master monitor
    parameter int CTRLWR_MON_AGENT_ID = 13,     // 0x0D for control write master monitor

    // Total monitor bus clients: CHANNEL_COUNT scheduler_groups + 3 AXI masters
    // (desc read, ctrlrd read, ctrlwr write)
    // NOTE: Program engine removed - was previously 4th AXI master
    localparam int MONBUS_CLIENTS = CHANNEL_COUNT + 3
) (
    // Global Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // ========================================================================
    // Per-Channel Interfaces (Array of CHANNEL_COUNT channels)
    // ========================================================================

    // APB Programming Interface (for descriptor fetch) - per channel
    input  logic [CHANNEL_COUNT-1:0]    apb_valid,
    output logic [CHANNEL_COUNT-1:0]    apb_ready,
    input  logic [ADDR_WIDTH-1:0]       apb_addr [CHANNEL_COUNT],

    // CDA Packet Interface (from Network Slave) - per channel, formerly RDA
    input  logic [CHANNEL_COUNT-1:0]    cda_valid,
    output logic [CHANNEL_COUNT-1:0]    cda_ready,
    input  logic [DATA_WIDTH-1:0]       cda_packet [CHANNEL_COUNT],
    input  logic [CHAN_WIDTH-1:0]       cda_channel [CHANNEL_COUNT],

    // EOS Completion Interface (from SRAM Control) - per channel
    input  logic [CHANNEL_COUNT-1:0]    eos_completion_valid,
    output logic [CHANNEL_COUNT-1:0]    eos_completion_ready,
    input  logic [CHAN_WIDTH-1:0]       eos_completion_channel [CHANNEL_COUNT],

    // Configuration Interface - per channel
    input  logic [CHANNEL_COUNT-1:0]    cfg_idle_mode,
    input  logic [CHANNEL_COUNT-1:0]    cfg_channel_wait,
    input  logic [CHANNEL_COUNT-1:0]    cfg_channel_enable,
    input  logic [CHANNEL_COUNT-1:0]    cfg_use_credit,
    input  logic [3:0]                  cfg_initial_credit [CHANNEL_COUNT],
    input  logic [CHANNEL_COUNT-1:0]    credit_increment,
    input  logic [CHANNEL_COUNT-1:0]    cfg_prefetch_enable,
    input  logic [3:0]                  cfg_fifo_threshold [CHANNEL_COUNT],
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_base [CHANNEL_COUNT],
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_limit [CHANNEL_COUNT],
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_base [CHANNEL_COUNT],
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_limit [CHANNEL_COUNT],
    input  logic [CHANNEL_COUNT-1:0]    cfg_channel_reset,
    input  logic [7:0]                  cfg_ctrlrd_max_try [CHANNEL_COUNT],

    // Status Interface - per channel
    output logic [CHANNEL_COUNT-1:0]    descriptor_engine_idle,
    output logic [CHANNEL_COUNT-1:0]    program_engine_idle,
    output logic [CHANNEL_COUNT-1:0]    scheduler_idle,
    output logic [31:0]                 descriptor_credit_counter [CHANNEL_COUNT],
    output logic [5:0]                  fsm_state [CHANNEL_COUNT],
    output logic [CHANNEL_COUNT-1:0]    scheduler_error,
    output logic [CHANNEL_COUNT-1:0]    backpressure_warning,

    // Data Mover Interface - per channel
    output logic [CHANNEL_COUNT-1:0]    data_valid,
    input  logic [CHANNEL_COUNT-1:0]    data_ready,
    output logic [63:0]                 data_address [CHANNEL_COUNT],
    output logic [31:0]                 data_length [CHANNEL_COUNT],
    output logic [1:0]                  data_type [CHANNEL_COUNT],
    output logic [CHANNEL_COUNT-1:0]    data_eos,

    input  logic [31:0]                 data_transfer_length [CHANNEL_COUNT],
    input  logic [CHANNEL_COUNT-1:0]    data_error,
    input  logic [CHANNEL_COUNT-1:0]    data_done_strobe,

    // Address Alignment Bus Interface - per channel (using RAPIDS types)
    output alignment_info_t             data_alignment_info [CHANNEL_COUNT],
    output logic [CHANNEL_COUNT-1:0]    data_alignment_valid,
    input  logic [CHANNEL_COUNT-1:0]    data_alignment_ready,
    input  logic [CHANNEL_COUNT-1:0]    data_alignment_next,
    output transfer_phase_t             data_transfer_phase [CHANNEL_COUNT],
    output logic [CHANNEL_COUNT-1:0]    data_sequence_complete,

    // RDA Credit Return Interface - per channel
    output logic [CHANNEL_COUNT-1:0]    rda_complete_valid,
    input  logic [CHANNEL_COUNT-1:0]    rda_complete_ready,
    output logic [CHAN_WIDTH-1:0]       rda_complete_channel [CHANNEL_COUNT],

    // ========================================================================
    // Shared AXI4 Master Read Interface (Descriptor Engine - with MonBus)
    // ========================================================================
    output logic [AXI_ID_WIDTH-1:0]     m_axi_desc_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_desc_araddr,
    output logic [7:0]                  m_axi_desc_arlen,
    output logic [2:0]                  m_axi_desc_arsize,
    output logic [1:0]                  m_axi_desc_arburst,
    output logic                        m_axi_desc_arlock,
    output logic [3:0]                  m_axi_desc_arcache,
    output logic [2:0]                  m_axi_desc_arprot,
    output logic [3:0]                  m_axi_desc_arqos,
    output logic [3:0]                  m_axi_desc_arregion,
    output logic                        m_axi_desc_arvalid,
    input  logic                        m_axi_desc_arready,

    input  logic [AXI_ID_WIDTH-1:0]     m_axi_desc_rid,
    input  logic [DATA_WIDTH-1:0]       m_axi_desc_rdata,
    input  logic [1:0]                  m_axi_desc_rresp,
    input  logic                        m_axi_desc_rlast,
    input  logic                        m_axi_desc_rvalid,
    output logic                        m_axi_desc_rready,

    // ========================================================================
    // Shared AXI4 Master Read Interface (Control Read Engine - with MonBus)
    // ========================================================================
    output logic [AXI_ID_WIDTH-1:0]     m_axi_ctrlrd_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_ctrlrd_araddr,
    output logic [7:0]                  m_axi_ctrlrd_arlen,
    output logic [2:0]                  m_axi_ctrlrd_arsize,
    output logic [1:0]                  m_axi_ctrlrd_arburst,
    output logic                        m_axi_ctrlrd_arlock,
    output logic [3:0]                  m_axi_ctrlrd_arcache,
    output logic [2:0]                  m_axi_ctrlrd_arprot,
    output logic [3:0]                  m_axi_ctrlrd_arqos,
    output logic [3:0]                  m_axi_ctrlrd_arregion,
    output logic                        m_axi_ctrlrd_arvalid,
    input  logic                        m_axi_ctrlrd_arready,

    input  logic [AXI_ID_WIDTH-1:0]     m_axi_ctrlrd_rid,
    input  logic [31:0]                 m_axi_ctrlrd_rdata,
    input  logic [1:0]                  m_axi_ctrlrd_rresp,
    input  logic                        m_axi_ctrlrd_rlast,
    input  logic                        m_axi_ctrlrd_rvalid,
    output logic                        m_axi_ctrlrd_rready,

    // ========================================================================
    // Shared AXI4 Master Write Interface (Control Write Engine - with MonBus)
    // ========================================================================
    output logic [AXI_ID_WIDTH-1:0]     m_axi_ctrlwr_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_ctrlwr_awaddr,
    output logic [7:0]                  m_axi_ctrlwr_awlen,
    output logic [2:0]                  m_axi_ctrlwr_awsize,
    output logic [1:0]                  m_axi_ctrlwr_awburst,
    output logic                        m_axi_ctrlwr_awlock,
    output logic [3:0]                  m_axi_ctrlwr_awcache,
    output logic [2:0]                  m_axi_ctrlwr_awprot,
    output logic [3:0]                  m_axi_ctrlwr_awqos,
    output logic [3:0]                  m_axi_ctrlwr_awregion,
    output logic                        m_axi_ctrlwr_awvalid,
    input  logic                        m_axi_ctrlwr_awready,

    output logic [31:0]                 m_axi_ctrlwr_wdata,
    output logic [3:0]                  m_axi_ctrlwr_wstrb,
    output logic                        m_axi_ctrlwr_wlast,
    output logic                        m_axi_ctrlwr_wvalid,
    input  logic                        m_axi_ctrlwr_wready,

    input  logic [AXI_ID_WIDTH-1:0]     m_axi_ctrlwr_bid,
    input  logic [1:0]                  m_axi_ctrlwr_bresp,
    input  logic                        m_axi_ctrlwr_bvalid,
    output logic                        m_axi_ctrlwr_bready,

    // ========================================================================
    // AXI Monitor Configuration (Shared for both AXI masters)
    // ========================================================================
    input  logic                        cfg_axi_monitor_enable,
    input  logic                        cfg_axi_error_enable,
    input  logic                        cfg_axi_timeout_enable,
    input  logic                        cfg_axi_perf_enable,
    input  logic [15:0]                 cfg_axi_timeout_cycles,
    input  logic [31:0]                 cfg_axi_latency_threshold,

    // AXI Filtering Configuration
    input  logic [15:0]                 cfg_axi_pkt_mask,
    input  logic [15:0]                 cfg_axi_err_select,
    input  logic [15:0]                 cfg_axi_error_mask,
    input  logic [15:0]                 cfg_axi_timeout_mask,
    input  logic [15:0]                 cfg_axi_compl_mask,
    input  logic [15:0]                 cfg_axi_thresh_mask,
    input  logic [15:0]                 cfg_axi_perf_mask,
    input  logic [15:0]                 cfg_axi_addr_mask,
    input  logic [15:0]                 cfg_axi_debug_mask,

    // Clock Gating Configuration
    input  logic                        cfg_cg_enable,
    input  logic [7:0]                  cfg_cg_idle_threshold,
    input  logic                        cfg_cg_force_on,
    input  logic                        cfg_cg_gate_monitor,
    input  logic                        cfg_cg_gate_reporter,
    input  logic                        cfg_cg_gate_timers,

    // ========================================================================
    // Aggregated Monitor Bus Output
    // ========================================================================
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet,

    // ========================================================================
    // Array-Level Status and Debug
    // ========================================================================
    output logic [7:0]                  active_channels,
    output logic [15:0]                 total_error_count,
    output logic [31:0]                 total_transaction_count
);

    //=========================================================================
    // Internal Signals - Scheduler Group Interconnect
    //=========================================================================

    // Descriptor Engine AXI Interface (per channel, before arbitration)
    logic [CHANNEL_COUNT-1:0]           desc_ar_valid;
    logic [CHANNEL_COUNT-1:0]           desc_ar_ready;
    logic [ADDR_WIDTH-1:0]              desc_ar_addr [CHANNEL_COUNT];
    logic [7:0]                         desc_ar_len [CHANNEL_COUNT];
    logic [2:0]                         desc_ar_size [CHANNEL_COUNT];
    logic [1:0]                         desc_ar_burst [CHANNEL_COUNT];
    logic [AXI_ID_WIDTH-1:0]            desc_ar_id [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           desc_ar_lock;
    logic [3:0]                         desc_ar_cache [CHANNEL_COUNT];
    logic [2:0]                         desc_ar_prot [CHANNEL_COUNT];
    logic [3:0]                         desc_ar_qos [CHANNEL_COUNT];
    logic [3:0]                         desc_ar_region [CHANNEL_COUNT];

    logic [CHANNEL_COUNT-1:0]           desc_r_valid;
    logic [CHANNEL_COUNT-1:0]           desc_r_ready;
    logic [DATA_WIDTH-1:0]              desc_r_data [CHANNEL_COUNT];
    logic [1:0]                         desc_r_resp [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           desc_r_last;
    logic [AXI_ID_WIDTH-1:0]            desc_r_id [CHANNEL_COUNT];

    // Program Engine AXI Interface (per channel, before arbitration)
    logic [CHANNEL_COUNT-1:0]           prog_aw_valid;
    logic [CHANNEL_COUNT-1:0]           prog_aw_ready;
    logic [ADDR_WIDTH-1:0]              prog_aw_addr [CHANNEL_COUNT];
    logic [7:0]                         prog_aw_len [CHANNEL_COUNT];
    logic [2:0]                         prog_aw_size [CHANNEL_COUNT];
    logic [1:0]                         prog_aw_burst [CHANNEL_COUNT];
    logic [AXI_ID_WIDTH-1:0]            prog_aw_id [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           prog_aw_lock;
    logic [3:0]                         prog_aw_cache [CHANNEL_COUNT];
    logic [2:0]                         prog_aw_prot [CHANNEL_COUNT];
    logic [3:0]                         prog_aw_qos [CHANNEL_COUNT];
    logic [3:0]                         prog_aw_region [CHANNEL_COUNT];

    logic [CHANNEL_COUNT-1:0]           prog_w_valid;
    logic [CHANNEL_COUNT-1:0]           prog_w_ready;
    logic [31:0]                        prog_w_data [CHANNEL_COUNT];
    logic [3:0]                         prog_w_strb [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           prog_w_last;

    logic [CHANNEL_COUNT-1:0]           prog_b_valid;
    logic [CHANNEL_COUNT-1:0]           prog_b_ready;
    logic [AXI_ID_WIDTH-1:0]            prog_b_id [CHANNEL_COUNT];
    logic [1:0]                         prog_b_resp [CHANNEL_COUNT];

    // Control Read Engine Interface (per channel, before arbitration)
    logic [CHANNEL_COUNT-1:0]           ctrlrd_valid;
    logic [CHANNEL_COUNT-1:0]           ctrlrd_ready;
    logic [ADDR_WIDTH-1:0]              ctrlrd_addr [CHANNEL_COUNT];
    logic [31:0]                        ctrlrd_data [CHANNEL_COUNT];
    logic [31:0]                        ctrlrd_mask [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           ctrlrd_error;
    logic [31:0]                        ctrlrd_result [CHANNEL_COUNT];

    // Control Write Engine Interface (per channel, before arbitration)
    logic [CHANNEL_COUNT-1:0]           ctrlwr_valid;
    logic [CHANNEL_COUNT-1:0]           ctrlwr_ready;
    logic [ADDR_WIDTH-1:0]              ctrlwr_addr [CHANNEL_COUNT];
    logic [31:0]                        ctrlwr_data [CHANNEL_COUNT];
    logic [CHANNEL_COUNT-1:0]           ctrlwr_error;

    // Scheduler Group Monitor Bus Outputs (before aggregation)
    logic [CHANNEL_COUNT-1:0]           sched_mon_valid;
    logic [CHANNEL_COUNT-1:0]           sched_mon_ready;
    logic [63:0]                        sched_mon_packet [CHANNEL_COUNT];

    //=========================================================================
    // Internal Signals - AXI Masters with MonBus
    //=========================================================================

    // Descriptor AXI master internal signals (before MonBus wrapper)
    logic                               desc_axi_int_arvalid;
    logic                               desc_axi_int_arready;
    logic [AXI_ID_WIDTH-1:0]            desc_axi_int_arid;
    logic [ADDR_WIDTH-1:0]              desc_axi_int_araddr;
    logic [7:0]                         desc_axi_int_arlen;
    logic [2:0]                         desc_axi_int_arsize;
    logic [1:0]                         desc_axi_int_arburst;
    logic                               desc_axi_int_arlock;
    logic [3:0]                         desc_axi_int_arcache;
    logic [2:0]                         desc_axi_int_arprot;
    logic [3:0]                         desc_axi_int_arqos;
    logic [3:0]                         desc_axi_int_arregion;

    logic                               desc_axi_int_rvalid;
    logic                               desc_axi_int_rready;
    logic [AXI_ID_WIDTH-1:0]            desc_axi_int_rid;
    logic [DATA_WIDTH-1:0]              desc_axi_int_rdata;
    logic [1:0]                         desc_axi_int_rresp;
    logic                               desc_axi_int_rlast;

    // NOTE: Program AXI master internal signals REMOVED
    // The program engine is tied off in scheduler_group.sv, so no external AXI master needed

    // Control Read AXI master internal signals (before MonBus wrapper)
    logic                               ctrlrd_axi_int_arvalid;
    logic                               ctrlrd_axi_int_arready;
    logic [AXI_ID_WIDTH-1:0]            ctrlrd_axi_int_arid;
    logic [ADDR_WIDTH-1:0]              ctrlrd_axi_int_araddr;
    logic [7:0]                         ctrlrd_axi_int_arlen;
    logic [2:0]                         ctrlrd_axi_int_arsize;
    logic [1:0]                         ctrlrd_axi_int_arburst;
    logic                               ctrlrd_axi_int_arlock;
    logic [3:0]                         ctrlrd_axi_int_arcache;
    logic [2:0]                         ctrlrd_axi_int_arprot;
    logic [3:0]                         ctrlrd_axi_int_arqos;
    logic [3:0]                         ctrlrd_axi_int_arregion;

    logic                               ctrlrd_axi_int_rvalid;
    logic                               ctrlrd_axi_int_rready;
    logic [AXI_ID_WIDTH-1:0]            ctrlrd_axi_int_rid;
    logic [31:0]                        ctrlrd_axi_int_rdata;
    logic [1:0]                         ctrlrd_axi_int_rresp;
    logic                               ctrlrd_axi_int_rlast;

    // Control Write AXI master internal signals (before MonBus wrapper)
    logic                               ctrlwr_axi_int_awvalid;
    logic                               ctrlwr_axi_int_awready;
    logic [AXI_ID_WIDTH-1:0]            ctrlwr_axi_int_awid;
    logic [ADDR_WIDTH-1:0]              ctrlwr_axi_int_awaddr;
    logic [7:0]                         ctrlwr_axi_int_awlen;
    logic [2:0]                         ctrlwr_axi_int_awsize;
    logic [1:0]                         ctrlwr_axi_int_awburst;
    logic                               ctrlwr_axi_int_awlock;
    logic [3:0]                         ctrlwr_axi_int_awcache;
    logic [2:0]                         ctrlwr_axi_int_awprot;
    logic [3:0]                         ctrlwr_axi_int_awqos;
    logic [3:0]                         ctrlwr_axi_int_awregion;

    logic                               ctrlwr_axi_int_wvalid;
    logic                               ctrlwr_axi_int_wready;
    logic [31:0]                        ctrlwr_axi_int_wdata;
    logic [3:0]                         ctrlwr_axi_int_wstrb;
    logic                               ctrlwr_axi_int_wlast;

    logic                               ctrlwr_axi_int_bvalid;
    logic                               ctrlwr_axi_int_bready;
    logic [AXI_ID_WIDTH-1:0]            ctrlwr_axi_int_bid;
    logic [1:0]                         ctrlwr_axi_int_bresp;

    // AXI Monitor Bus Outputs
    logic                               desc_axi_mon_valid;
    logic                               desc_axi_mon_ready;
    logic [63:0]                        desc_axi_mon_packet;

    // NOTE: Program AXI monitor signals REMOVED - prog engine tied off in scheduler_group.sv

    logic                               ctrlrd_axi_mon_valid;
    logic                               ctrlrd_axi_mon_ready;
    logic [63:0]                        ctrlrd_axi_mon_packet;

    logic                               ctrlwr_axi_mon_valid;
    logic                               ctrlwr_axi_mon_ready;
    logic [63:0]                        ctrlwr_axi_mon_packet;

    // AXI Monitor Status
    logic                               desc_axi_busy;
    logic [7:0]                         desc_axi_active_transactions;
    logic [15:0]                        desc_axi_error_count;
    logic [31:0]                        desc_axi_transaction_count;

    // NOTE: Program AXI monitor status REMOVED - prog engine tied off in scheduler_group.sv

    logic                               ctrlrd_axi_busy;
    logic [7:0]                         ctrlrd_axi_active_transactions;
    logic [15:0]                        ctrlrd_axi_error_count;
    logic [31:0]                        ctrlrd_axi_transaction_count;

    logic                               ctrlwr_axi_busy;
    logic [7:0]                         ctrlwr_axi_active_transactions;
    logic [15:0]                        ctrlwr_axi_error_count;
    logic [31:0]                        ctrlwr_axi_transaction_count;

    //=========================================================================
    // Internal Signals - MonBus Aggregation
    //=========================================================================

    // Aggregated MonBus inputs (CHANNEL_COUNT scheduler_groups + 2 AXI masters)
    logic                               monbus_valid_in [MONBUS_CLIENTS];  // Unpacked array to match monbus_arbiter
    logic                               monbus_ready_in [MONBUS_CLIENTS];  // Unpacked array to match monbus_arbiter
    logic [63:0]                        monbus_packet_in [MONBUS_CLIENTS];

    //=========================================================================
    // Scheduler Group Array Instantiation
    //=========================================================================

    genvar ch;
    generate
        for (ch = 0; ch < CHANNEL_COUNT; ch++) begin : gen_scheduler_groups

            scheduler_group #(
                .CHANNEL_ID                 (ch),
                .NUM_CHANNELS               (CHANNEL_COUNT),
                .ADDR_WIDTH                 (ADDR_WIDTH),
                .DATA_WIDTH                 (DATA_WIDTH),
                .AXI_ID_WIDTH               (AXI_ID_WIDTH),
                .CREDIT_WIDTH               (CREDIT_WIDTH),
                .TIMEOUT_CYCLES             (TIMEOUT_CYCLES),
                .EARLY_WARNING_THRESHOLD    (EARLY_WARNING_THRESHOLD),
                .DESC_MON_AGENT_ID          (DESC_MON_AGENT_BASE + ch),
                .PROG_MON_AGENT_ID          (PROG_MON_AGENT_BASE + ch),
                .SCHED_MON_AGENT_ID         (SCHED_MON_AGENT_BASE + ch),
                .MON_UNIT_ID                (MON_UNIT_ID),
                .MON_CHANNEL_ID             (ch)
            ) u_scheduler_group (
                // Clock and Reset
                .clk                        (clk),
                .rst_n                      (rst_n),

                // APB Programming Interface
                .apb_valid                  (apb_valid[ch]),
                .apb_ready                  (apb_ready[ch]),
                .apb_addr                   (apb_addr[ch]),

                // CDA Packet Interface (formerly RDA)
                .cda_valid                  (cda_valid[ch]),
                .cda_ready                  (cda_ready[ch]),
                .cda_packet                 (cda_packet[ch]),
                .cda_channel                (cda_channel[ch]),

                // EOS Completion Interface
                .eos_completion_valid       (eos_completion_valid[ch]),
                .eos_completion_ready       (eos_completion_ready[ch]),
                .eos_completion_channel     (eos_completion_channel[ch]),

                // Configuration Interface
                .cfg_idle_mode              (cfg_idle_mode[ch]),
                .cfg_channel_wait           (cfg_channel_wait[ch]),
                .cfg_channel_enable         (cfg_channel_enable[ch]),
                .cfg_use_credit             (cfg_use_credit[ch]),
                .cfg_initial_credit         (cfg_initial_credit[ch]),
                .credit_increment           (credit_increment[ch]),
                .cfg_prefetch_enable        (cfg_prefetch_enable[ch]),
                .cfg_fifo_threshold         (cfg_fifo_threshold[ch]),
                .cfg_addr0_base             (cfg_addr0_base[ch]),
                .cfg_addr0_limit            (cfg_addr0_limit[ch]),
                .cfg_addr1_base             (cfg_addr1_base[ch]),
                .cfg_addr1_limit            (cfg_addr1_limit[ch]),
                .cfg_channel_reset          (cfg_channel_reset[ch]),
                .cfg_ctrlrd_max_try         (cfg_ctrlrd_max_try[ch]),

                // Status Interface
                .descriptor_engine_idle     (descriptor_engine_idle[ch]),
                .program_engine_idle        (program_engine_idle[ch]),
                .scheduler_idle             (scheduler_idle[ch]),
                .descriptor_credit_counter  (descriptor_credit_counter[ch]),
                .fsm_state                  (fsm_state[ch]),
                .scheduler_error            (scheduler_error[ch]),
                .backpressure_warning       (backpressure_warning[ch]),

                // Descriptor Engine AXI4 Master Read Interface
                .desc_ar_valid              (desc_ar_valid[ch]),
                .desc_ar_ready              (desc_ar_ready[ch]),
                .desc_ar_addr               (desc_ar_addr[ch]),
                .desc_ar_len                (desc_ar_len[ch]),
                .desc_ar_size               (desc_ar_size[ch]),
                .desc_ar_burst              (desc_ar_burst[ch]),
                .desc_ar_id                 (desc_ar_id[ch]),
                .desc_ar_lock               (desc_ar_lock[ch]),
                .desc_ar_cache              (desc_ar_cache[ch]),
                .desc_ar_prot               (desc_ar_prot[ch]),
                .desc_ar_qos                (desc_ar_qos[ch]),
                .desc_ar_region             (desc_ar_region[ch]),

                .desc_r_valid               (desc_r_valid[ch]),
                .desc_r_ready               (desc_r_ready[ch]),
                .desc_r_data                (desc_r_data[ch]),
                .desc_r_resp                (desc_r_resp[ch]),
                .desc_r_last                (desc_r_last[ch]),
                .desc_r_id                  (desc_r_id[ch]),

                // Program Engine AXI4 Master Write Interface
                .prog_aw_valid              (prog_aw_valid[ch]),
                .prog_aw_ready              (prog_aw_ready[ch]),
                .prog_aw_addr               (prog_aw_addr[ch]),
                .prog_aw_len                (prog_aw_len[ch]),
                .prog_aw_size               (prog_aw_size[ch]),
                .prog_aw_burst              (prog_aw_burst[ch]),
                .prog_aw_id                 (prog_aw_id[ch]),
                .prog_aw_lock               (prog_aw_lock[ch]),
                .prog_aw_cache              (prog_aw_cache[ch]),
                .prog_aw_prot               (prog_aw_prot[ch]),
                .prog_aw_qos                (prog_aw_qos[ch]),
                .prog_aw_region             (prog_aw_region[ch]),

                .prog_w_valid               (prog_w_valid[ch]),
                .prog_w_ready               (prog_w_ready[ch]),
                .prog_w_data                (prog_w_data[ch]),
                .prog_w_strb                (prog_w_strb[ch]),
                .prog_w_last                (prog_w_last[ch]),

                .prog_b_valid               (prog_b_valid[ch]),
                .prog_b_ready               (prog_b_ready[ch]),
                .prog_b_id                  (prog_b_id[ch]),
                .prog_b_resp                (prog_b_resp[ch]),

                // Control Read Engine Interface
                .ctrlrd_valid               (ctrlrd_valid[ch]),
                .ctrlrd_ready               (ctrlrd_ready[ch]),
                .ctrlrd_addr                (ctrlrd_addr[ch]),
                .ctrlrd_data                (ctrlrd_data[ch]),
                .ctrlrd_mask                (ctrlrd_mask[ch]),
                .ctrlrd_error               (ctrlrd_error[ch]),
                .ctrlrd_result              (ctrlrd_result[ch]),

                // Control Write Engine Interface
                .ctrlwr_valid               (ctrlwr_valid[ch]),
                .ctrlwr_ready               (ctrlwr_ready[ch]),
                .ctrlwr_addr                (ctrlwr_addr[ch]),
                .ctrlwr_data                (ctrlwr_data[ch]),
                .ctrlwr_error               (ctrlwr_error[ch]),

                // Data Mover Interface
                .data_valid                 (data_valid[ch]),
                .data_ready                 (data_ready[ch]),
                .data_address               (data_address[ch]),
                .data_length                (data_length[ch]),
                .data_type                  (data_type[ch]),
                .data_eos                   (data_eos[ch]),

                .data_transfer_length       (data_transfer_length[ch]),
                .data_error                 (data_error[ch]),
                .data_done_strobe           (data_done_strobe[ch]),

                // Address Alignment Bus Interface
                .data_alignment_info        (data_alignment_info[ch]),
                .data_alignment_valid       (data_alignment_valid[ch]),
                .data_alignment_ready       (data_alignment_ready[ch]),
                .data_alignment_next        (data_alignment_next[ch]),
                .data_transfer_phase        (data_transfer_phase[ch]),
                .data_sequence_complete     (data_sequence_complete[ch]),

                // RDA Credit Return Interface
                .rda_complete_valid         (rda_complete_valid[ch]),
                .rda_complete_ready         (rda_complete_ready[ch]),
                .rda_complete_channel       (rda_complete_channel[ch]),

                // Monitor Bus Interface
                .mon_valid                  (sched_mon_valid[ch]),
                .mon_ready                  (sched_mon_ready[ch]),
                .mon_packet                 (sched_mon_packet[ch])
            );

        end
    endgenerate

    //=========================================================================
    // AXI Arbitration - Descriptor Engine (Read Master with MonBus)
    //=========================================================================

    // AR Channel Arbitration Signals
    logic [CHANNEL_COUNT-1:0]   desc_ar_grant;
    logic [CHAN_WIDTH-1:0]      desc_ar_grant_id;
    logic                       desc_ar_grant_valid;
    logic [CHANNEL_COUNT-1:0]   desc_ar_grant_ack;

    // AR Channel Round-Robin Arbiter
    arbiter_round_robin #(
        .CLIENTS        (CHANNEL_COUNT),
        .WAIT_GNT_ACK   (1)  // ACK mode for proper handshaking
    ) u_desc_ar_arbiter (
        .clk            (clk),
        .rst_n          (rst_n),
        .block_arb      (1'b0),
        .request        (desc_ar_valid),
        .grant_ack      (desc_ar_grant_ack),
        .grant_valid    (desc_ar_grant_valid),
        .grant          (desc_ar_grant),
        .grant_id       (desc_ar_grant_id),
        .last_grant     ()
    );

    // AR Channel Grant ACK: Asserted when granted client's request is accepted
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            desc_ar_grant_ack[i] = desc_ar_grant[i] && desc_ar_valid[i] && desc_axi_int_arready;
        end
    end

    // AR Channel Ready: Only granted client receives ready
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            desc_ar_ready[i] = desc_ar_grant[i] && desc_axi_int_arready;
        end
    end

    // AR Channel Multiplexing: Select granted client's signals
    always_comb begin
        if (desc_ar_grant_valid) begin
            desc_axi_int_arvalid  = desc_ar_valid[desc_ar_grant_id];
            // Embed channel ID in lower bits of AXI ID for response routing (matches ctrlrd/ctrlwr)
            // Lower CHAN_WIDTH bits = channel number, upper bits = 0
            desc_axi_int_arid     = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, desc_ar_grant_id};
            desc_axi_int_araddr   = desc_ar_addr[desc_ar_grant_id];
            desc_axi_int_arlen    = desc_ar_len[desc_ar_grant_id];
            desc_axi_int_arsize   = desc_ar_size[desc_ar_grant_id];
            desc_axi_int_arburst  = desc_ar_burst[desc_ar_grant_id];
            desc_axi_int_arlock   = desc_ar_lock[desc_ar_grant_id];
            desc_axi_int_arcache  = desc_ar_cache[desc_ar_grant_id];
            desc_axi_int_arprot   = desc_ar_prot[desc_ar_grant_id];
            desc_axi_int_arqos    = desc_ar_qos[desc_ar_grant_id];
            desc_axi_int_arregion = desc_ar_region[desc_ar_grant_id];
        end else begin
            desc_axi_int_arvalid  = 1'b0;
            desc_axi_int_arid     = '0;
            desc_axi_int_araddr   = '0;
            desc_axi_int_arlen    = '0;
            desc_axi_int_arsize   = '0;
            desc_axi_int_arburst  = '0;
            desc_axi_int_arlock   = 1'b0;
            desc_axi_int_arcache  = '0;
            desc_axi_int_arprot   = '0;
            desc_axi_int_arqos    = '0;
            desc_axi_int_arregion = '0;
        end
    end

    // R Channel ID-Based Demultiplexing
    // Extract channel ID from lower bits of AXI ID (matches ctrlrd/ctrlwr)
    // Lower CHAN_WIDTH bits contain channel number
    logic [CHAN_WIDTH-1:0] desc_r_channel_id;
    assign desc_r_channel_id = desc_axi_int_rid[CHAN_WIDTH-1:0];

    always_comb begin
        // Default: no channel receives R data
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            desc_r_valid[i] = 1'b0;
            desc_r_data[i]  = '0;
            desc_r_resp[i]  = '0;
            desc_r_last[i]  = 1'b0;
            desc_r_id[i]    = '0;
        end

        // Route R channel to correct channel based on ID
        if (desc_axi_int_rvalid && desc_r_channel_id < CHANNEL_COUNT) begin
            desc_r_valid[desc_r_channel_id] = 1'b1;
            desc_r_data[desc_r_channel_id]  = desc_axi_int_rdata;
            desc_r_resp[desc_r_channel_id]  = desc_axi_int_rresp;
            desc_r_last[desc_r_channel_id]  = desc_axi_int_rlast;
            desc_r_id[desc_r_channel_id]    = desc_axi_int_rid;
        end
    end

    // R Channel Ready: OR of all channel ready signals (gated by ID match)
    always_comb begin
        desc_axi_int_rready = 1'b0;
        if (desc_axi_int_rvalid && desc_r_channel_id < CHANNEL_COUNT) begin
            desc_axi_int_rready = desc_r_ready[desc_r_channel_id];
        end
    end

    //=========================================================================
    // NOTE: Program Engine AXI Arbitration REMOVED
    // The program engine is tied off in scheduler_group.sv, so no arbitration needed.
    // The prog_* per-channel signals still exist (connected to scheduler_group instances)
    // but are not arbitrated to an external AXI master.
    //=========================================================================

    //=========================================================================
    // AXI Arbitration - Control Read Engine (Read Master with MonBus)
    //=========================================================================

    // Note: ctrlrd interface has custom valid/ready/addr/data/mask/error/result signals
    // We need to arbitrate the valid/ready/addr/data/mask signals and demux error/result

    // Arbitration Signals
    logic [CHANNEL_COUNT-1:0]   ctrlrd_grant;
    logic [CHAN_WIDTH-1:0]      ctrlrd_grant_id;
    logic                       ctrlrd_grant_valid;
    logic [CHANNEL_COUNT-1:0]   ctrlrd_grant_ack;

    // Round-Robin Arbiter for ctrlrd requests
    arbiter_round_robin #(
        .CLIENTS        (CHANNEL_COUNT),
        .WAIT_GNT_ACK   (1)  // ACK mode for proper handshaking
    ) u_ctrlrd_arbiter (
        .clk            (clk),
        .rst_n          (rst_n),
        .block_arb      (1'b0),
        .request        (ctrlrd_valid),
        .grant_ack      (ctrlrd_grant_ack),
        .grant_valid    (ctrlrd_grant_valid),
        .grant          (ctrlrd_grant),
        .grant_id       (ctrlrd_grant_id),
        .last_grant     ()
    );

    // Grant ACK: Asserted when granted client's request is accepted
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlrd_grant_ack[i] = ctrlrd_grant[i] && ctrlrd_valid[i] && ctrlrd_axi_int_arready;
        end
    end

    // Ready: Only granted client receives ready
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlrd_ready[i] = ctrlrd_grant[i] && ctrlrd_axi_int_arready;
        end
    end

    // Request Multiplexing: Select granted client's signals
    // Note: We need to convert custom ctrlrd interface to AXI AR channel
    always_comb begin
        if (ctrlrd_grant_valid) begin
            ctrlrd_axi_int_arvalid  = ctrlrd_valid[ctrlrd_grant_id];
            ctrlrd_axi_int_arid     = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, ctrlrd_grant_id};  // Embed channel ID in upper bits
            ctrlrd_axi_int_araddr   = ctrlrd_addr[ctrlrd_grant_id];
            ctrlrd_axi_int_arlen    = 8'h0;   // Single transfer
            ctrlrd_axi_int_arsize   = 3'b010; // 4 bytes (32-bit data)
            ctrlrd_axi_int_arburst  = 2'b01;  // INCR
            ctrlrd_axi_int_arlock   = 1'b0;
            ctrlrd_axi_int_arcache  = 4'b0000;
            ctrlrd_axi_int_arprot   = 3'b000;
            ctrlrd_axi_int_arqos    = 4'b0000;
            ctrlrd_axi_int_arregion = 4'b0000;
        end else begin
            ctrlrd_axi_int_arvalid  = 1'b0;
            ctrlrd_axi_int_arid     = '0;
            ctrlrd_axi_int_araddr   = '0;
            ctrlrd_axi_int_arlen    = '0;
            ctrlrd_axi_int_arsize   = '0;
            ctrlrd_axi_int_arburst  = '0;
            ctrlrd_axi_int_arlock   = 1'b0;
            ctrlrd_axi_int_arcache  = '0;
            ctrlrd_axi_int_arprot   = '0;
            ctrlrd_axi_int_arqos    = '0;
            ctrlrd_axi_int_arregion = '0;
        end
    end

    // R Channel ID-Based Demultiplexing
    // Convert AXI R channel back to custom ctrlrd interface
    logic [CHAN_WIDTH-1:0] ctrlrd_r_channel_id;
    assign ctrlrd_r_channel_id = ctrlrd_axi_int_rid[CHAN_WIDTH-1:0];

    always_comb begin
        // Default: no channel receives response
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlrd_error[i]  = 1'b0;
            ctrlrd_result[i] = '0;
        end

        // Route R channel to correct channel based on ID
        // Error is set if rresp != OKAY
        if (ctrlrd_axi_int_rvalid && ctrlrd_r_channel_id < CHANNEL_COUNT) begin
            ctrlrd_error[ctrlrd_r_channel_id]  = (ctrlrd_axi_int_rresp != 2'b00);
            ctrlrd_result[ctrlrd_r_channel_id] = ctrlrd_axi_int_rdata;
        end
    end

    // R Channel Ready: Always ready (synchronous response expected)
    assign ctrlrd_axi_int_rready = 1'b1;

    //=========================================================================
    // AXI Arbitration - Control Write Engine (Write Master with MonBus)
    //=========================================================================

    // Note: ctrlwr interface has custom valid/ready/addr/data/error signals
    // We need to arbitrate AW and W channels, and demux B channel (error)

    // AW Channel Arbitration Signals
    logic [CHANNEL_COUNT-1:0]   ctrlwr_aw_grant;
    logic [CHAN_WIDTH-1:0]      ctrlwr_aw_grant_id;
    logic                       ctrlwr_aw_grant_valid;
    logic [CHANNEL_COUNT-1:0]   ctrlwr_aw_grant_ack;

    // AW Channel Round-Robin Arbiter
    arbiter_round_robin #(
        .CLIENTS        (CHANNEL_COUNT),
        .WAIT_GNT_ACK   (1)
    ) u_ctrlwr_aw_arbiter (
        .clk            (clk),
        .rst_n          (rst_n),
        .block_arb      (1'b0),
        .request        (ctrlwr_valid),
        .grant_ack      (ctrlwr_aw_grant_ack),
        .grant_valid    (ctrlwr_aw_grant_valid),
        .grant          (ctrlwr_aw_grant),
        .grant_id       (ctrlwr_aw_grant_id),
        .last_grant     ()
    );

    // AW Channel Grant ACK
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlwr_aw_grant_ack[i] = ctrlwr_aw_grant[i] && ctrlwr_valid[i] && ctrlwr_axi_int_awready;
        end
    end

    // Ready: Only granted client receives ready
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlwr_ready[i] = ctrlwr_aw_grant[i] && ctrlwr_axi_int_awready && ctrlwr_axi_int_wready;
        end
    end

    // AW Channel Multiplexing: Convert ctrlwr to AXI AW channel
    always_comb begin
        if (ctrlwr_aw_grant_valid) begin
            ctrlwr_axi_int_awvalid  = ctrlwr_valid[ctrlwr_aw_grant_id];
            ctrlwr_axi_int_awid     = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, ctrlwr_aw_grant_id};
            ctrlwr_axi_int_awaddr   = ctrlwr_addr[ctrlwr_aw_grant_id];
            ctrlwr_axi_int_awlen    = 8'h0;   // Single transfer
            ctrlwr_axi_int_awsize   = 3'b010; // 4 bytes (32-bit data)
            ctrlwr_axi_int_awburst  = 2'b01;  // INCR
            ctrlwr_axi_int_awlock   = 1'b0;
            ctrlwr_axi_int_awcache  = 4'b0000;
            ctrlwr_axi_int_awprot   = 3'b000;
            ctrlwr_axi_int_awqos    = 4'b0000;
            ctrlwr_axi_int_awregion = 4'b0000;
        end else begin
            ctrlwr_axi_int_awvalid  = 1'b0;
            ctrlwr_axi_int_awid     = '0;
            ctrlwr_axi_int_awaddr   = '0;
            ctrlwr_axi_int_awlen    = '0;
            ctrlwr_axi_int_awsize   = '0;
            ctrlwr_axi_int_awburst  = '0;
            ctrlwr_axi_int_awlock   = 1'b0;
            ctrlwr_axi_int_awcache  = '0;
            ctrlwr_axi_int_awprot   = '0;
            ctrlwr_axi_int_awqos    = '0;
            ctrlwr_axi_int_awregion = '0;
        end
    end

    // W Channel Multiplexing: Convert ctrlwr data to AXI W channel
    always_comb begin
        if (ctrlwr_aw_grant_valid) begin
            ctrlwr_axi_int_wvalid = ctrlwr_valid[ctrlwr_aw_grant_id];
            ctrlwr_axi_int_wdata  = ctrlwr_data[ctrlwr_aw_grant_id];
            ctrlwr_axi_int_wstrb  = 4'b1111; // All bytes valid
            ctrlwr_axi_int_wlast  = 1'b1;    // Single transfer
        end else begin
            ctrlwr_axi_int_wvalid = 1'b0;
            ctrlwr_axi_int_wdata  = '0;
            ctrlwr_axi_int_wstrb  = '0;
            ctrlwr_axi_int_wlast  = 1'b0;
        end
    end

    // B Channel ID-Based Demultiplexing
    logic [CHAN_WIDTH-1:0] ctrlwr_b_channel_id;
    assign ctrlwr_b_channel_id = ctrlwr_axi_int_bid[CHAN_WIDTH-1:0];

    always_comb begin
        // Default: no channel receives error
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            ctrlwr_error[i] = 1'b0;
        end

        // Route B channel error to correct channel based on ID
        if (ctrlwr_axi_int_bvalid && ctrlwr_b_channel_id < CHANNEL_COUNT) begin
            ctrlwr_error[ctrlwr_b_channel_id] = (ctrlwr_axi_int_bresp != 2'b00);
        end
    end

    // B Channel Ready: Always ready (synchronous response expected)
    assign ctrlwr_axi_int_bready = 1'b1;

    //=========================================================================
    // AXI4 Master Read with MonBus (Descriptor Engine)
    //=========================================================================

    axi4_master_rd_mon_cg #(
        .SKID_DEPTH_AR          (AXI_SKID_DEPTH_AR),
        .SKID_DEPTH_R           (AXI_SKID_DEPTH_R),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_DATA_WIDTH         (DATA_WIDTH),
        .AXI_USER_WIDTH         (1),
        .UNIT_ID                (MON_UNIT_ID),
        .AGENT_ID               (AXI_RD_MON_AGENT_ID),
        .MAX_TRANSACTIONS       (AXI_MAX_TRANSACTIONS),
        .ENABLE_FILTERING       (AXI_ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE     (AXI_ADD_PIPELINE_STAGE),
        .ENABLE_CLOCK_GATING    (AXI_ENABLE_CLOCK_GATING),
        .CG_IDLE_CYCLES         (AXI_CG_IDLE_CYCLES)
    ) u_desc_axi_master_rd_mon (
        // Clock and Reset
        .aclk                   (clk),
        .aresetn                (rst_n),

        // FUB AXI Interface (from arbiter)
        .fub_axi_arid           (desc_axi_int_arid),
        .fub_axi_araddr         (desc_axi_int_araddr),
        .fub_axi_arlen          (desc_axi_int_arlen),
        .fub_axi_arsize         (desc_axi_int_arsize),
        .fub_axi_arburst        (desc_axi_int_arburst),
        .fub_axi_arlock         (desc_axi_int_arlock),
        .fub_axi_arcache        (desc_axi_int_arcache),
        .fub_axi_arprot         (desc_axi_int_arprot),
        .fub_axi_arqos          (desc_axi_int_arqos),
        .fub_axi_arregion       (desc_axi_int_arregion),
        .fub_axi_aruser         (1'b0),
        .fub_axi_arvalid        (desc_axi_int_arvalid),
        .fub_axi_arready        (desc_axi_int_arready),

        .fub_axi_rid            (desc_axi_int_rid),
        .fub_axi_rdata          (desc_axi_int_rdata),
        .fub_axi_rresp          (desc_axi_int_rresp),
        .fub_axi_rlast          (desc_axi_int_rlast),
        .fub_axi_ruser          (),
        .fub_axi_rvalid         (desc_axi_int_rvalid),
        .fub_axi_rready         (desc_axi_int_rready),

        // Master AXI Interface (to system)
        .m_axi_arid             (m_axi_desc_arid),
        .m_axi_araddr           (m_axi_desc_araddr),
        .m_axi_arlen            (m_axi_desc_arlen),
        .m_axi_arsize           (m_axi_desc_arsize),
        .m_axi_arburst          (m_axi_desc_arburst),
        .m_axi_arlock           (m_axi_desc_arlock),
        .m_axi_arcache          (m_axi_desc_arcache),
        .m_axi_arprot           (m_axi_desc_arprot),
        .m_axi_arqos            (m_axi_desc_arqos),
        .m_axi_arregion         (m_axi_desc_arregion),
        .m_axi_aruser           (),
        .m_axi_arvalid          (m_axi_desc_arvalid),
        .m_axi_arready          (m_axi_desc_arready),

        .m_axi_rid              (m_axi_desc_rid),
        .m_axi_rdata            (m_axi_desc_rdata),
        .m_axi_rresp            (m_axi_desc_rresp),
        .m_axi_rlast            (m_axi_desc_rlast),
        .m_axi_ruser            (1'b0),
        .m_axi_rvalid           (m_axi_desc_rvalid),
        .m_axi_rready           (m_axi_desc_rready),

        // Monitor Configuration
        .cfg_monitor_enable     (cfg_axi_monitor_enable),
        .cfg_error_enable       (cfg_axi_error_enable),
        .cfg_timeout_enable     (cfg_axi_timeout_enable),
        .cfg_perf_enable        (cfg_axi_perf_enable),
        .cfg_timeout_cycles     (cfg_axi_timeout_cycles),
        .cfg_latency_threshold  (cfg_axi_latency_threshold),

        // AXI Protocol Filtering Configuration
        .cfg_axi_pkt_mask       (cfg_axi_pkt_mask),
        .cfg_axi_err_select     (cfg_axi_err_select),
        .cfg_axi_error_mask     (cfg_axi_error_mask),
        .cfg_axi_timeout_mask   (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask     (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask    (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),

        // Clock Gating Configuration
        .cfg_cg_enable          (cfg_cg_enable),
        .cfg_cg_idle_threshold  (cfg_cg_idle_threshold),
        .cfg_cg_force_on        (cfg_cg_force_on),
        .cfg_cg_gate_monitor    (cfg_cg_gate_monitor),
        .cfg_cg_gate_reporter   (cfg_cg_gate_reporter),
        .cfg_cg_gate_timers     (cfg_cg_gate_timers),

        // Monitor Bus Output
        .monbus_valid           (desc_axi_mon_valid),
        .monbus_ready           (desc_axi_mon_ready),
        .monbus_packet          (desc_axi_mon_packet),

        // Status outputs
        .busy                   (desc_axi_busy),
        .active_transactions    (desc_axi_active_transactions),
        .error_count            (desc_axi_error_count),
        .transaction_count      (desc_axi_transaction_count),

        // Clock gating status
        .cg_monitor_gated       (),
        .cg_reporter_gated      (),
        .cg_timers_gated        (),
        .cg_cycles_saved        (),

        // Configuration error flags
        .cfg_conflict_error     ()
    );

    //=========================================================================
    // NOTE: Program Engine AXI Master REMOVED
    // The program engine has been removed from scheduler_group.sv and replaced
    // with ctrlwr_engine. The external AXI interface is now m_axi_ctrlwr_*.
    //=========================================================================

    //=========================================================================
    // AXI4 Master Read with MonBus (Control Read Engine)
    //=========================================================================

    axi4_master_rd_mon_cg #(
        .SKID_DEPTH_AR          (AXI_SKID_DEPTH_AR),
        .SKID_DEPTH_R           (AXI_SKID_DEPTH_R),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_DATA_WIDTH         (32),  // Control read uses 32-bit data
        .AXI_USER_WIDTH         (1),
        .UNIT_ID                (MON_UNIT_ID),
        .AGENT_ID               (CTRLRD_MON_AGENT_ID),
        .MAX_TRANSACTIONS       (AXI_MAX_TRANSACTIONS),
        .ENABLE_FILTERING       (AXI_ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE     (AXI_ADD_PIPELINE_STAGE),
        .ENABLE_CLOCK_GATING    (AXI_ENABLE_CLOCK_GATING),
        .CG_IDLE_CYCLES         (AXI_CG_IDLE_CYCLES)
    ) u_ctrlrd_axi_master_rd_mon (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .fub_axi_arid           (ctrlrd_axi_int_arid),
        .fub_axi_araddr         (ctrlrd_axi_int_araddr),
        .fub_axi_arlen          (ctrlrd_axi_int_arlen),
        .fub_axi_arsize         (ctrlrd_axi_int_arsize),
        .fub_axi_arburst        (ctrlrd_axi_int_arburst),
        .fub_axi_arlock         (ctrlrd_axi_int_arlock),
        .fub_axi_arcache        (ctrlrd_axi_int_arcache),
        .fub_axi_arprot         (ctrlrd_axi_int_arprot),
        .fub_axi_arqos          (ctrlrd_axi_int_arqos),
        .fub_axi_arregion       (ctrlrd_axi_int_arregion),
        .fub_axi_aruser         (1'b0),
        .fub_axi_arvalid        (ctrlrd_axi_int_arvalid),
        .fub_axi_arready        (ctrlrd_axi_int_arready),
        .fub_axi_rid            (ctrlrd_axi_int_rid),
        .fub_axi_rdata          (ctrlrd_axi_int_rdata),
        .fub_axi_rresp          (ctrlrd_axi_int_rresp),
        .fub_axi_rlast          (ctrlrd_axi_int_rlast),
        .fub_axi_ruser          (),
        .fub_axi_rvalid         (ctrlrd_axi_int_rvalid),
        .fub_axi_rready         (ctrlrd_axi_int_rready),
        // Master AXI Interface (to external system)
        .m_axi_arid             (m_axi_ctrlrd_arid),
        .m_axi_araddr           (m_axi_ctrlrd_araddr),
        .m_axi_arlen            (m_axi_ctrlrd_arlen),
        .m_axi_arsize           (m_axi_ctrlrd_arsize),
        .m_axi_arburst          (m_axi_ctrlrd_arburst),
        .m_axi_arlock           (m_axi_ctrlrd_arlock),
        .m_axi_arcache          (m_axi_ctrlrd_arcache),
        .m_axi_arprot           (m_axi_ctrlrd_arprot),
        .m_axi_arqos            (m_axi_ctrlrd_arqos),
        .m_axi_arregion         (m_axi_ctrlrd_arregion),
        .m_axi_aruser           (),
        .m_axi_arvalid          (m_axi_ctrlrd_arvalid),
        .m_axi_arready          (m_axi_ctrlrd_arready),
        .m_axi_rid              (m_axi_ctrlrd_rid),
        .m_axi_rdata            (m_axi_ctrlrd_rdata),
        .m_axi_rresp            (m_axi_ctrlrd_rresp),
        .m_axi_rlast            (m_axi_ctrlrd_rlast),
        .m_axi_ruser            (1'b0),
        .m_axi_rvalid           (m_axi_ctrlrd_rvalid),
        .m_axi_rready           (m_axi_ctrlrd_rready),
        .cfg_monitor_enable     (cfg_axi_monitor_enable),
        .cfg_error_enable       (cfg_axi_error_enable),
        .cfg_timeout_enable     (cfg_axi_timeout_enable),
        .cfg_perf_enable        (cfg_axi_perf_enable),
        .cfg_timeout_cycles     (cfg_axi_timeout_cycles),
        .cfg_latency_threshold  (cfg_axi_latency_threshold),
        .cfg_axi_pkt_mask       (cfg_axi_pkt_mask),
        .cfg_axi_err_select     (cfg_axi_err_select),
        .cfg_axi_error_mask     (cfg_axi_error_mask),
        .cfg_axi_timeout_mask   (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask     (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask    (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),
        .cfg_cg_enable          (cfg_cg_enable),
        .cfg_cg_idle_threshold  (cfg_cg_idle_threshold),
        .cfg_cg_force_on        (cfg_cg_force_on),
        .cfg_cg_gate_monitor    (cfg_cg_gate_monitor),
        .cfg_cg_gate_reporter   (cfg_cg_gate_reporter),
        .cfg_cg_gate_timers     (cfg_cg_gate_timers),
        .monbus_valid           (ctrlrd_axi_mon_valid),
        .monbus_ready           (ctrlrd_axi_mon_ready),
        .monbus_packet          (ctrlrd_axi_mon_packet),
        .busy                   (ctrlrd_axi_busy),
        .active_transactions    (ctrlrd_axi_active_transactions),
        .error_count            (ctrlrd_axi_error_count),
        .transaction_count      (ctrlrd_axi_transaction_count),
        .cg_monitor_gated       (),
        .cg_reporter_gated      (),
        .cg_timers_gated        (),
        .cg_cycles_saved        (),
        .cfg_conflict_error     ()
    );

    //=========================================================================
    // AXI4 Master Write with MonBus (Control Write Engine)
    //=========================================================================

    axi4_master_wr_mon_cg #(
        .SKID_DEPTH_AW          (AXI_SKID_DEPTH_AW),
        .SKID_DEPTH_W           (AXI_SKID_DEPTH_W),
        .SKID_DEPTH_B           (AXI_SKID_DEPTH_B),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_DATA_WIDTH         (32),  // Control write uses 32-bit data
        .AXI_USER_WIDTH         (1),
        .UNIT_ID                (MON_UNIT_ID),
        .AGENT_ID               (CTRLWR_MON_AGENT_ID),
        .MAX_TRANSACTIONS       (AXI_MAX_TRANSACTIONS),
        .ENABLE_FILTERING       (AXI_ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE     (AXI_ADD_PIPELINE_STAGE),
        .ENABLE_CLOCK_GATING    (AXI_ENABLE_CLOCK_GATING),
        .CG_IDLE_CYCLES         (AXI_CG_IDLE_CYCLES)
    ) u_ctrlwr_axi_master_wr_mon (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .fub_axi_awid           (ctrlwr_axi_int_awid),
        .fub_axi_awaddr         (ctrlwr_axi_int_awaddr),
        .fub_axi_awlen          (ctrlwr_axi_int_awlen),
        .fub_axi_awsize         (ctrlwr_axi_int_awsize),
        .fub_axi_awburst        (ctrlwr_axi_int_awburst),
        .fub_axi_awlock         (ctrlwr_axi_int_awlock),
        .fub_axi_awcache        (ctrlwr_axi_int_awcache),
        .fub_axi_awprot         (ctrlwr_axi_int_awprot),
        .fub_axi_awqos          (ctrlwr_axi_int_awqos),
        .fub_axi_awregion       (ctrlwr_axi_int_awregion),
        .fub_axi_awuser         (1'b0),
        .fub_axi_awvalid        (ctrlwr_axi_int_awvalid),
        .fub_axi_awready        (ctrlwr_axi_int_awready),
        .fub_axi_wdata          (ctrlwr_axi_int_wdata),
        .fub_axi_wstrb          (ctrlwr_axi_int_wstrb),
        .fub_axi_wlast          (ctrlwr_axi_int_wlast),
        .fub_axi_wuser          (1'b0),
        .fub_axi_wvalid         (ctrlwr_axi_int_wvalid),
        .fub_axi_wready         (ctrlwr_axi_int_wready),
        .fub_axi_bid            (ctrlwr_axi_int_bid),
        .fub_axi_bresp          (ctrlwr_axi_int_bresp),
        .fub_axi_buser          (),
        .fub_axi_bvalid         (ctrlwr_axi_int_bvalid),
        .fub_axi_bready         (ctrlwr_axi_int_bready),
        // Master AXI Interface (to external system)
        .m_axi_awid             (m_axi_ctrlwr_awid),
        .m_axi_awaddr           (m_axi_ctrlwr_awaddr),
        .m_axi_awlen            (m_axi_ctrlwr_awlen),
        .m_axi_awsize           (m_axi_ctrlwr_awsize),
        .m_axi_awburst          (m_axi_ctrlwr_awburst),
        .m_axi_awlock           (m_axi_ctrlwr_awlock),
        .m_axi_awcache          (m_axi_ctrlwr_awcache),
        .m_axi_awprot           (m_axi_ctrlwr_awprot),
        .m_axi_awqos            (m_axi_ctrlwr_awqos),
        .m_axi_awregion         (m_axi_ctrlwr_awregion),
        .m_axi_awuser           (),
        .m_axi_awvalid          (m_axi_ctrlwr_awvalid),
        .m_axi_awready          (m_axi_ctrlwr_awready),
        .m_axi_wdata            (m_axi_ctrlwr_wdata),
        .m_axi_wstrb            (m_axi_ctrlwr_wstrb),
        .m_axi_wlast            (m_axi_ctrlwr_wlast),
        .m_axi_wuser            (),
        .m_axi_wvalid           (m_axi_ctrlwr_wvalid),
        .m_axi_wready           (m_axi_ctrlwr_wready),
        .m_axi_bid              (m_axi_ctrlwr_bid),
        .m_axi_bresp            (m_axi_ctrlwr_bresp),
        .m_axi_buser            (1'b0),
        .m_axi_bvalid           (m_axi_ctrlwr_bvalid),
        .m_axi_bready           (m_axi_ctrlwr_bready),
        .cfg_monitor_enable     (cfg_axi_monitor_enable),
        .cfg_error_enable       (cfg_axi_error_enable),
        .cfg_timeout_enable     (cfg_axi_timeout_enable),
        .cfg_perf_enable        (cfg_axi_perf_enable),
        .cfg_timeout_cycles     (cfg_axi_timeout_cycles),
        .cfg_latency_threshold  (cfg_axi_latency_threshold),
        .cfg_axi_pkt_mask       (cfg_axi_pkt_mask),
        .cfg_axi_err_select     (cfg_axi_err_select),
        .cfg_axi_error_mask     (cfg_axi_error_mask),
        .cfg_axi_timeout_mask   (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask     (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask    (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),
        .cfg_cg_enable          (cfg_cg_enable),
        .cfg_cg_idle_threshold  (cfg_cg_idle_threshold),
        .cfg_cg_force_on        (cfg_cg_force_on),
        .cfg_cg_gate_monitor    (cfg_cg_gate_monitor),
        .cfg_cg_gate_reporter   (cfg_cg_gate_reporter),
        .cfg_cg_gate_timers     (cfg_cg_gate_timers),
        .monbus_valid           (ctrlwr_axi_mon_valid),
        .monbus_ready           (ctrlwr_axi_mon_ready),
        .monbus_packet          (ctrlwr_axi_mon_packet),
        .busy                   (ctrlwr_axi_busy),
        .active_transactions    (ctrlwr_axi_active_transactions),
        .error_count            (ctrlwr_axi_error_count),
        .transaction_count      (ctrlwr_axi_transaction_count),
        .cg_monitor_gated       (),
        .cg_reporter_gated      (),
        .cg_timers_gated        (),
        .cg_cycles_saved        (),
        .cfg_conflict_error     ()
    );

    //=========================================================================
    // MonBus Aggregation - Combine all monitor outputs
    //=========================================================================

    // Map scheduler group monitor outputs
    always_comb begin
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            monbus_valid_in[i] = sched_mon_valid[i];
            sched_mon_ready[i] = monbus_ready_in[i];
            monbus_packet_in[i] = sched_mon_packet[i];
        end

        // Map AXI master monitor outputs (3 AXI masters: desc, ctrlrd, ctrlwr)
        monbus_valid_in[CHANNEL_COUNT]   = desc_axi_mon_valid;
        desc_axi_mon_ready               = monbus_ready_in[CHANNEL_COUNT];
        monbus_packet_in[CHANNEL_COUNT]  = desc_axi_mon_packet;

        monbus_valid_in[CHANNEL_COUNT+1] = ctrlrd_axi_mon_valid;
        ctrlrd_axi_mon_ready             = monbus_ready_in[CHANNEL_COUNT+1];
        monbus_packet_in[CHANNEL_COUNT+1] = ctrlrd_axi_mon_packet;

        monbus_valid_in[CHANNEL_COUNT+2] = ctrlwr_axi_mon_valid;
        ctrlwr_axi_mon_ready             = monbus_ready_in[CHANNEL_COUNT+2];
        monbus_packet_in[CHANNEL_COUNT+2] = ctrlwr_axi_mon_packet;
    end

    // MonBus Arbiter - Round-robin with skid buffers
    monbus_arbiter #(
        .CLIENTS                (MONBUS_CLIENTS),
        .INPUT_SKID_ENABLE      (MONBUS_INPUT_SKID_ENABLE),
        .OUTPUT_SKID_ENABLE     (MONBUS_OUTPUT_SKID_ENABLE),
        .INPUT_SKID_DEPTH       (MONBUS_INPUT_SKID_DEPTH),
        .OUTPUT_SKID_DEPTH      (MONBUS_OUTPUT_SKID_DEPTH)
    ) u_monbus_arbiter (
        // Clock and Reset
        .axi_aclk               (clk),
        .axi_aresetn            (rst_n),

        // Block arbitration (tie low)
        .block_arb              (1'b0),

        // Monitor bus inputs from all clients
        .monbus_valid_in        (monbus_valid_in),
        .monbus_ready_in        (monbus_ready_in),
        .monbus_packet_in       (monbus_packet_in),

        // Aggregated monitor bus output
        .monbus_valid           (mon_valid),
        .monbus_ready           (mon_ready),
        .monbus_packet          (mon_packet),

        // Debug/Status (unused)
        .grant_valid            (),
        .grant                  (),
        .grant_id               (),
        .last_grant             ()
    );

    //=========================================================================
    // Array-Level Status Aggregation
    //=========================================================================

    // Count active channels (not idle)
    always_comb begin
        active_channels = '0;
        for (int i = 0; i < CHANNEL_COUNT; i++) begin
            if (!scheduler_idle[i]) begin
                active_channels = active_channels + 1'b1;
            end
        end
    end

    // Aggregate error counts (3 AXI masters: desc, ctrlrd, ctrlwr)
    assign total_error_count = desc_axi_error_count + ctrlrd_axi_error_count + ctrlwr_axi_error_count;

    // Aggregate transaction counts (3 AXI masters: desc, ctrlrd, ctrlwr)
    assign total_transaction_count = desc_axi_transaction_count + ctrlrd_axi_transaction_count + ctrlwr_axi_transaction_count;

endmodule : scheduler_group_array
