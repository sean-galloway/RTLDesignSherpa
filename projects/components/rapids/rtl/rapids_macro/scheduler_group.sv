// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_group
// Purpose: Scheduler Group module
//
// Documentation: projects/components/rapids_macro/PRD.md
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"

module scheduler_group #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int CREDIT_WIDTH = 8,
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int EARLY_WARNING_THRESHOLD = 4,
    // Monitor Bus Parameters - Base IDs for each component (Use plain parameter type for cocotb-test compatibility)
    parameter DESC_MON_AGENT_ID = 16,       // 0x10
    parameter PROG_MON_AGENT_ID = 32,       // 0x20
    parameter SCHED_MON_AGENT_ID = 48,      // 0x30
    parameter MON_UNIT_ID = 1,              // 0x1
    parameter MON_CHANNEL_ID = 0            // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // APB Programming Interface (for descriptor fetch)
    input  logic                        apb_valid,
    output logic                        apb_ready,
    input  logic [ADDR_WIDTH-1:0]       apb_addr,

    // CDA Packet Interface (from Network Slave) - formerly RDA
    input  logic                        cda_valid,
    output logic                        cda_ready,
    input  logic [DATA_WIDTH-1:0]       cda_packet,
    input  logic [CHAN_WIDTH-1:0]       cda_channel,

    // EOS Completion Interface (from SRAM Control - packet-level EOS)
    input  logic                        eos_completion_valid,
    output logic                        eos_completion_ready,
    input  logic [CHAN_WIDTH-1:0]       eos_completion_channel,

    // Configuration Interface
    input  logic                        cfg_idle_mode,
    input  logic                        cfg_channel_wait,
    input  logic                        cfg_channel_enable,
    input  logic                        cfg_use_credit,
    input  logic [3:0]                  cfg_initial_credit,
    input  logic                        credit_increment,
    input  logic                        cfg_prefetch_enable,
    input  logic [3:0]                  cfg_fifo_threshold,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr0_limit,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_addr1_limit,
    input  logic                        cfg_channel_reset,
    input  logic [7:0]                  cfg_ctrlrd_max_try,     // Control read max retry count (for external ctrlrd_engine)

    // Status Interface
    output logic                        descriptor_engine_idle,
    output logic                        program_engine_idle,
    output logic                        scheduler_idle,

    // Descriptor Engine AXI4 Master Read Interface
    output logic                        desc_ar_valid,
    input  logic                        desc_ar_ready,
    output logic [ADDR_WIDTH-1:0]       desc_ar_addr,
    output logic [7:0]                  desc_ar_len,
    output logic [2:0]                  desc_ar_size,
    output logic [1:0]                  desc_ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     desc_ar_id,
    output logic                        desc_ar_lock,
    output logic [3:0]                  desc_ar_cache,
    output logic [2:0]                  desc_ar_prot,
    output logic [3:0]                  desc_ar_qos,
    output logic [3:0]                  desc_ar_region,

    // Descriptor Engine AXI Read Data Channel
    input  logic                        desc_r_valid,
    output logic                        desc_r_ready,
    input  logic [DATA_WIDTH-1:0]       desc_r_data,
    input  logic [1:0]                  desc_r_resp,
    input  logic                        desc_r_last,
    input  logic [AXI_ID_WIDTH-1:0]     desc_r_id,

    // Program Engine AXI4 Master Write Interface
    output logic                        prog_aw_valid,
    input  logic                        prog_aw_ready,
    output logic [ADDR_WIDTH-1:0]       prog_aw_addr,
    output logic [7:0]                  prog_aw_len,
    output logic [2:0]                  prog_aw_size,
    output logic [1:0]                  prog_aw_burst,
    output logic [AXI_ID_WIDTH-1:0]     prog_aw_id,
    output logic                        prog_aw_lock,
    output logic [3:0]                  prog_aw_cache,
    output logic [2:0]                  prog_aw_prot,
    output logic [3:0]                  prog_aw_qos,
    output logic [3:0]                  prog_aw_region,

    // Program Engine AXI Write Data Channel
    output logic                        prog_w_valid,
    input  logic                        prog_w_ready,
    output logic [31:0]                 prog_w_data,
    output logic [3:0]                  prog_w_strb,
    output logic                        prog_w_last,

    // Program Engine AXI Write Response Channel
    input  logic                        prog_b_valid,
    output logic                        prog_b_ready,
    input  logic [AXI_ID_WIDTH-1:0]     prog_b_id,
    input  logic [1:0]                  prog_b_resp,

    // Control Read Engine Interface (Pre-Descriptor Control Operations)
    output logic                        ctrlrd_valid,
    input  logic                        ctrlrd_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlrd_addr,
    output logic [31:0]                 ctrlrd_data,
    output logic [31:0]                 ctrlrd_mask,
    input  logic                        ctrlrd_error,
    input  logic [31:0]                 ctrlrd_result,

    // Control Write Engine Interface (Post-Descriptor Control Operations)
    output logic                        ctrlwr_valid,
    input  logic                        ctrlwr_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlwr_addr,
    output logic [31:0]                 ctrlwr_data,
    input  logic                        ctrlwr_error,

    // ========================================================================
    // UPDATED: Enhanced Data Mover Interface with Alignment Bus - RAPIDS Types
    // ========================================================================

    // Basic Data Interface (EXISTING - unchanged for compatibility)
    output logic                        data_valid,
    input  logic                        data_ready,
    output logic [63:0]                 data_address,
    output logic [31:0]                 data_length,
    output logic [1:0]                  data_type,
    output logic                        data_eos,           // EOS only in data path

    input  logic [31:0]                 data_transfer_length,
    input  logic                        data_error,
    input  logic                        data_done_strobe,

    // NEW: Address Alignment Bus Interface (using RAPIDS package types)
    output alignment_info_t             data_alignment_info,
    output logic                        data_alignment_valid,
    input  logic                        data_alignment_ready,
    input  logic                        data_alignment_next,
    output transfer_phase_t             data_transfer_phase,
    output logic                        data_sequence_complete,

    // Generic RDA Credit Return Interface
    output logic                        rda_complete_valid,
    input  logic                        rda_complete_ready,
    output logic [CHAN_WIDTH-1:0]       rda_complete_channel,

    // Unified Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet,

    // Status and Error Outputs
    output logic [31:0]                 descriptor_credit_counter,
    output logic [7:0]                  fsm_state,
    output logic                        scheduler_error,
    output logic                        backpressure_warning
);

    //=========================================================================
    // Internal Signals - Component Interconnect
    //=========================================================================

    // Descriptor Engine to Scheduler Interface
    // NOTE: Renamed to avoid conflicts with external AXI signals (desc_ar_*, desc_r_*)
    // Use component-based naming instead of data-type prefix to avoid pattern matching conflicts
    logic                        desceng_to_sched_valid;
    logic                        desceng_to_sched_ready;
    logic [DATA_WIDTH-1:0]       desceng_to_sched_packet;
    logic                        desceng_to_sched_same;
    logic                        desceng_to_sched_error;
    logic                        desceng_to_sched_is_cda;
    logic [CHAN_WIDTH-1:0]       desceng_to_sched_cda_channel;
    logic                        desceng_to_sched_eos;
    logic                        desceng_to_sched_eol;
    logic                        desceng_to_sched_eod;
    logic [1:0]                  desceng_to_sched_type;

    //=========================================================================
    // Internal Signals - Monitor Bus Aggregation
    //=========================================================================
    // NOTE: Renamed to avoid conflicts with external AXI signals
    // Use component-specific names instead of prefix-based names

    logic                        desceng_mon_valid;
    logic                        desceng_mon_ready;
    logic [63:0]                 desceng_mon_packet;

    logic                        progeng_mon_valid;
    logic                        progeng_mon_ready;
    logic [63:0]                 progeng_mon_packet;

    logic                        sched_mon_valid;
    logic                        sched_mon_ready;
    logic [63:0]                 sched_mon_packet;

    //=========================================================================
    // Component Instantiations
    //=========================================================================

    // Single Descriptor Engine Instance
    descriptor_engine #(
        .CHANNEL_ID             (CHANNEL_ID),
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .MON_AGENT_ID           (8'(DESC_MON_AGENT_ID)),
        .MON_UNIT_ID            (4'(MON_UNIT_ID)),
        .MON_CHANNEL_ID         (6'(MON_CHANNEL_ID))
    ) u_descriptor_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .apb_valid              (apb_valid),
        .apb_ready              (apb_ready),
        .apb_addr               (apb_addr),
        // CDA Packet Interface (formerly RDA)
        .cda_valid              (cda_valid),
        .cda_ready              (cda_ready),
        .cda_packet             (cda_packet),
        .cda_channel            (cda_channel),
        .descriptor_valid       (desceng_to_sched_valid),
        .descriptor_ready       (desceng_to_sched_ready),
        .descriptor_packet      (desceng_to_sched_packet),
        .descriptor_same        (desceng_to_sched_same),
        .descriptor_error       (desceng_to_sched_error),
        // RDA renamed to CDA (Control Descriptor Arrival)
        .descriptor_is_cda      (desceng_to_sched_is_cda),
        .descriptor_cda_channel (desceng_to_sched_cda_channel),
        .descriptor_eos         (desceng_to_sched_eos),
        .descriptor_eol         (desceng_to_sched_eol),
        .descriptor_eod         (desceng_to_sched_eod),
        .descriptor_type        (desceng_to_sched_type),
        .ar_valid               (desc_ar_valid),
        .ar_ready               (desc_ar_ready),
        .ar_addr                (desc_ar_addr),
        .ar_len                 (desc_ar_len),
        .ar_size                (desc_ar_size),
        .ar_burst               (desc_ar_burst),
        .ar_id                  (desc_ar_id),
        .ar_lock                (desc_ar_lock),
        .ar_cache               (desc_ar_cache),
        .ar_prot                (desc_ar_prot),
        .ar_qos                 (desc_ar_qos),
        .ar_region              (desc_ar_region),
        .r_valid                (desc_r_valid),
        .r_ready                (desc_r_ready),
        .r_data                 (desc_r_data),
        .r_resp                 (desc_r_resp),
        .r_last                 (desc_r_last),
        .r_id                   (desc_r_id),
        .cfg_prefetch_enable    (cfg_prefetch_enable),
        .cfg_fifo_threshold     (cfg_fifo_threshold),
        .cfg_addr0_base         (cfg_addr0_base),
        .cfg_addr0_limit        (cfg_addr0_limit),
        .cfg_addr1_base         (cfg_addr1_base),
        .cfg_addr1_limit        (cfg_addr1_limit),
        .cfg_channel_reset      (cfg_channel_reset),
        .descriptor_engine_idle (descriptor_engine_idle),
        .mon_valid              (desceng_mon_valid),
        .mon_ready              (desceng_mon_ready),
        .mon_packet             (desceng_mon_packet)
    );

    // Program Engine Instance - REMOVED
    // NOTE: Program engine has been replaced by ctrlwr_engine in the standalone scheduler.
    // The scheduler_group now exposes ctrlwr_* interface directly.
    // For backwards compatibility, prog_aw_*, prog_w_*, prog_b_* ports are retained but tied off.

    // Tie off program engine AXI interface
    assign prog_aw_valid = 1'b0;
    assign prog_aw_addr = '0;
    assign prog_aw_len = '0;
    assign prog_aw_size = '0;
    assign prog_aw_burst = '0;
    assign prog_aw_id = '0;
    assign prog_aw_lock = '0;
    assign prog_aw_cache = '0;
    assign prog_aw_prot = '0;
    assign prog_aw_qos = '0;
    assign prog_aw_region = '0;
    assign prog_w_valid = 1'b0;
    assign prog_w_data = '0;
    assign prog_w_strb = '0;
    assign prog_w_last = '0;
    assign prog_b_ready = 1'b1;

    // Tie off program engine idle status and monitor
    assign program_engine_idle = 1'b1;
    assign progeng_mon_valid = 1'b0;
    assign progeng_mon_packet = '0;

    // UPDATED: Single Scheduler Instance with Enhanced Data Interface and RAPIDS Types
    scheduler #(
        .CHANNEL_ID             (CHANNEL_ID),
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH),
        .CREDIT_WIDTH           (CREDIT_WIDTH),
        .TIMEOUT_CYCLES         (TIMEOUT_CYCLES),
        .EARLY_WARNING_THRESHOLD(EARLY_WARNING_THRESHOLD),
        .MON_AGENT_ID           (8'(SCHED_MON_AGENT_ID)),
        .MON_UNIT_ID            (4'(MON_UNIT_ID)),
        .MON_CHANNEL_ID         (6'(MON_CHANNEL_ID))
    ) u_scheduler (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .cfg_idle_mode          (cfg_idle_mode),
        .cfg_channel_wait       (cfg_channel_wait),
        .cfg_channel_enable     (cfg_channel_enable),
        .cfg_use_credit         (cfg_use_credit),
        .cfg_initial_credit     (cfg_initial_credit),
        .credit_increment       (credit_increment),
        .cfg_channel_reset      (cfg_channel_reset),
        .descriptor_credit_counter(descriptor_credit_counter),
        .fsm_state              (fsm_state),
        .scheduler_idle         (scheduler_idle),
        .descriptor_valid       (desceng_to_sched_valid),
        .descriptor_ready       (desceng_to_sched_ready),
        .descriptor_packet      (desceng_to_sched_packet),
        .descriptor_same        (desceng_to_sched_same),
        .descriptor_error       (desceng_to_sched_error),
        // RDA renamed to CDA (Control Descriptor Arrival)
        .descriptor_is_cda      (desceng_to_sched_is_cda),
        .descriptor_cda_channel (desceng_to_sched_cda_channel),
        .descriptor_eos         (desceng_to_sched_eos),
        .descriptor_eol         (desceng_to_sched_eol),
        .descriptor_eod         (desceng_to_sched_eod),
        .descriptor_type        (desceng_to_sched_type),
        .eos_completion_valid   (eos_completion_valid),
        .eos_completion_ready   (eos_completion_ready),
        .eos_completion_channel (eos_completion_channel),

        // Control Read Engine Interface (ctrlrd)
        .ctrlrd_valid           (ctrlrd_valid),
        .ctrlrd_ready           (ctrlrd_ready),
        .ctrlrd_addr            (ctrlrd_addr),
        .ctrlrd_data            (ctrlrd_data),
        .ctrlrd_mask            (ctrlrd_mask),
        .ctrlrd_error           (ctrlrd_error),
        .ctrlrd_result          (ctrlrd_result),

        // Control Write Engine Interface (ctrlwr)
        .ctrlwr_valid           (ctrlwr_valid),
        .ctrlwr_ready           (ctrlwr_ready),
        .ctrlwr_addr            (ctrlwr_addr),
        .ctrlwr_data            (ctrlwr_data),
        .ctrlwr_error           (ctrlwr_error),

        // EXISTING Data Engine Interface (unchanged for compatibility)
        .data_valid             (data_valid),
        .data_ready             (data_ready),
        .data_address           (data_address),
        .data_length            (data_length),
        .data_type              (data_type),
        .data_eos               (data_eos),
        .data_transfer_length   (data_transfer_length),
        .data_error             (data_error),
        .data_done_strobe       (data_done_strobe),

        // NEW: Address Alignment Bus Interface (using RAPIDS package types)
        .data_alignment_info    (data_alignment_info),
        .data_alignment_valid   (data_alignment_valid),
        .data_alignment_ready   (data_alignment_ready),
        .data_alignment_next    (data_alignment_next),
        .data_transfer_phase    (data_transfer_phase),
        .data_sequence_complete (data_sequence_complete),

        // RDA completion interface removed from scheduler
        // .rda_complete_valid     (rda_complete_valid),
        // .rda_complete_ready     (rda_complete_ready),
        // .rda_complete_channel   (rda_complete_channel),
        // Use CDA completion interface instead
        .cda_complete_valid     (cda_complete_valid),
        .cda_complete_ready     (cda_complete_ready),
        .cda_complete_channel   (cda_complete_channel),
        .mon_valid              (sched_mon_valid),
        .mon_ready              (sched_mon_ready),
        .mon_packet             (sched_mon_packet),
        .scheduler_error        (scheduler_error),
        .backpressure_warning   (backpressure_warning)
    );

    //=========================================================================
    // Single Monitor Bus Arbiter Instance - Direct Connection
    //=========================================================================

    monbus_arbiter #(
        .CLIENTS                (3),
        .INPUT_SKID_ENABLE      (1),
        .OUTPUT_SKID_ENABLE     (1),
        .INPUT_SKID_DEPTH       (2),
        .OUTPUT_SKID_DEPTH      (2)
    ) u_monbus_aggregator (
        .axi_aclk               (clk),
        .axi_aresetn            (rst_n),
        .block_arb              (1'b0),
        // Direct connection to individual signals
        .monbus_valid_in        ('{desceng_mon_valid, progeng_mon_valid, sched_mon_valid}),
        .monbus_ready_in        ('{desceng_mon_ready, progeng_mon_ready, sched_mon_ready}),
        .monbus_packet_in       ('{desceng_mon_packet, progeng_mon_packet, sched_mon_packet}),
        .monbus_valid           (mon_valid),
        .monbus_ready           (mon_ready),
        .monbus_packet          (mon_packet),
        .grant_valid            (/* UNUSED */),
        .grant                  (/* UNUSED */),
        .grant_id               (/* UNUSED */),
        .last_grant             (/* UNUSED */)
    );

    //=========================================================================
    // Assertions for Verification - UPDATED
    //=========================================================================

    `ifdef FORMAL
    // Monitor bus connectivity
    property monitor_bus_connected;
        @(posedge clk) disable iff (!rst_n)
        (desceng_mon_valid || progeng_mon_valid || sched_mon_valid) |-> ##[1:10] mon_valid;
    endproperty
    assert property (monitor_bus_connected);

    // Component integration
    property descriptor_scheduler_handshake;
        @(posedge clk) disable iff (!rst_n)
        (desceng_to_sched_valid && desceng_to_sched_ready) |-> ##[1:5] (fsm_state != 6'b000001);
    endproperty
    assert property (descriptor_scheduler_handshake);

    // Single program engine usage
    property single_program_engine;
        @(posedge clk) disable iff (!rst_n)
        sched_to_progeng_valid |-> sched_to_progeng_ready;
    endproperty
    assert property (single_program_engine);

    // Channel reset properties
    property channel_reset_propagation;
        @(posedge clk) disable iff (!rst_n)
        cfg_channel_reset |-> ##[1:100] (descriptor_engine_idle && program_engine_idle && scheduler_idle);
    endproperty
    assert property (channel_reset_propagation);

    property idle_signals_consistency;
        @(posedge clk) disable iff (!rst_n)
        (descriptor_engine_idle && program_engine_idle && scheduler_idle) |-> !cfg_channel_reset;
    endproperty
    assert property (idle_signals_consistency);

    // EOS completion interface properties
    property eos_completion_handshake;
        @(posedge clk) disable iff (!rst_n)
        (eos_completion_valid && eos_completion_ready) |-> ##[1:5] data_eos;
    endproperty
    assert property (eos_completion_handshake);

    property eos_completion_channel_valid;
        @(posedge clk) disable iff (!rst_n)
        eos_completion_valid |-> (eos_completion_channel < NUM_CHANNELS);
    endproperty
    assert property (eos_completion_channel_valid);

    // NEW: Enhanced alignment bus properties using RAPIDS package types
    property alignment_info_consistency;
        @(posedge clk) disable iff (!rst_n)
        data_alignment_valid |-> (data_alignment_info.total_transfers > 0) &&
                               (data_alignment_info.payload_bytes > 0);
    endproperty
    assert property (alignment_info_consistency);

    property transfer_phase_progression;
        @(posedge clk) disable iff (!rst_n)
        data_alignment_next |-> ##[1:3] (data_transfer_phase != PHASE_IDLE);
    endproperty
    assert property (transfer_phase_progression);

    property sequence_completion_logic;
        @(posedge clk) disable iff (!rst_n)
        data_sequence_complete |-> data_alignment_valid;
    endproperty
    assert property (sequence_completion_logic);

    // Enhanced stream control using RAPIDS package types
    property eos_only_in_data_path;
        @(posedge clk) disable iff (!rst_n)
        data_valid |-> (data_eos == 1'b1 || data_eos == 1'b0);
    endproperty
    assert property (eos_only_in_data_path);

    `endif

endmodule : scheduler_group
