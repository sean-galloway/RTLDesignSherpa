// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_group_array
// Purpose: STREAM Scheduler Group Array - Multi-channel DMA with shared resources
//
// Description:
//   Top-level array of 8 scheduler_group instances with:
//   - Shared descriptor AXI master (round-robin arbitration)
//   - Shared data read interface (to axi_read_engine)
//   - Shared data write interface (to axi_write_engine)
//   - Unified MonBus aggregation (9 sources: 8 channels + desc AXI monitor)
//
//   Simplified from RAPIDS for tutorial focus:
//   - 8 channels (vs 32 in RAPIDS)
//   - No control read/write engines
//   - No program engine
//   - No network interfaces (RDA, EOS completion)
//   - No alignment bus
//   - Direct data path interfaces (beats-based, no chunks)
//
// Documentation: projects/components/stream/docs/stream_spec/
// Subsystem: stream_macro
//
// Author: sean galloway
// Created: 2025-10-19

`timescale 1ns / 1ps

// Import STREAM and monitor packages
`include "stream_imports.svh"

module scheduler_group_array #(
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int TIMEOUT_CYCLES = 1000,
    // Monitor Bus Base IDs
    parameter DESC_MON_BASE_AGENT_ID = 16,   // 0x10 - Descriptor Engines (16-23)
    parameter SCHED_MON_BASE_AGENT_ID = 48,  // 0x30 - Schedulers (48-55)
    parameter DESC_AXI_MON_AGENT_ID = 8,     // 0x08 - Descriptor AXI Master Monitor
    parameter MON_UNIT_ID = 1                // 0x1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // APB Programming Interface (per channel kick-off)
    input  logic [NUM_CHANNELS-1:0]              apb_valid,
    output logic [NUM_CHANNELS-1:0]              apb_ready,
    input  logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] apb_addr,

    // Configuration Interface (per channel)
    input  logic [NUM_CHANNELS-1:0]              cfg_channel_enable,
    input  logic [NUM_CHANNELS-1:0]              cfg_channel_reset,

    // Scheduler Configuration (global - applied to all channels)
    input  logic                                 cfg_sched_enable,          // Master scheduler enable
    input  logic [15:0]                          cfg_sched_timeout_cycles,  // Timeout threshold
    input  logic                                 cfg_sched_timeout_enable,  // Enable timeout detection
    input  logic                                 cfg_sched_err_enable,      // Enable error reporting
    input  logic                                 cfg_sched_compl_enable,    // Enable completion reporting
    input  logic                                 cfg_sched_perf_enable,     // Enable performance monitoring

    // Descriptor Engine Configuration (global - applied to all channels)
    input  logic                                 cfg_desceng_enable,        // Master descriptor engine enable
    input  logic                                 cfg_desceng_prefetch,      // Enable descriptor prefetch
    input  logic [3:0]                           cfg_desceng_fifo_thresh,   // FIFO threshold for prefetch
    input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr0_base,    // Address range 0 base
    input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr0_limit,   // Address range 0 limit
    input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr1_base,    // Address range 1 base
    input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr1_limit,   // Address range 1 limit

    // Descriptor AXI Monitor Configuration
    input  logic                                 cfg_daxmon_err_enable,     // Enable error detection
    input  logic                                 cfg_daxmon_compl_enable,   // Enable completion packets
    input  logic                                 cfg_daxmon_timeout_enable, // Enable timeout detection
    input  logic                                 cfg_daxmon_perf_enable,    // Enable performance packets
    input  logic                                 cfg_daxmon_debug_enable,   // Enable debug packets

    // Status Interface (per channel)
    output logic [NUM_CHANNELS-1:0]              descriptor_engine_idle,
    output logic [NUM_CHANNELS-1:0]              scheduler_idle,
    output logic [NUM_CHANNELS-1:0][6:0]         scheduler_state,  // ONE-HOT encoding (7 bits)

    // Descriptor AXI Monitor Status
    output logic                                 desc_axi_mon_busy,
    output logic [7:0]                           desc_axi_mon_active_txns,
    output logic [15:0]                          desc_axi_mon_error_count,
    output logic [31:0]                          desc_axi_mon_txn_count,
    output logic                                 desc_axi_mon_conflict_error,

    // Shared Descriptor AXI4 Master Read Interface (256-bit descriptor fetch)
    output logic                        desc_axi_arvalid,
    input  logic                        desc_axi_arready,
    output logic [ADDR_WIDTH-1:0]       desc_axi_araddr,
    output logic [7:0]                  desc_axi_arlen,
    output logic [2:0]                  desc_axi_arsize,
    output logic [1:0]                  desc_axi_arburst,
    output logic [AXI_ID_WIDTH-1:0]     desc_axi_arid,
    output logic                        desc_axi_arlock,
    output logic [3:0]                  desc_axi_arcache,
    output logic [2:0]                  desc_axi_arprot,
    output logic [3:0]                  desc_axi_arqos,
    output logic [3:0]                  desc_axi_arregion,

    // Descriptor AXI Read Data Channel (FIXED 256-bit for descriptor size)
    input  logic                        desc_axi_rvalid,
    output logic                        desc_axi_rready,
    input  logic [255:0]                desc_axi_rdata,  // FIXED 256-bit descriptor
    input  logic [1:0]                  desc_axi_rresp,
    input  logic                        desc_axi_rlast,
    input  logic [AXI_ID_WIDTH-1:0]     desc_axi_rid,

    // Shared Data Read Interface (to AXI Read Engine)
    // Per-channel arrays - direct passthrough to engines
    output logic [NUM_CHANNELS-1:0]                     datard_valid,
    input  logic [NUM_CHANNELS-1:0]                     datard_ready,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     datard_addr,
    output logic [NUM_CHANNELS-1:0][31:0]               datard_beats_remaining,

    // Shared Data Write Interface (to AXI Write Engine)
    // Per-channel arrays - direct passthrough to engines
    output logic [NUM_CHANNELS-1:0]                     datawr_valid,
    input  logic [NUM_CHANNELS-1:0]                     datawr_ready,
    output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     datawr_addr,
    output logic [NUM_CHANNELS-1:0][31:0]               datawr_beats_remaining,

    // Data Path Completion Strobes (per-channel from engines)
    input  logic [NUM_CHANNELS-1:0]                     datard_done_strobe,
    input  logic [NUM_CHANNELS-1:0][31:0]               datard_beats_done,
    input  logic [NUM_CHANNELS-1:0]                     datawr_done_strobe,
    input  logic [NUM_CHANNELS-1:0][31:0]               datawr_beats_done,

    // Error Signals (per-channel from engines)
    input  logic [NUM_CHANNELS-1:0]                     datard_error,
    input  logic [NUM_CHANNELS-1:0]                     datawr_error,

    // Unified Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    //=========================================================================
    // Internal Signals - Per-Channel Descriptor AXI Interface
    //=========================================================================

    // Descriptor AR channel (per channel)
    logic [NUM_CHANNELS-1:0]                     desc_ar_valid;
    logic [NUM_CHANNELS-1:0]                     desc_ar_ready;
    logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     desc_ar_addr;
    logic [NUM_CHANNELS-1:0][7:0]                desc_ar_len;
    logic [NUM_CHANNELS-1:0][2:0]                desc_ar_size;
    logic [NUM_CHANNELS-1:0][1:0]                desc_ar_burst;
    logic [NUM_CHANNELS-1:0][AXI_ID_WIDTH-1:0]   desc_ar_id;
    logic [NUM_CHANNELS-1:0]                     desc_ar_lock;
    logic [NUM_CHANNELS-1:0][3:0]                desc_ar_cache;
    logic [NUM_CHANNELS-1:0][2:0]                desc_ar_prot;
    logic [NUM_CHANNELS-1:0][3:0]                desc_ar_qos;
    logic [NUM_CHANNELS-1:0][3:0]                desc_ar_region;

    // Descriptor R channel (per channel)
    // NOTE: Descriptors are FIXED at 256-bit width (not DATA_WIDTH)
    logic [NUM_CHANNELS-1:0]                     desc_r_valid;
    logic [NUM_CHANNELS-1:0]                     desc_r_ready;
    logic [NUM_CHANNELS-1:0][255:0]              desc_r_data;  // 256-bit descriptors
    logic [NUM_CHANNELS-1:0][1:0]                desc_r_resp;
    logic [NUM_CHANNELS-1:0]                     desc_r_last;
    logic [NUM_CHANNELS-1:0][AXI_ID_WIDTH-1:0]   desc_r_id;

    //=========================================================================
    // Internal Signals - Per-Channel Data Interfaces
    // NOTE: These are directly connected to outputs - no arbitration!
    //=========================================================================
    // (Removed - using output ports directly)

    //=========================================================================
    // Internal Signals - Monitor Bus (per channel)
    //=========================================================================

    logic [NUM_CHANNELS-1:0]                     mon_valid_ch;
    logic [NUM_CHANNELS-1:0]                     mon_ready_ch;
    logic [NUM_CHANNELS-1:0][63:0]               mon_packet_ch;

    //=========================================================================
    // Internal Signals - Descriptor AXI Arbitration
    //=========================================================================

    logic                                        desc_ar_grant_valid;
    logic [NUM_CHANNELS-1:0]                     desc_ar_grant;
    logic [NUM_CHANNELS-1:0]                     desc_ar_grant_ack;
    logic [CHAN_WIDTH-1:0]                       desc_ar_grant_id;

    // Internal AXI signals (post-arbitration, pre-monitor)
    logic                                        desc_axi_int_arvalid;
    logic                                        desc_axi_int_arready;
    logic [ADDR_WIDTH-1:0]                       desc_axi_int_araddr;
    logic [7:0]                                  desc_axi_int_arlen;
    logic [2:0]                                  desc_axi_int_arsize;
    logic [1:0]                                  desc_axi_int_arburst;
    logic [AXI_ID_WIDTH-1:0]                     desc_axi_int_arid;
    logic                                        desc_axi_int_arlock;
    logic [3:0]                                  desc_axi_int_arcache;
    logic [2:0]                                  desc_axi_int_arprot;
    logic [3:0]                                  desc_axi_int_arqos;
    logic [3:0]                                  desc_axi_int_arregion;

    logic                                        desc_axi_int_rvalid;
    logic                                        desc_axi_int_rready;
    logic [255:0]                                desc_axi_int_rdata;  // FIXED 256-bit descriptor
    logic [1:0]                                  desc_axi_int_rresp;
    logic                                        desc_axi_int_rlast;
    logic [AXI_ID_WIDTH-1:0]                     desc_axi_int_rid;

    //=========================================================================
    // Internal Signals - Data Read/Write (NO ARBITRATION - direct passthrough)
    //=========================================================================
    // (Removed - using output ports directly)

    //=========================================================================
    // Internal Signals - Monitor Bus Aggregation
    //=========================================================================

    // MonBus from descriptor AXI monitor
    logic                                        desc_axi_mon_valid;
    logic                                        desc_axi_mon_ready;
    logic [63:0]                                 desc_axi_mon_packet;

    // Combined MonBus arrays (9 sources: 8 channels + 1 desc AXI monitor)
    localparam int MONBUS_SOURCES = NUM_CHANNELS + 1;
    // Use unpacked arrays to match monbus_arbiter port types
    logic                    monbus_valid_all[MONBUS_SOURCES];
    logic                    monbus_ready_all[MONBUS_SOURCES];
    logic [63:0]             monbus_packet_all[MONBUS_SOURCES];

    //=========================================================================
    // Scheduler Group Array Instantiation
    //=========================================================================

    generate
        for (genvar ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_scheduler_groups
            scheduler_group #(
                .CHANNEL_ID             (ch),
                .NUM_CHANNELS           (NUM_CHANNELS),
                .CHAN_WIDTH             (CHAN_WIDTH),
                .ADDR_WIDTH             (ADDR_WIDTH),
                .DATA_WIDTH             (DATA_WIDTH),
                .AXI_ID_WIDTH           (AXI_ID_WIDTH),
                .TIMEOUT_CYCLES         (TIMEOUT_CYCLES),
                .DESC_MON_AGENT_ID      (8'(DESC_MON_BASE_AGENT_ID + ch)),
                .SCHED_MON_AGENT_ID     (8'(SCHED_MON_BASE_AGENT_ID + ch)),
                .MON_UNIT_ID            (4'(MON_UNIT_ID)),
                .MON_CHANNEL_ID         (6'(ch))
            ) u_scheduler_group (
                .clk                    (clk),
                .rst_n                  (rst_n),

                // APB interface
                .apb_valid              (apb_valid[ch]),
                .apb_ready              (apb_ready[ch]),
                .apb_addr               (apb_addr[ch]),

                // Configuration
                .cfg_channel_enable     (cfg_channel_enable[ch]),
                .cfg_channel_reset      (cfg_channel_reset[ch]),

                // Scheduler Configuration (global)
                .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
                .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
                .cfg_sched_err_enable       (cfg_sched_err_enable),
                .cfg_sched_compl_enable     (cfg_sched_compl_enable),
                .cfg_sched_perf_enable      (cfg_sched_perf_enable),

                // Descriptor Engine Configuration (global)
                .cfg_desceng_prefetch       (cfg_desceng_prefetch),
                .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
                .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
                .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
                .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
                .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),

                // Status
                .descriptor_engine_idle (descriptor_engine_idle[ch]),
                .scheduler_idle         (scheduler_idle[ch]),
                .scheduler_state        (scheduler_state[ch]),

                // Descriptor AXI (per channel, to arbiter)
                .desc_ar_valid          (desc_ar_valid[ch]),
                .desc_ar_ready          (desc_ar_ready[ch]),
                .desc_ar_addr           (desc_ar_addr[ch]),
                .desc_ar_len            (desc_ar_len[ch]),
                .desc_ar_size           (desc_ar_size[ch]),
                .desc_ar_burst          (desc_ar_burst[ch]),
                .desc_ar_id             (desc_ar_id[ch]),
                .desc_ar_lock           (desc_ar_lock[ch]),
                .desc_ar_cache          (desc_ar_cache[ch]),
                .desc_ar_prot           (desc_ar_prot[ch]),
                .desc_ar_qos            (desc_ar_qos[ch]),
                .desc_ar_region         (desc_ar_region[ch]),

                .desc_r_valid           (desc_r_valid[ch]),
                .desc_r_ready           (desc_r_ready[ch]),
                .desc_r_data            (desc_r_data[ch]),
                .desc_r_resp            (desc_r_resp[ch]),
                .desc_r_last            (desc_r_last[ch]),
                .desc_r_id              (desc_r_id[ch]),

                // Data read interface (direct passthrough - no arbitration)
                .datard_valid           (datard_valid[ch]),
                .datard_ready           (datard_ready[ch]),
                .datard_addr            (datard_addr[ch]),
                .datard_beats_remaining (datard_beats_remaining[ch]),
                .datard_channel_id      (),  // Not used - index IS the channel ID

                // Data write interface (direct passthrough - no arbitration)
                .datawr_valid           (datawr_valid[ch]),
                .datawr_ready           (datawr_ready[ch]),
                .datawr_addr            (datawr_addr[ch]),
                .datawr_beats_remaining (datawr_beats_remaining[ch]),
                .datawr_channel_id      (),  // Not used - index IS the channel ID

                // Completion strobes (direct passthrough)
                .datard_done_strobe     (datard_done_strobe[ch]),
                .datard_beats_done      (datard_beats_done[ch]),
                .datawr_done_strobe     (datawr_done_strobe[ch]),
                .datawr_beats_done      (datawr_beats_done[ch]),

                // Error signals (direct passthrough)
                .datard_error           (datard_error[ch]),
                .datawr_error           (datawr_error[ch]),

                // Monitor bus (per channel)
                .mon_valid              (mon_valid_ch[ch]),
                .mon_ready              (mon_ready_ch[ch]),
                .mon_packet             (mon_packet_ch[ch])
            );
        end
    endgenerate

    //=========================================================================
    // Descriptor AXI AR Channel Arbitration
    //=========================================================================

    // Round-robin arbiter with ACK mode for proper AXI handshaking
    arbiter_round_robin #(
        .CLIENTS                (NUM_CHANNELS),
        .WAIT_GNT_ACK           (1)  // ACK mode: wait for grant acknowledgment
    ) u_desc_ar_arbiter (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .block_arb              (1'b0),
        .request                (desc_ar_valid),
        .grant_ack              (desc_ar_grant_ack),
        .grant_valid            (desc_ar_grant_valid),
        .grant                  (desc_ar_grant),
        .grant_id               (desc_ar_grant_id),
        .last_grant             (/* unused */)
    );

    // Grant acknowledgment: asserted when granted client's AR request is accepted
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            desc_ar_grant_ack[ch] = desc_ar_grant_valid && desc_ar_grant[ch] && desc_ar_valid[ch] && desc_axi_int_arready;
        end
    end

    // AR channel ready: granted channel sees internal ready only when grant is valid
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            desc_ar_ready[ch] = desc_ar_grant_valid && desc_ar_grant[ch] && desc_axi_int_arready;
        end
    end

    // AR channel multiplexing: select granted channel
    always_comb begin
        desc_axi_int_arvalid = '0;
        desc_axi_int_araddr = '0;
        desc_axi_int_arlen = '0;
        desc_axi_int_arsize = '0;
        desc_axi_int_arburst = '0;
        desc_axi_int_arid = '0;
        desc_axi_int_arlock = '0;
        desc_axi_int_arcache = '0;
        desc_axi_int_arprot = '0;
        desc_axi_int_arqos = '0;
        desc_axi_int_arregion = '0;

        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            if (desc_ar_grant[ch]) begin
                desc_axi_int_arvalid = desc_ar_valid[ch];
                desc_axi_int_araddr = desc_ar_addr[ch];
                desc_axi_int_arlen = desc_ar_len[ch];
                desc_axi_int_arsize = desc_ar_size[ch];
                desc_axi_int_arburst = desc_ar_burst[ch];
                // Embed channel ID in lower bits of AXI ID for R channel demux
                desc_axi_int_arid = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, ch[CHAN_WIDTH-1:0]};
                desc_axi_int_arlock = desc_ar_lock[ch];
                desc_axi_int_arcache = desc_ar_cache[ch];
                desc_axi_int_arprot = desc_ar_prot[ch];
                desc_axi_int_arqos = desc_ar_qos[ch];
                desc_axi_int_arregion = desc_ar_region[ch];
            end
        end
    end

    //=========================================================================
    // Descriptor AXI R Channel Demultiplexing
    //=========================================================================

    // Extract channel ID from lower bits of R channel ID
    logic [CHAN_WIDTH-1:0] desc_r_channel_id;
    assign desc_r_channel_id = desc_axi_int_rid[CHAN_WIDTH-1:0];

    // R channel demultiplexing: route based on ID
    always_comb begin
        // Default: no valid to any channel
        desc_r_valid = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            desc_r_data[ch] = desc_axi_int_rdata;
            desc_r_resp[ch] = desc_axi_int_rresp;
            desc_r_last[ch] = desc_axi_int_rlast;
            desc_r_id[ch] = desc_axi_int_rid;
        end

        // Route R valid to correct channel based on ID
        if (desc_axi_int_rvalid && desc_r_channel_id < NUM_CHANNELS) begin
            desc_r_valid[desc_r_channel_id] = 1'b1;
        end
    end

    // R channel ready: OR of all channel readies (only routed channel should be ready)
    assign desc_axi_int_rready = |desc_r_ready;

    //=========================================================================
    // Data Read/Write Interface - Direct Passthrough (NO ARBITRATION)
    //=========================================================================
    // All signals connected directly in scheduler_group instantiations above
    // Engines handle arbitration internally

    // NOTE: Removed all arbiter logic - engines expect per-channel arrays

    //=========================================================================
    // Descriptor AXI Master Monitor
    //=========================================================================

    axi4_master_rd_mon #(
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_DATA_WIDTH         (256),  // FIXED 256-bit for descriptor size
        .AXI_USER_WIDTH         (1),
        .UNIT_ID                (4'(MON_UNIT_ID)),
        .AGENT_ID               (8'(DESC_AXI_MON_AGENT_ID)),
        .MAX_TRANSACTIONS       (16),
        .ENABLE_FILTERING       (1)
    ) u_desc_axi_monitor (
        .aclk                   (clk),
        .aresetn                (rst_n),

        // FUB side (input to monitor) - AR Channel
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

        // FUB side (input to monitor) - R Channel
        .fub_axi_rid            (desc_axi_int_rid),
        .fub_axi_rdata          (desc_axi_int_rdata),
        .fub_axi_rresp          (desc_axi_int_rresp),
        .fub_axi_rlast          (desc_axi_int_rlast),
        .fub_axi_ruser          (),  // Unused, leave floating
        .fub_axi_rvalid         (desc_axi_int_rvalid),
        .fub_axi_rready         (desc_axi_int_rready),

        // Master side (output from monitor) - connect to external AXI for pass-through
        .m_axi_arid             (desc_axi_arid),
        .m_axi_araddr           (desc_axi_araddr),
        .m_axi_arlen            (desc_axi_arlen),
        .m_axi_arsize           (desc_axi_arsize),
        .m_axi_arburst          (desc_axi_arburst),
        .m_axi_arlock           (desc_axi_arlock),
        .m_axi_arcache          (desc_axi_arcache),
        .m_axi_arprot           (desc_axi_arprot),
        .m_axi_arqos            (desc_axi_arqos),
        .m_axi_arregion         (desc_axi_arregion),
        .m_axi_aruser           (),  // Unused
        .m_axi_arvalid          (desc_axi_arvalid),
        .m_axi_arready          (desc_axi_arready),
        .m_axi_rid              (desc_axi_rid),
        .m_axi_rdata            (desc_axi_rdata),
        .m_axi_rresp            (desc_axi_rresp),
        .m_axi_rlast            (desc_axi_rlast),
        .m_axi_ruser            (1'b0),  // Input, tie to constant
        .m_axi_rvalid           (desc_axi_rvalid),
        .m_axi_rready           (desc_axi_rready),

        // Monitor Configuration
        .cfg_monitor_enable     (1'b1),
        .cfg_error_enable       (cfg_daxmon_err_enable),
        .cfg_timeout_enable     (cfg_daxmon_timeout_enable),
        .cfg_perf_enable        (cfg_daxmon_perf_enable),
        .cfg_timeout_cycles     (cfg_sched_timeout_cycles),
        .cfg_latency_threshold  (32'hFFFFFFFF),

        // AXI Protocol Filtering Configuration
        .cfg_axi_pkt_mask       (16'h0000),
        .cfg_axi_err_select     (16'h0000),
        .cfg_axi_error_mask     (16'h0000),
        .cfg_axi_timeout_mask   (16'h0000),
        .cfg_axi_compl_mask     (16'h0000),
        .cfg_axi_thresh_mask    (16'h0000),
        .cfg_axi_perf_mask      (16'h0000),
        .cfg_axi_addr_mask      (16'h0000),
        .cfg_axi_debug_mask     (16'h0000),

        // Monitor bus
        .monbus_valid           (desc_axi_mon_valid),
        .monbus_ready           (desc_axi_mon_ready),
        .monbus_packet          (desc_axi_mon_packet),

        // Status outputs
        .busy                   (desc_axi_mon_busy),
        .active_transactions    (desc_axi_mon_active_txns),
        .error_count            (desc_axi_mon_error_count),
        .transaction_count      (desc_axi_mon_txn_count),
        .cfg_conflict_error     (desc_axi_mon_conflict_error)
    );

    // Monitor handles pass-through from desc_axi_int_* (FUB) to desc_axi_* (Master) internally
    // No additional assigns needed - monitor connects both sides

    //=========================================================================
    // Monitor Bus Aggregation
    //=========================================================================

    // Combine channel monitor buses + descriptor AXI monitor
    always_comb begin
        // 8 channel monitors
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            monbus_valid_all[ch] = mon_valid_ch[ch];
            mon_ready_ch[ch] = monbus_ready_all[ch];
            monbus_packet_all[ch] = mon_packet_ch[ch];
        end

        // Descriptor AXI monitor (source 8)
        monbus_valid_all[NUM_CHANNELS] = desc_axi_mon_valid;
        desc_axi_mon_ready = monbus_ready_all[NUM_CHANNELS];
        monbus_packet_all[NUM_CHANNELS] = desc_axi_mon_packet;
    end

    // Aggregate all monitor sources
    monbus_arbiter #(
        .CLIENTS                (MONBUS_SOURCES),
        .INPUT_SKID_ENABLE      (1),
        .OUTPUT_SKID_ENABLE     (1),
        .INPUT_SKID_DEPTH       (2),
        .OUTPUT_SKID_DEPTH      (2)
    ) u_monbus_aggregator (
        .axi_aclk               (clk),
        .axi_aresetn            (rst_n),
        .block_arb              (1'b0),
        .monbus_valid_in        (monbus_valid_all),
        .monbus_ready_in        (monbus_ready_all),
        .monbus_packet_in       (monbus_packet_all),
        .monbus_valid           (mon_valid),
        .monbus_ready           (mon_ready),
        .monbus_packet          (mon_packet),
        .grant_valid            (/* unused */),
        .grant                  (/* unused */),
        .grant_id               (/* unused */),
        .last_grant             (/* unused */)
    );

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Arbitration correctness
    property desc_ar_arbiter_one_hot;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(desc_ar_grant);  // At most one grant
    endproperty
    assert property (desc_ar_arbiter_one_hot);

    property datard_arbiter_one_hot;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(datard_grant);
    endproperty
    assert property (datard_arbiter_one_hot);

    property datawr_arbiter_one_hot;
        @(posedge clk) disable iff (!rst_n)
        $onehot0(datawr_grant);
    endproperty
    assert property (datawr_arbiter_one_hot);

    // R channel routing
    property desc_r_channel_valid_routing;
        @(posedge clk) disable iff (!rst_n)
        desc_axi_int_rvalid && (desc_r_channel_id < NUM_CHANNELS) |->
            desc_r_valid[desc_r_channel_id];
    endproperty
    assert property (desc_r_channel_valid_routing);

    // Completion strobe routing
    property datard_completion_routing;
        @(posedge clk) disable iff (!rst_n)
        datard_done_strobe && (datard_done_channel_id < NUM_CHANNELS) |->
            datard_done_strobe_ch[datard_done_channel_id];
    endproperty
    assert property (datard_completion_routing);

    property datawr_completion_routing;
        @(posedge clk) disable iff (!rst_n)
        datawr_done_strobe && (datawr_done_channel_id < NUM_CHANNELS) |->
            datawr_done_strobe_ch[datawr_done_channel_id];
    endproperty
    assert property (datawr_completion_routing);
    `endif

endmodule : scheduler_group_array
