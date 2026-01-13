//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: beats_scheduler_group_array
        // Purpose: RAPIDS Beats Scheduler Group Array - Multi-channel with shared resources
        //
        // Description:
        //   Top-level array of 8 beats_scheduler_group instances with:
        //   - Shared descriptor AXI master (round-robin arbitration)
        //   - Shared data read interface (to axi_read_engine)
        //   - Shared data write interface (to axi_write_engine)
        //   - Unified MonBus aggregation (9 sources: 8 channels + desc AXI monitor)
        //
        //   Part of RAPIDS Phase 1 "beats" architecture:
        //   - 8 channels (simplified from full RAPIDS)
        //   - No control read/write engines
        //   - No program engine
        //   - No network interfaces (RDA, EOS completion)
        //   - Direct data path interfaces (beats-based, no chunks)
        //
        // Documentation: projects/components/rapids/docs/rapids_spec/
        // Subsystem: rapids_macro_beats
        //
        // Author: sean galloway
        // Created: 2025-01-10
        
        `timescale 1ns / 1ps
        
        // Import RAPIDS and monitor packages
        `include "rapids_imports.svh"
        
        module scheduler_group_array_beats #(
            parameter int NUM_CHANNELS = 8,
            parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
            parameter int ADDR_WIDTH = 64,
            parameter int DATA_WIDTH = 512,
            parameter int AXI_ID_WIDTH = 8,
            // Monitor Bus Base IDs
            parameter int DESC_MON_BASE_AGENT_ID = 16,   // 0x10 - Descriptor Engines (16-23)
            parameter int SCHED_MON_BASE_AGENT_ID = 48,  // 0x30 - Schedulers (48-55)
            parameter int DESC_AXI_MON_AGENT_ID = 8,     // 0x08 - Descriptor AXI Master Monitor
            parameter int MON_UNIT_ID = 1,               // 0x1
            parameter int MON_MAX_TRANSACTIONS = 16
        ) (
            // Clock and Reset
 006844     input  logic                        clk,
 000012     input  logic                        rst_n,
        
            // APB Programming Interface (per channel kick-off)
 000012     input  logic [NUM_CHANNELS-1:0]              apb_valid,
 000020     output logic [NUM_CHANNELS-1:0]              apb_ready,
            input  logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0] apb_addr,
        
            // Configuration Interface (per channel)
 000012     input  logic [NUM_CHANNELS-1:0]              cfg_channel_enable,
%000000     input  logic [NUM_CHANNELS-1:0]              cfg_channel_reset,
        
            // Scheduler Configuration (global - applied to all channels)
 000012     input  logic                                 cfg_sched_enable,          // Master scheduler enable
%000000     input  logic [15:0]                          cfg_sched_timeout_cycles,  // Timeout threshold
 000012     input  logic                                 cfg_sched_timeout_enable,  // Enable timeout detection
 000012     input  logic                                 cfg_sched_err_enable,      // Enable error reporting
 000012     input  logic                                 cfg_sched_compl_enable,    // Enable completion reporting
%000000     input  logic                                 cfg_sched_perf_enable,     // Enable performance monitoring
        
            // Descriptor Engine Configuration (global - applied to all channels)
 000012     input  logic                                 cfg_desceng_enable,        // Master descriptor engine enable
 000012     input  logic                                 cfg_desceng_prefetch,      // Enable descriptor prefetch
%000000     input  logic [3:0]                           cfg_desceng_fifo_thresh,   // FIFO threshold for prefetch
%000000     input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr0_base,    // Address range 0 base
 000012     input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr0_limit,   // Address range 0 limit
%000000     input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr1_base,    // Address range 1 base
 000012     input  logic [ADDR_WIDTH-1:0]                cfg_desceng_addr1_limit,   // Address range 1 limit
        
            // Descriptor AXI Monitor Configuration (expanded with filtering)
 000012     input  logic                                 cfg_desc_mon_enable,
 000012     input  logic                                 cfg_desc_mon_err_enable,
%000000     input  logic                                 cfg_desc_mon_perf_enable,
 000012     input  logic                                 cfg_desc_mon_timeout_enable,
%000000     input  logic [31:0]                          cfg_desc_mon_timeout_cycles,
%000000     input  logic [31:0]                          cfg_desc_mon_latency_thresh,
 000012     input  logic [15:0]                          cfg_desc_mon_pkt_mask,
%000000     input  logic [3:0]                           cfg_desc_mon_err_select,
 000012     input  logic [7:0]                           cfg_desc_mon_err_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_timeout_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_compl_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_thresh_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_perf_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_addr_mask,
 000012     input  logic [7:0]                           cfg_desc_mon_debug_mask,
        
            // Status Interface (per channel)
 000024     output logic [NUM_CHANNELS-1:0]              descriptor_engine_idle,
 000020     output logic [NUM_CHANNELS-1:0]              scheduler_idle,
%000000     output logic [NUM_CHANNELS-1:0][6:0]         scheduler_state,  // ONE-HOT encoding (7 bits)
%000000     output logic [NUM_CHANNELS-1:0]              sched_error,       // Scheduler error (sticky)
        
            // Descriptor AXI Monitor Status
 000220     output logic                                 cfg_sts_desc_mon_busy,
%000000     output logic [7:0]                           cfg_sts_desc_mon_active_txns,
%000000     output logic [15:0]                          cfg_sts_desc_mon_error_count,
%000000     output logic [31:0]                          cfg_sts_desc_mon_txn_count,
%000000     output logic                                 cfg_sts_desc_mon_conflict_error,
        
            // Shared Descriptor AXI4 Master Read Interface (256-bit descriptor fetch)
 000112     output logic                        desc_axi_arvalid,
 000132     input  logic                        desc_axi_arready,
%000000     output logic [ADDR_WIDTH-1:0]       desc_axi_araddr,
%000000     output logic [7:0]                  desc_axi_arlen,
%000000     output logic [2:0]                  desc_axi_arsize,
%000000     output logic [1:0]                  desc_axi_arburst,
%000000     output logic [AXI_ID_WIDTH-1:0]     desc_axi_arid,
%000000     output logic                        desc_axi_arlock,
%000000     output logic [3:0]                  desc_axi_arcache,
%000000     output logic [2:0]                  desc_axi_arprot,
%000000     output logic [3:0]                  desc_axi_arqos,
%000000     output logic [3:0]                  desc_axi_arregion,
        
            // Descriptor AXI Read Data Channel (FIXED 256-bit for descriptor size)
 000132     input  logic                        desc_axi_rvalid,
 000012     output logic                        desc_axi_rready,
%000000     input  logic [255:0]                desc_axi_rdata,  // FIXED 256-bit descriptor
%000000     input  logic [1:0]                  desc_axi_rresp,
 000012     input  logic                        desc_axi_rlast,
%000000     input  logic [AXI_ID_WIDTH-1:0]     desc_axi_rid,
        
            // Shared Data Read Interface (to AXI Read Engine)
            // Per-channel arrays - direct passthrough to engines
%000008     output logic [NUM_CHANNELS-1:0]                     sched_rd_valid,
            output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     sched_rd_addr,
%000000     output logic [NUM_CHANNELS-1:0][31:0]               sched_rd_beats,
        
            // Shared Data Write Interface (to AXI Write Engine)
            // Per-channel arrays - direct passthrough to engines
%000008     output logic [NUM_CHANNELS-1:0]                     sched_wr_valid,
 000012     input  logic [NUM_CHANNELS-1:0]                     sched_wr_ready,
            output logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     sched_wr_addr,
%000000     output logic [NUM_CHANNELS-1:0][31:0]               sched_wr_beats,
        
            // Data Path Completion Strobes (per-channel from engines)
%000004     input  logic [NUM_CHANNELS-1:0]                     sched_rd_done_strobe,
%000000     input  logic [NUM_CHANNELS-1:0][31:0]               sched_rd_beats_done,
%000004     input  logic [NUM_CHANNELS-1:0]                     sched_wr_done_strobe,
%000000     input  logic [NUM_CHANNELS-1:0][31:0]               sched_wr_beats_done,
        
            // Error Signals (per-channel from AXI engines)
%000000     input  logic [NUM_CHANNELS-1:0]                     sched_rd_error,
%000000     input  logic [NUM_CHANNELS-1:0]                     sched_wr_error,
        
            // Unified Monitor Bus Interface
 000332     output logic                        mon_valid,
 000012     input  logic                        mon_ready,
%000000     output logic [63:0]                 mon_packet
        );
        
            //=========================================================================
            // Internal Signals - Per-Channel Descriptor AXI Interface
            //=========================================================================
        
            // Descriptor AR channel (per channel)
 000012     logic [NUM_CHANNELS-1:0]                     desc_ar_valid;
 000012     logic [NUM_CHANNELS-1:0]                     desc_ar_ready;
            logic [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0]     desc_ar_addr;
%000000     logic [NUM_CHANNELS-1:0][7:0]                desc_ar_len;
%000000     logic [NUM_CHANNELS-1:0][2:0]                desc_ar_size;
%000000     logic [NUM_CHANNELS-1:0][1:0]                desc_ar_burst;
%000000     logic [NUM_CHANNELS-1:0][AXI_ID_WIDTH-1:0]   desc_ar_id;
%000000     logic [NUM_CHANNELS-1:0]                     desc_ar_lock;
%000000     logic [NUM_CHANNELS-1:0][3:0]                desc_ar_cache;
%000000     logic [NUM_CHANNELS-1:0][2:0]                desc_ar_prot;
%000000     logic [NUM_CHANNELS-1:0][3:0]                desc_ar_qos;
%000000     logic [NUM_CHANNELS-1:0][3:0]                desc_ar_region;
        
            // Descriptor R channel (per channel)
            // NOTE: Descriptors are FIXED at 256-bit width (not DATA_WIDTH)
 000012     logic [NUM_CHANNELS-1:0]                     desc_r_valid;
 000012     logic [NUM_CHANNELS-1:0]                     desc_r_ready;
            logic [NUM_CHANNELS-1:0][255:0]              desc_r_data;  // 256-bit descriptors
%000000     logic [NUM_CHANNELS-1:0][1:0]                desc_r_resp;
 000132     logic [NUM_CHANNELS-1:0]                     desc_r_last;
%000000     logic [NUM_CHANNELS-1:0][AXI_ID_WIDTH-1:0]   desc_r_id;
        
            //=========================================================================
            // Internal Signals - Monitor Bus (per channel)
            //=========================================================================
        
 000028     logic [NUM_CHANNELS-1:0]                     mon_valid_ch;
 000012     logic [NUM_CHANNELS-1:0]                     mon_ready_ch;
            logic [NUM_CHANNELS-1:0][63:0]               mon_packet_ch;
        
            //=========================================================================
            // Internal Signals - Descriptor AXI Arbitration
            //=========================================================================
        
 000128     logic                                        desc_ar_grant_valid;
 000012     logic [NUM_CHANNELS-1:0]                     desc_ar_grant;
 000012     logic [NUM_CHANNELS-1:0]                     desc_ar_grant_ack;
 000048     logic [CHAN_WIDTH-1:0]                       desc_ar_grant_id;
        
            // Internal AXI signals (post-arbitration, pre-monitor)
 000128     logic                                        desc_axi_int_arvalid;
 000032     logic                                        desc_axi_int_arready;
%000000     logic [ADDR_WIDTH-1:0]                       desc_axi_int_araddr;
%000000     logic [7:0]                                  desc_axi_int_arlen;
%000000     logic [2:0]                                  desc_axi_int_arsize;
%000000     logic [1:0]                                  desc_axi_int_arburst;
%000000     logic [AXI_ID_WIDTH-1:0]                     desc_axi_int_arid;
%000000     logic                                        desc_axi_int_arlock;
%000000     logic [3:0]                                  desc_axi_int_arcache;
%000000     logic [2:0]                                  desc_axi_int_arprot;
%000000     logic [3:0]                                  desc_axi_int_arqos;
%000000     logic [3:0]                                  desc_axi_int_arregion;
        
 000132     logic                                        desc_axi_int_rvalid;
 000132     logic                                        desc_axi_int_rready;
%000000     logic [255:0]                                desc_axi_int_rdata;  // FIXED 256-bit descriptor
%000000     logic [1:0]                                  desc_axi_int_rresp;
 000132     logic                                        desc_axi_int_rlast;
%000000     logic [AXI_ID_WIDTH-1:0]                     desc_axi_int_rid;
        
            //=========================================================================
            // Internal Signals - Monitor Bus Aggregation
            //=========================================================================
        
            // MonBus from descriptor AXI monitor
%000000     logic                                        desc_axi_mon_valid;
 000012     logic                                        desc_axi_mon_ready;
%000000     logic [63:0]                                 desc_axi_mon_packet;
        
            // Combined MonBus arrays (9 sources: 8 channels + 1 desc AXI monitor)
            localparam int MONBUS_SOURCES = NUM_CHANNELS + 1;
            // Use unpacked arrays to match monbus_arbiter port types
%000000     logic                    monbus_valid_all[MONBUS_SOURCES];
 000012     logic                    monbus_ready_all[MONBUS_SOURCES];
            logic [63:0]             monbus_packet_all[MONBUS_SOURCES];
        
            //=========================================================================
            // Beats Scheduler Group Array Instantiation
            //=========================================================================
        
            generate
                for (genvar ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_scheduler_groups
                    scheduler_group_beats #(
                        .CHANNEL_ID             (ch),
                        .NUM_CHANNELS           (NUM_CHANNELS),
                        .CHAN_WIDTH             (CHAN_WIDTH),
                        .ADDR_WIDTH             (ADDR_WIDTH),
                        .DATA_WIDTH             (DATA_WIDTH),
                        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
                        .DESC_MON_AGENT_ID      (8'(DESC_MON_BASE_AGENT_ID + ch)),
                        .SCHED_MON_AGENT_ID     (8'(SCHED_MON_BASE_AGENT_ID + ch)),
                        .MON_UNIT_ID            (4'(MON_UNIT_ID)),
                        .MON_CHANNEL_ID         (6'(ch))
                    ) u_beats_scheduler_group (
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
                        .sched_error            (sched_error[ch]),
        
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
                        .sched_rd_valid         (sched_rd_valid[ch]),
                        .sched_rd_addr          (sched_rd_addr[ch]),
                        .sched_rd_beats         (sched_rd_beats[ch]),
        
                        // Data write interface (direct passthrough - no arbitration)
                        .sched_wr_valid         (sched_wr_valid[ch]),
                        .sched_wr_ready         (sched_wr_ready[ch]),
                        .sched_wr_addr          (sched_wr_addr[ch]),
                        .sched_wr_beats         (sched_wr_beats[ch]),
        
                        // Completion strobes (direct passthrough)
                        .sched_rd_done_strobe   (sched_rd_done_strobe[ch]),
                        .sched_rd_beats_done    (sched_rd_beats_done[ch]),
                        .sched_wr_done_strobe   (sched_wr_done_strobe[ch]),
                        .sched_wr_beats_done    (sched_wr_beats_done[ch]),
        
                        // Error signals (direct passthrough)
                        .sched_rd_error         (sched_rd_error[ch]),
                        .sched_wr_error         (sched_wr_error[ch]),
        
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
 000012     always_comb begin
 000012         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
 000096             desc_ar_grant_ack[ch] = desc_ar_grant_valid && desc_ar_grant[ch] && desc_ar_valid[ch] && desc_axi_int_arready;
                end
            end
        
            // AR channel ready: granted channel sees internal ready only when grant is valid
 000012     always_comb begin
 000012         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
 000096             desc_ar_ready[ch] = desc_ar_grant_valid && desc_ar_grant[ch] && desc_axi_int_arready;
                end
            end
        
            // AR channel multiplexing: select granted channel
 021072     always_comb begin
 021072         desc_axi_int_arvalid = '0;
 021072         desc_axi_int_araddr = '0;
 021072         desc_axi_int_arlen = '0;
 021072         desc_axi_int_arsize = '0;
 021072         desc_axi_int_arburst = '0;
 021072         desc_axi_int_arid = '0;
 021072         desc_axi_int_arlock = '0;
 021072         desc_axi_int_arcache = '0;
 021072         desc_axi_int_arprot = '0;
 021072         desc_axi_int_arqos = '0;
 021072         desc_axi_int_arregion = '0;
        
 021072         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
 006460             if (desc_ar_grant[ch]) begin
 006460                 desc_axi_int_arvalid = desc_ar_valid[ch];
 006460                 desc_axi_int_araddr = desc_ar_addr[ch];
 006460                 desc_axi_int_arlen = desc_ar_len[ch];
 006460                 desc_axi_int_arsize = desc_ar_size[ch];
 006460                 desc_axi_int_arburst = desc_ar_burst[ch];
                        // Embed channel ID in lower bits of AXI ID for R channel demux
 006460                 desc_axi_int_arid = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, ch[CHAN_WIDTH-1:0]};
 006460                 desc_axi_int_arlock = desc_ar_lock[ch];
 006460                 desc_axi_int_arcache = desc_ar_cache[ch];
 006460                 desc_axi_int_arprot = desc_ar_prot[ch];
 006460                 desc_axi_int_arqos = desc_ar_qos[ch];
 006460                 desc_axi_int_arregion = desc_ar_region[ch];
                    end
                end
            end
        
            //=========================================================================
            // Descriptor AXI R Channel Demultiplexing
            //=========================================================================
        
            // Extract channel ID from lower bits of R channel ID
 000048     logic [CHAN_WIDTH-1:0] desc_r_channel_id;
            assign desc_r_channel_id = desc_axi_int_rid[CHAN_WIDTH-1:0];
        
            // R channel demultiplexing: route based on ID
 021072     always_comb begin
                // Default: no valid to any channel
 021072         desc_r_valid = '0;
 021072         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
 168576             desc_r_data[ch] = desc_axi_int_rdata;
 168576             desc_r_resp[ch] = desc_axi_int_rresp;
 168576             desc_r_last[ch] = desc_axi_int_rlast;
 168576             desc_r_id[ch] = desc_axi_int_rid;
                end
        
                // Route R valid to correct channel based on ID
 000462         if (desc_axi_int_rvalid && desc_r_channel_id < NUM_CHANNELS) begin
 000462             desc_r_valid[desc_r_channel_id] = 1'b1;
                end
            end
        
            // R channel ready: OR of all channel readies (only routed channel should be ready)
            assign desc_axi_int_rready = |desc_r_ready;
        
            //=========================================================================
            // Data Read/Write Interface - Direct Passthrough (NO ARBITRATION)
            //=========================================================================
            // All signals connected directly in beats_scheduler_group instantiations above
            // Engines handle arbitration internally
        
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
                .MAX_TRANSACTIONS       (MON_MAX_TRANSACTIONS),
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
                .cfg_monitor_enable     (cfg_desc_mon_enable),
                .cfg_error_enable       (cfg_desc_mon_err_enable),
                .cfg_perf_enable        (cfg_desc_mon_perf_enable),
                .cfg_timeout_enable     (cfg_desc_mon_timeout_enable),
                .cfg_timeout_cycles     (cfg_desc_mon_timeout_cycles),
                .cfg_latency_threshold  (cfg_desc_mon_latency_thresh),
        
                // AXI Protocol Filtering Configuration
                .cfg_axi_pkt_mask       (cfg_desc_mon_pkt_mask),
                .cfg_axi_err_select     (cfg_desc_mon_err_select),
                .cfg_axi_error_mask     (cfg_desc_mon_err_mask),
                .cfg_axi_timeout_mask   (cfg_desc_mon_timeout_mask),
                .cfg_axi_compl_mask     (cfg_desc_mon_compl_mask),
                .cfg_axi_thresh_mask    (cfg_desc_mon_thresh_mask),
                .cfg_axi_perf_mask      (cfg_desc_mon_perf_mask),
                .cfg_axi_addr_mask      (cfg_desc_mon_addr_mask),
                .cfg_axi_debug_mask     (cfg_desc_mon_debug_mask),
        
                // Monitor bus
                .monbus_valid           (desc_axi_mon_valid),
                .monbus_ready           (desc_axi_mon_ready),
                .monbus_packet          (desc_axi_mon_packet),
        
                // Status outputs
                .busy                   (cfg_sts_desc_mon_busy),
                .active_transactions    (cfg_sts_desc_mon_active_txns),
                .error_count            (cfg_sts_desc_mon_error_count),
                .transaction_count      (cfg_sts_desc_mon_txn_count),
                .cfg_conflict_error     (cfg_sts_desc_mon_conflict_error)
            );
        
            //=========================================================================
            // Monitor Bus Aggregation
            //=========================================================================
        
            // Combine channel monitor buses + descriptor AXI monitor
 000012     always_comb begin
                // 8 channel monitors
 000012         for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
 000096             monbus_valid_all[ch] = mon_valid_ch[ch];
 000096             mon_ready_ch[ch] = monbus_ready_all[ch];
 000096             monbus_packet_all[ch] = mon_packet_ch[ch];
                end
        
                // Descriptor AXI monitor (source 8)
 000012         monbus_valid_all[NUM_CHANNELS] = desc_axi_mon_valid;
 000012         desc_axi_mon_ready = monbus_ready_all[NUM_CHANNELS];
 000012         monbus_packet_all[NUM_CHANNELS] = desc_axi_mon_packet;
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
        
            // R channel routing
            property desc_r_channel_valid_routing;
                @(posedge clk) disable iff (!rst_n)
                desc_axi_int_rvalid && (desc_r_channel_id < NUM_CHANNELS) |->
                    desc_r_valid[desc_r_channel_id];
            endproperty
            assert property (desc_r_channel_valid_routing);
            `endif
        
        endmodule : scheduler_group_array_beats
        
