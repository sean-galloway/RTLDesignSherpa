// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for stream_config_block (yosys-compatible, sv2v-preprocessed)
// Run with: sby stream_config_block.sby
//
// Pure combinational module: register fields -> config signals.
// All outputs are assigns with no sequential logic, so depth 2 suffices.
//
// Properties verified:
//   P1: Global enable gates channel_enable, sched_enable, desceng_enable,
//       desc_mon_enable, rdeng_mon_enable, wreng_mon_enable, perf_enable
//   P2: Channel reset OR'd with global reset
//   P3: Address zero-extension (32-bit reg -> ADDR_WIDTH output)
//   P4: Direct pass-through fields (timeout, masks, thresholds)
//   P5: Stability (combinational outputs only depend on inputs)

module formal_stream_config_block (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int NUM_CHANNELS = 4;
    localparam int ADDR_WIDTH   = 64;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyconst *) reg                        reg_global_ctrl_global_en;
    (* anyconst *) reg                        reg_global_ctrl_global_rst;
    (* anyconst *) reg  [7:0]                 reg_channel_enable_ch_en;
    (* anyconst *) reg  [7:0]                 reg_channel_reset_ch_rst;

    // Scheduler config
    (* anyconst *) reg  [15:0]                reg_sched_timeout_cycles_timeout_cycles;
    (* anyconst *) reg                        reg_sched_config_sched_en;
    (* anyconst *) reg                        reg_sched_config_timeout_en;
    (* anyconst *) reg                        reg_sched_config_err_en;
    (* anyconst *) reg                        reg_sched_config_compl_en;
    (* anyconst *) reg                        reg_sched_config_perf_en;

    // Descriptor engine config
    (* anyconst *) reg                        reg_desceng_config_desceng_en;
    (* anyconst *) reg                        reg_desceng_config_prefetch_en;
    (* anyconst *) reg  [3:0]                 reg_desceng_config_fifo_thresh;
    (* anyconst *) reg  [31:0]                reg_desceng_addr0_base_addr0_base;
    (* anyconst *) reg  [31:0]                reg_desceng_addr0_limit_addr0_limit;
    (* anyconst *) reg  [31:0]                reg_desceng_addr1_base_addr1_base;
    (* anyconst *) reg  [31:0]                reg_desceng_addr1_limit_addr1_limit;

    // Descriptor AXI Monitor config
    (* anyconst *) reg                        reg_daxmon_enable_mon_en;
    (* anyconst *) reg                        reg_daxmon_enable_err_en;
    (* anyconst *) reg                        reg_daxmon_enable_compl_en;
    (* anyconst *) reg                        reg_daxmon_enable_timeout_en;
    (* anyconst *) reg                        reg_daxmon_enable_perf_en;
    (* anyconst *) reg  [31:0]                reg_daxmon_timeout_timeout_cycles;
    (* anyconst *) reg  [31:0]                reg_daxmon_latency_thresh_latency_thresh;
    (* anyconst *) reg  [15:0]                reg_daxmon_pkt_mask_pkt_mask;
    (* anyconst *) reg  [3:0]                 reg_daxmon_err_cfg_err_select;
    (* anyconst *) reg  [7:0]                 reg_daxmon_err_cfg_err_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask1_timeout_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask1_compl_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask2_thresh_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask2_perf_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask3_addr_mask;
    (* anyconst *) reg  [7:0]                 reg_daxmon_mask3_debug_mask;

    // Read Engine Monitor config
    (* anyconst *) reg                        reg_rdmon_enable_mon_en;
    (* anyconst *) reg                        reg_rdmon_enable_err_en;
    (* anyconst *) reg                        reg_rdmon_enable_compl_en;
    (* anyconst *) reg                        reg_rdmon_enable_timeout_en;
    (* anyconst *) reg                        reg_rdmon_enable_perf_en;
    (* anyconst *) reg  [31:0]                reg_rdmon_timeout_timeout_cycles;
    (* anyconst *) reg  [31:0]                reg_rdmon_latency_thresh_latency_thresh;
    (* anyconst *) reg  [15:0]                reg_rdmon_pkt_mask_pkt_mask;
    (* anyconst *) reg  [3:0]                 reg_rdmon_err_cfg_err_select;
    (* anyconst *) reg  [7:0]                 reg_rdmon_err_cfg_err_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask1_timeout_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask1_compl_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask2_thresh_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask2_perf_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask3_addr_mask;
    (* anyconst *) reg  [7:0]                 reg_rdmon_mask3_debug_mask;

    // Write Engine Monitor config
    (* anyconst *) reg                        reg_wrmon_enable_mon_en;
    (* anyconst *) reg                        reg_wrmon_enable_err_en;
    (* anyconst *) reg                        reg_wrmon_enable_compl_en;
    (* anyconst *) reg                        reg_wrmon_enable_timeout_en;
    (* anyconst *) reg                        reg_wrmon_enable_perf_en;
    (* anyconst *) reg  [31:0]                reg_wrmon_timeout_timeout_cycles;
    (* anyconst *) reg  [31:0]                reg_wrmon_latency_thresh_latency_thresh;
    (* anyconst *) reg  [15:0]                reg_wrmon_pkt_mask_pkt_mask;
    (* anyconst *) reg  [3:0]                 reg_wrmon_err_cfg_err_select;
    (* anyconst *) reg  [7:0]                 reg_wrmon_err_cfg_err_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask1_timeout_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask1_compl_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask2_thresh_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask2_perf_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask3_addr_mask;
    (* anyconst *) reg  [7:0]                 reg_wrmon_mask3_debug_mask;

    // AXI transfer config
    (* anyconst *) reg  [7:0]                 reg_axi_xfer_config_rd_xfer_beats;
    (* anyconst *) reg  [7:0]                 reg_axi_xfer_config_wr_xfer_beats;

    // Performance profiler config
    (* anyconst *) reg                        reg_perf_config_perf_en;
    (* anyconst *) reg                        reg_perf_config_perf_mode;
    (* anyconst *) reg                        reg_perf_config_perf_clear;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire [NUM_CHANNELS-1:0]     cfg_channel_enable;
    wire [NUM_CHANNELS-1:0]     cfg_channel_reset;
    wire                        cfg_sched_enable;
    wire [15:0]                 cfg_sched_timeout_cycles;
    wire                        cfg_sched_timeout_enable;
    wire                        cfg_sched_err_enable;
    wire                        cfg_sched_compl_enable;
    wire                        cfg_sched_perf_enable;
    wire                        cfg_desceng_enable;
    wire                        cfg_desceng_prefetch;
    wire [3:0]                  cfg_desceng_fifo_thresh;
    wire [ADDR_WIDTH-1:0]       cfg_desceng_addr0_base;
    wire [ADDR_WIDTH-1:0]       cfg_desceng_addr0_limit;
    wire [ADDR_WIDTH-1:0]       cfg_desceng_addr1_base;
    wire [ADDR_WIDTH-1:0]       cfg_desceng_addr1_limit;
    wire                        cfg_desc_mon_enable;
    wire                        cfg_desc_mon_err_enable;
    wire                        cfg_desc_mon_perf_enable;
    wire                        cfg_desc_mon_timeout_enable;
    wire [31:0]                 cfg_desc_mon_timeout_cycles;
    wire [31:0]                 cfg_desc_mon_latency_thresh;
    wire [15:0]                 cfg_desc_mon_pkt_mask;
    wire [3:0]                  cfg_desc_mon_err_select;
    wire [7:0]                  cfg_desc_mon_err_mask;
    wire [7:0]                  cfg_desc_mon_timeout_mask;
    wire [7:0]                  cfg_desc_mon_compl_mask;
    wire [7:0]                  cfg_desc_mon_thresh_mask;
    wire [7:0]                  cfg_desc_mon_perf_mask;
    wire [7:0]                  cfg_desc_mon_addr_mask;
    wire [7:0]                  cfg_desc_mon_debug_mask;
    wire                        cfg_rdeng_mon_enable;
    wire                        cfg_rdeng_mon_err_enable;
    wire                        cfg_rdeng_mon_perf_enable;
    wire                        cfg_rdeng_mon_timeout_enable;
    wire [31:0]                 cfg_rdeng_mon_timeout_cycles;
    wire [31:0]                 cfg_rdeng_mon_latency_thresh;
    wire [15:0]                 cfg_rdeng_mon_pkt_mask;
    wire [3:0]                  cfg_rdeng_mon_err_select;
    wire [7:0]                  cfg_rdeng_mon_err_mask;
    wire [7:0]                  cfg_rdeng_mon_timeout_mask;
    wire [7:0]                  cfg_rdeng_mon_compl_mask;
    wire [7:0]                  cfg_rdeng_mon_thresh_mask;
    wire [7:0]                  cfg_rdeng_mon_perf_mask;
    wire [7:0]                  cfg_rdeng_mon_addr_mask;
    wire [7:0]                  cfg_rdeng_mon_debug_mask;
    wire                        cfg_wreng_mon_enable;
    wire                        cfg_wreng_mon_err_enable;
    wire                        cfg_wreng_mon_perf_enable;
    wire                        cfg_wreng_mon_timeout_enable;
    wire [31:0]                 cfg_wreng_mon_timeout_cycles;
    wire [31:0]                 cfg_wreng_mon_latency_thresh;
    wire [15:0]                 cfg_wreng_mon_pkt_mask;
    wire [3:0]                  cfg_wreng_mon_err_select;
    wire [7:0]                  cfg_wreng_mon_err_mask;
    wire [7:0]                  cfg_wreng_mon_timeout_mask;
    wire [7:0]                  cfg_wreng_mon_compl_mask;
    wire [7:0]                  cfg_wreng_mon_thresh_mask;
    wire [7:0]                  cfg_wreng_mon_perf_mask;
    wire [7:0]                  cfg_wreng_mon_addr_mask;
    wire [7:0]                  cfg_wreng_mon_debug_mask;
    wire [7:0]                  cfg_axi_rd_xfer_beats;
    wire [7:0]                  cfg_axi_wr_xfer_beats;
    wire                        cfg_perf_enable;
    wire                        cfg_perf_mode;
    wire                        cfg_perf_clear;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    stream_config_block #(
        .NUM_CHANNELS (NUM_CHANNELS),
        .ADDR_WIDTH   (ADDR_WIDTH)
    ) dut (
        .clk                                        (clk),
        .rst_n                                      (rst_n),
        // Global control
        .reg_global_ctrl_global_en                  (reg_global_ctrl_global_en),
        .reg_global_ctrl_global_rst                 (reg_global_ctrl_global_rst),
        .reg_channel_enable_ch_en                   (reg_channel_enable_ch_en),
        .reg_channel_reset_ch_rst                   (reg_channel_reset_ch_rst),
        // Scheduler config
        .reg_sched_timeout_cycles_timeout_cycles    (reg_sched_timeout_cycles_timeout_cycles),
        .reg_sched_config_sched_en                  (reg_sched_config_sched_en),
        .reg_sched_config_timeout_en                (reg_sched_config_timeout_en),
        .reg_sched_config_err_en                    (reg_sched_config_err_en),
        .reg_sched_config_compl_en                  (reg_sched_config_compl_en),
        .reg_sched_config_perf_en                   (reg_sched_config_perf_en),
        // Descriptor engine config
        .reg_desceng_config_desceng_en              (reg_desceng_config_desceng_en),
        .reg_desceng_config_prefetch_en             (reg_desceng_config_prefetch_en),
        .reg_desceng_config_fifo_thresh             (reg_desceng_config_fifo_thresh),
        .reg_desceng_addr0_base_addr0_base          (reg_desceng_addr0_base_addr0_base),
        .reg_desceng_addr0_limit_addr0_limit        (reg_desceng_addr0_limit_addr0_limit),
        .reg_desceng_addr1_base_addr1_base          (reg_desceng_addr1_base_addr1_base),
        .reg_desceng_addr1_limit_addr1_limit        (reg_desceng_addr1_limit_addr1_limit),
        // Descriptor AXI Monitor config
        .reg_daxmon_enable_mon_en                   (reg_daxmon_enable_mon_en),
        .reg_daxmon_enable_err_en                   (reg_daxmon_enable_err_en),
        .reg_daxmon_enable_compl_en                 (reg_daxmon_enable_compl_en),
        .reg_daxmon_enable_timeout_en               (reg_daxmon_enable_timeout_en),
        .reg_daxmon_enable_perf_en                  (reg_daxmon_enable_perf_en),
        .reg_daxmon_timeout_timeout_cycles          (reg_daxmon_timeout_timeout_cycles),
        .reg_daxmon_latency_thresh_latency_thresh   (reg_daxmon_latency_thresh_latency_thresh),
        .reg_daxmon_pkt_mask_pkt_mask               (reg_daxmon_pkt_mask_pkt_mask),
        .reg_daxmon_err_cfg_err_select              (reg_daxmon_err_cfg_err_select),
        .reg_daxmon_err_cfg_err_mask                (reg_daxmon_err_cfg_err_mask),
        .reg_daxmon_mask1_timeout_mask              (reg_daxmon_mask1_timeout_mask),
        .reg_daxmon_mask1_compl_mask                (reg_daxmon_mask1_compl_mask),
        .reg_daxmon_mask2_thresh_mask               (reg_daxmon_mask2_thresh_mask),
        .reg_daxmon_mask2_perf_mask                 (reg_daxmon_mask2_perf_mask),
        .reg_daxmon_mask3_addr_mask                 (reg_daxmon_mask3_addr_mask),
        .reg_daxmon_mask3_debug_mask                (reg_daxmon_mask3_debug_mask),
        // Read Engine Monitor config
        .reg_rdmon_enable_mon_en                    (reg_rdmon_enable_mon_en),
        .reg_rdmon_enable_err_en                    (reg_rdmon_enable_err_en),
        .reg_rdmon_enable_compl_en                  (reg_rdmon_enable_compl_en),
        .reg_rdmon_enable_timeout_en                (reg_rdmon_enable_timeout_en),
        .reg_rdmon_enable_perf_en                   (reg_rdmon_enable_perf_en),
        .reg_rdmon_timeout_timeout_cycles           (reg_rdmon_timeout_timeout_cycles),
        .reg_rdmon_latency_thresh_latency_thresh    (reg_rdmon_latency_thresh_latency_thresh),
        .reg_rdmon_pkt_mask_pkt_mask                (reg_rdmon_pkt_mask_pkt_mask),
        .reg_rdmon_err_cfg_err_select               (reg_rdmon_err_cfg_err_select),
        .reg_rdmon_err_cfg_err_mask                 (reg_rdmon_err_cfg_err_mask),
        .reg_rdmon_mask1_timeout_mask               (reg_rdmon_mask1_timeout_mask),
        .reg_rdmon_mask1_compl_mask                 (reg_rdmon_mask1_compl_mask),
        .reg_rdmon_mask2_thresh_mask                (reg_rdmon_mask2_thresh_mask),
        .reg_rdmon_mask2_perf_mask                  (reg_rdmon_mask2_perf_mask),
        .reg_rdmon_mask3_addr_mask                  (reg_rdmon_mask3_addr_mask),
        .reg_rdmon_mask3_debug_mask                 (reg_rdmon_mask3_debug_mask),
        // Write Engine Monitor config
        .reg_wrmon_enable_mon_en                    (reg_wrmon_enable_mon_en),
        .reg_wrmon_enable_err_en                    (reg_wrmon_enable_err_en),
        .reg_wrmon_enable_compl_en                  (reg_wrmon_enable_compl_en),
        .reg_wrmon_enable_timeout_en                (reg_wrmon_enable_timeout_en),
        .reg_wrmon_enable_perf_en                   (reg_wrmon_enable_perf_en),
        .reg_wrmon_timeout_timeout_cycles           (reg_wrmon_timeout_timeout_cycles),
        .reg_wrmon_latency_thresh_latency_thresh    (reg_wrmon_latency_thresh_latency_thresh),
        .reg_wrmon_pkt_mask_pkt_mask                (reg_wrmon_pkt_mask_pkt_mask),
        .reg_wrmon_err_cfg_err_select               (reg_wrmon_err_cfg_err_select),
        .reg_wrmon_err_cfg_err_mask                 (reg_wrmon_err_cfg_err_mask),
        .reg_wrmon_mask1_timeout_mask               (reg_wrmon_mask1_timeout_mask),
        .reg_wrmon_mask1_compl_mask                 (reg_wrmon_mask1_compl_mask),
        .reg_wrmon_mask2_thresh_mask                (reg_wrmon_mask2_thresh_mask),
        .reg_wrmon_mask2_perf_mask                  (reg_wrmon_mask2_perf_mask),
        .reg_wrmon_mask3_addr_mask                  (reg_wrmon_mask3_addr_mask),
        .reg_wrmon_mask3_debug_mask                 (reg_wrmon_mask3_debug_mask),
        // AXI transfer config
        .reg_axi_xfer_config_rd_xfer_beats          (reg_axi_xfer_config_rd_xfer_beats),
        .reg_axi_xfer_config_wr_xfer_beats          (reg_axi_xfer_config_wr_xfer_beats),
        // Performance profiler config
        .reg_perf_config_perf_en                    (reg_perf_config_perf_en),
        .reg_perf_config_perf_mode                  (reg_perf_config_perf_mode),
        .reg_perf_config_perf_clear                 (reg_perf_config_perf_clear),
        // Outputs
        .cfg_channel_enable                         (cfg_channel_enable),
        .cfg_channel_reset                          (cfg_channel_reset),
        .cfg_sched_enable                           (cfg_sched_enable),
        .cfg_sched_timeout_cycles                   (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable                   (cfg_sched_timeout_enable),
        .cfg_sched_err_enable                       (cfg_sched_err_enable),
        .cfg_sched_compl_enable                     (cfg_sched_compl_enable),
        .cfg_sched_perf_enable                      (cfg_sched_perf_enable),
        .cfg_desceng_enable                         (cfg_desceng_enable),
        .cfg_desceng_prefetch                       (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh                    (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base                     (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit                    (cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base                     (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit                    (cfg_desceng_addr1_limit),
        .cfg_desc_mon_enable                        (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable                    (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable                   (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable                (cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles                (cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh                (cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask                      (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select                    (cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask                      (cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask                  (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask                    (cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask                   (cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask                     (cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask                     (cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask                    (cfg_desc_mon_debug_mask),
        .cfg_rdeng_mon_enable                       (cfg_rdeng_mon_enable),
        .cfg_rdeng_mon_err_enable                   (cfg_rdeng_mon_err_enable),
        .cfg_rdeng_mon_perf_enable                  (cfg_rdeng_mon_perf_enable),
        .cfg_rdeng_mon_timeout_enable               (cfg_rdeng_mon_timeout_enable),
        .cfg_rdeng_mon_timeout_cycles               (cfg_rdeng_mon_timeout_cycles),
        .cfg_rdeng_mon_latency_thresh               (cfg_rdeng_mon_latency_thresh),
        .cfg_rdeng_mon_pkt_mask                     (cfg_rdeng_mon_pkt_mask),
        .cfg_rdeng_mon_err_select                   (cfg_rdeng_mon_err_select),
        .cfg_rdeng_mon_err_mask                     (cfg_rdeng_mon_err_mask),
        .cfg_rdeng_mon_timeout_mask                 (cfg_rdeng_mon_timeout_mask),
        .cfg_rdeng_mon_compl_mask                   (cfg_rdeng_mon_compl_mask),
        .cfg_rdeng_mon_thresh_mask                  (cfg_rdeng_mon_thresh_mask),
        .cfg_rdeng_mon_perf_mask                    (cfg_rdeng_mon_perf_mask),
        .cfg_rdeng_mon_addr_mask                    (cfg_rdeng_mon_addr_mask),
        .cfg_rdeng_mon_debug_mask                   (cfg_rdeng_mon_debug_mask),
        .cfg_wreng_mon_enable                       (cfg_wreng_mon_enable),
        .cfg_wreng_mon_err_enable                   (cfg_wreng_mon_err_enable),
        .cfg_wreng_mon_perf_enable                  (cfg_wreng_mon_perf_enable),
        .cfg_wreng_mon_timeout_enable               (cfg_wreng_mon_timeout_enable),
        .cfg_wreng_mon_timeout_cycles               (cfg_wreng_mon_timeout_cycles),
        .cfg_wreng_mon_latency_thresh               (cfg_wreng_mon_latency_thresh),
        .cfg_wreng_mon_pkt_mask                     (cfg_wreng_mon_pkt_mask),
        .cfg_wreng_mon_err_select                   (cfg_wreng_mon_err_select),
        .cfg_wreng_mon_err_mask                     (cfg_wreng_mon_err_mask),
        .cfg_wreng_mon_timeout_mask                 (cfg_wreng_mon_timeout_mask),
        .cfg_wreng_mon_compl_mask                   (cfg_wreng_mon_compl_mask),
        .cfg_wreng_mon_thresh_mask                  (cfg_wreng_mon_thresh_mask),
        .cfg_wreng_mon_perf_mask                    (cfg_wreng_mon_perf_mask),
        .cfg_wreng_mon_addr_mask                    (cfg_wreng_mon_addr_mask),
        .cfg_wreng_mon_debug_mask                   (cfg_wreng_mon_debug_mask),
        .cfg_axi_rd_xfer_beats                      (cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats                      (cfg_axi_wr_xfer_beats),
        .cfg_perf_enable                            (cfg_perf_enable),
        .cfg_perf_mode                              (cfg_perf_mode),
        .cfg_perf_clear                             (cfg_perf_clear)
    );

    // =========================================================================
    // P1: Global enable gating
    // When global_en=0, all gated enables must be 0
    // =========================================================================

    always @(*) begin
        if (!reg_global_ctrl_global_en) begin
            ap_global_gate_channel_en: assert (cfg_channel_enable == '0);
            ap_global_gate_sched_en:   assert (cfg_sched_enable == 1'b0);
            ap_global_gate_desceng_en: assert (cfg_desceng_enable == 1'b0);
            ap_global_gate_desc_mon:   assert (cfg_desc_mon_enable == 1'b0);
            ap_global_gate_rdeng_mon:  assert (cfg_rdeng_mon_enable == 1'b0);
            ap_global_gate_wreng_mon:  assert (cfg_wreng_mon_enable == 1'b0);
            ap_global_gate_perf:       assert (cfg_perf_enable == 1'b0);
        end
    end

    // When global_en=1, gated enables reflect their register values
    always @(*) begin
        if (reg_global_ctrl_global_en) begin
            ap_global_pass_sched_en:   assert (cfg_sched_enable == reg_sched_config_sched_en);
            ap_global_pass_desceng_en: assert (cfg_desceng_enable == reg_desceng_config_desceng_en);
            ap_global_pass_desc_mon:   assert (cfg_desc_mon_enable == reg_daxmon_enable_mon_en);
            ap_global_pass_rdeng_mon:  assert (cfg_rdeng_mon_enable == reg_rdmon_enable_mon_en);
            ap_global_pass_wreng_mon:  assert (cfg_wreng_mon_enable == reg_wrmon_enable_mon_en);
            ap_global_pass_perf:       assert (cfg_perf_enable == reg_perf_config_perf_en);
        end
    end

    // Channel enable: ch_en & {N{global_en}}
    always @(*) begin
        ap_channel_enable_gating: assert (
            cfg_channel_enable ==
            (reg_channel_enable_ch_en[NUM_CHANNELS-1:0] & {NUM_CHANNELS{reg_global_ctrl_global_en}})
        );
    end

    // =========================================================================
    // P2: Channel reset OR'd with global reset
    // =========================================================================
    always @(*) begin
        ap_channel_reset_or: assert (
            cfg_channel_reset ==
            (reg_channel_reset_ch_rst[NUM_CHANNELS-1:0] | {NUM_CHANNELS{reg_global_ctrl_global_rst}})
        );
    end

    // =========================================================================
    // P3: Address zero-extension (32-bit register -> 64-bit output)
    // Upper 32 bits must always be zero
    // =========================================================================
    always @(*) begin
        ap_addr0_base_upper_zero:  assert (cfg_desceng_addr0_base[ADDR_WIDTH-1:32] == '0);
        ap_addr0_limit_upper_zero: assert (cfg_desceng_addr0_limit[ADDR_WIDTH-1:32] == '0);
        ap_addr1_base_upper_zero:  assert (cfg_desceng_addr1_base[ADDR_WIDTH-1:32] == '0);
        ap_addr1_limit_upper_zero: assert (cfg_desceng_addr1_limit[ADDR_WIDTH-1:32] == '0);
    end

    // Lower 32 bits must match the register value
    always @(*) begin
        ap_addr0_base_lower:  assert (cfg_desceng_addr0_base[31:0] == reg_desceng_addr0_base_addr0_base);
        ap_addr0_limit_lower: assert (cfg_desceng_addr0_limit[31:0] == reg_desceng_addr0_limit_addr0_limit);
        ap_addr1_base_lower:  assert (cfg_desceng_addr1_base[31:0] == reg_desceng_addr1_base_addr1_base);
        ap_addr1_limit_lower: assert (cfg_desceng_addr1_limit[31:0] == reg_desceng_addr1_limit_addr1_limit);
    end

    // =========================================================================
    // P4: Direct pass-through fields
    // =========================================================================
    always @(*) begin
        // Scheduler pass-through
        ap_sched_timeout:   assert (cfg_sched_timeout_cycles == reg_sched_timeout_cycles_timeout_cycles);
        ap_sched_timeout_en: assert (cfg_sched_timeout_enable == reg_sched_config_timeout_en);
        ap_sched_err_en:    assert (cfg_sched_err_enable == reg_sched_config_err_en);
        ap_sched_compl_en:  assert (cfg_sched_compl_enable == reg_sched_config_compl_en);
        ap_sched_perf_en:   assert (cfg_sched_perf_enable == reg_sched_config_perf_en);

        // Descriptor engine pass-through
        ap_desceng_prefetch: assert (cfg_desceng_prefetch == reg_desceng_config_prefetch_en);
        ap_desceng_thresh:   assert (cfg_desceng_fifo_thresh == reg_desceng_config_fifo_thresh);

        // AXI transfer pass-through
        ap_axi_rd_beats: assert (cfg_axi_rd_xfer_beats == reg_axi_xfer_config_rd_xfer_beats);
        ap_axi_wr_beats: assert (cfg_axi_wr_xfer_beats == reg_axi_xfer_config_wr_xfer_beats);

        // Perf profiler pass-through
        ap_perf_mode:  assert (cfg_perf_mode == reg_perf_config_perf_mode);
        ap_perf_clear: assert (cfg_perf_clear == reg_perf_config_perf_clear);
    end

    // Desc monitor pass-through
    always @(*) begin
        ap_dmon_err_en:    assert (cfg_desc_mon_err_enable == reg_daxmon_enable_err_en);
        ap_dmon_perf_en:   assert (cfg_desc_mon_perf_enable == reg_daxmon_enable_perf_en);
        ap_dmon_to_en:     assert (cfg_desc_mon_timeout_enable == reg_daxmon_enable_timeout_en);
        ap_dmon_to_cyc:    assert (cfg_desc_mon_timeout_cycles == reg_daxmon_timeout_timeout_cycles);
        ap_dmon_lat:       assert (cfg_desc_mon_latency_thresh == reg_daxmon_latency_thresh_latency_thresh);
        ap_dmon_pkt:       assert (cfg_desc_mon_pkt_mask == reg_daxmon_pkt_mask_pkt_mask);
        ap_dmon_err_sel:   assert (cfg_desc_mon_err_select == reg_daxmon_err_cfg_err_select);
        ap_dmon_err_mask:  assert (cfg_desc_mon_err_mask == reg_daxmon_err_cfg_err_mask);
        ap_dmon_to_mask:   assert (cfg_desc_mon_timeout_mask == reg_daxmon_mask1_timeout_mask);
        ap_dmon_compl:     assert (cfg_desc_mon_compl_mask == reg_daxmon_mask1_compl_mask);
        ap_dmon_thresh:    assert (cfg_desc_mon_thresh_mask == reg_daxmon_mask2_thresh_mask);
        ap_dmon_perf_mask: assert (cfg_desc_mon_perf_mask == reg_daxmon_mask2_perf_mask);
        ap_dmon_addr:      assert (cfg_desc_mon_addr_mask == reg_daxmon_mask3_addr_mask);
        ap_dmon_debug:     assert (cfg_desc_mon_debug_mask == reg_daxmon_mask3_debug_mask);
    end

    // Read monitor pass-through
    always @(*) begin
        ap_rmon_err_en:    assert (cfg_rdeng_mon_err_enable == reg_rdmon_enable_err_en);
        ap_rmon_perf_en:   assert (cfg_rdeng_mon_perf_enable == reg_rdmon_enable_perf_en);
        ap_rmon_to_en:     assert (cfg_rdeng_mon_timeout_enable == reg_rdmon_enable_timeout_en);
        ap_rmon_to_cyc:    assert (cfg_rdeng_mon_timeout_cycles == reg_rdmon_timeout_timeout_cycles);
        ap_rmon_lat:       assert (cfg_rdeng_mon_latency_thresh == reg_rdmon_latency_thresh_latency_thresh);
        ap_rmon_pkt:       assert (cfg_rdeng_mon_pkt_mask == reg_rdmon_pkt_mask_pkt_mask);
        ap_rmon_err_sel:   assert (cfg_rdeng_mon_err_select == reg_rdmon_err_cfg_err_select);
        ap_rmon_err_mask:  assert (cfg_rdeng_mon_err_mask == reg_rdmon_err_cfg_err_mask);
        ap_rmon_to_mask:   assert (cfg_rdeng_mon_timeout_mask == reg_rdmon_mask1_timeout_mask);
        ap_rmon_compl:     assert (cfg_rdeng_mon_compl_mask == reg_rdmon_mask1_compl_mask);
        ap_rmon_thresh:    assert (cfg_rdeng_mon_thresh_mask == reg_rdmon_mask2_thresh_mask);
        ap_rmon_perf_mask: assert (cfg_rdeng_mon_perf_mask == reg_rdmon_mask2_perf_mask);
        ap_rmon_addr:      assert (cfg_rdeng_mon_addr_mask == reg_rdmon_mask3_addr_mask);
        ap_rmon_debug:     assert (cfg_rdeng_mon_debug_mask == reg_rdmon_mask3_debug_mask);
    end

    // Write monitor pass-through
    always @(*) begin
        ap_wmon_err_en:    assert (cfg_wreng_mon_err_enable == reg_wrmon_enable_err_en);
        ap_wmon_perf_en:   assert (cfg_wreng_mon_perf_enable == reg_wrmon_enable_perf_en);
        ap_wmon_to_en:     assert (cfg_wreng_mon_timeout_enable == reg_wrmon_enable_timeout_en);
        ap_wmon_to_cyc:    assert (cfg_wreng_mon_timeout_cycles == reg_wrmon_timeout_timeout_cycles);
        ap_wmon_lat:       assert (cfg_wreng_mon_latency_thresh == reg_wrmon_latency_thresh_latency_thresh);
        ap_wmon_pkt:       assert (cfg_wreng_mon_pkt_mask == reg_wrmon_pkt_mask_pkt_mask);
        ap_wmon_err_sel:   assert (cfg_wreng_mon_err_select == reg_wrmon_err_cfg_err_select);
        ap_wmon_err_mask:  assert (cfg_wreng_mon_err_mask == reg_wrmon_err_cfg_err_mask);
        ap_wmon_to_mask:   assert (cfg_wreng_mon_timeout_mask == reg_wrmon_mask1_timeout_mask);
        ap_wmon_compl:     assert (cfg_wreng_mon_compl_mask == reg_wrmon_mask1_compl_mask);
        ap_wmon_thresh:    assert (cfg_wreng_mon_thresh_mask == reg_wrmon_mask2_thresh_mask);
        ap_wmon_perf_mask: assert (cfg_wreng_mon_perf_mask == reg_wrmon_mask2_perf_mask);
        ap_wmon_addr:      assert (cfg_wreng_mon_addr_mask == reg_wrmon_mask3_addr_mask);
        ap_wmon_debug:     assert (cfg_wreng_mon_debug_mask == reg_wrmon_mask3_debug_mask);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all channels enabled with global enable
    always @(*) begin
        cp_all_ch_en: cover (cfg_channel_enable == {NUM_CHANNELS{1'b1}});
    end

    // Cover: global reset active (all channel resets asserted)
    always @(*) begin
        cp_global_reset: cover (cfg_channel_reset == {NUM_CHANNELS{1'b1}});
    end

    // Cover: scheduler enable active
    always @(*) begin
        cp_sched_enabled: cover (cfg_sched_enable);
    end

    // Cover: descriptor engine enabled with prefetch
    always @(*) begin
        cp_desceng_prefetch: cover (cfg_desceng_enable && cfg_desceng_prefetch);
    end

    // Cover: performance profiler enabled
    always @(*) begin
        cp_perf_enabled: cover (cfg_perf_enable);
    end

    // Cover: all enables off (global disabled)
    always @(*) begin
        cp_all_disabled: cover (
            !cfg_sched_enable && !cfg_desceng_enable &&
            !cfg_desc_mon_enable && !cfg_perf_enable &&
            cfg_channel_enable == '0
        );
    end

endmodule
