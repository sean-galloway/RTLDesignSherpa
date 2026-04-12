module stream_config_block (
	clk,
	rst_n,
	reg_global_ctrl_global_en,
	reg_global_ctrl_global_rst,
	reg_channel_enable_ch_en,
	reg_channel_reset_ch_rst,
	reg_sched_timeout_cycles_timeout_cycles,
	reg_sched_config_sched_en,
	reg_sched_config_timeout_en,
	reg_sched_config_err_en,
	reg_sched_config_compl_en,
	reg_sched_config_perf_en,
	reg_desceng_config_desceng_en,
	reg_desceng_config_prefetch_en,
	reg_desceng_config_fifo_thresh,
	reg_desceng_addr0_base_addr0_base,
	reg_desceng_addr0_limit_addr0_limit,
	reg_desceng_addr1_base_addr1_base,
	reg_desceng_addr1_limit_addr1_limit,
	reg_daxmon_enable_mon_en,
	reg_daxmon_enable_err_en,
	reg_daxmon_enable_compl_en,
	reg_daxmon_enable_timeout_en,
	reg_daxmon_enable_perf_en,
	reg_daxmon_timeout_timeout_cycles,
	reg_daxmon_latency_thresh_latency_thresh,
	reg_daxmon_pkt_mask_pkt_mask,
	reg_daxmon_err_cfg_err_select,
	reg_daxmon_err_cfg_err_mask,
	reg_daxmon_mask1_timeout_mask,
	reg_daxmon_mask1_compl_mask,
	reg_daxmon_mask2_thresh_mask,
	reg_daxmon_mask2_perf_mask,
	reg_daxmon_mask3_addr_mask,
	reg_daxmon_mask3_debug_mask,
	reg_rdmon_enable_mon_en,
	reg_rdmon_enable_err_en,
	reg_rdmon_enable_compl_en,
	reg_rdmon_enable_timeout_en,
	reg_rdmon_enable_perf_en,
	reg_rdmon_timeout_timeout_cycles,
	reg_rdmon_latency_thresh_latency_thresh,
	reg_rdmon_pkt_mask_pkt_mask,
	reg_rdmon_err_cfg_err_select,
	reg_rdmon_err_cfg_err_mask,
	reg_rdmon_mask1_timeout_mask,
	reg_rdmon_mask1_compl_mask,
	reg_rdmon_mask2_thresh_mask,
	reg_rdmon_mask2_perf_mask,
	reg_rdmon_mask3_addr_mask,
	reg_rdmon_mask3_debug_mask,
	reg_wrmon_enable_mon_en,
	reg_wrmon_enable_err_en,
	reg_wrmon_enable_compl_en,
	reg_wrmon_enable_timeout_en,
	reg_wrmon_enable_perf_en,
	reg_wrmon_timeout_timeout_cycles,
	reg_wrmon_latency_thresh_latency_thresh,
	reg_wrmon_pkt_mask_pkt_mask,
	reg_wrmon_err_cfg_err_select,
	reg_wrmon_err_cfg_err_mask,
	reg_wrmon_mask1_timeout_mask,
	reg_wrmon_mask1_compl_mask,
	reg_wrmon_mask2_thresh_mask,
	reg_wrmon_mask2_perf_mask,
	reg_wrmon_mask3_addr_mask,
	reg_wrmon_mask3_debug_mask,
	reg_axi_xfer_config_rd_xfer_beats,
	reg_axi_xfer_config_wr_xfer_beats,
	reg_perf_config_perf_en,
	reg_perf_config_perf_mode,
	reg_perf_config_perf_clear,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_enable,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_enable,
	cfg_desceng_prefetch,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	cfg_desc_mon_enable,
	cfg_desc_mon_err_enable,
	cfg_desc_mon_perf_enable,
	cfg_desc_mon_timeout_enable,
	cfg_desc_mon_timeout_cycles,
	cfg_desc_mon_latency_thresh,
	cfg_desc_mon_pkt_mask,
	cfg_desc_mon_err_select,
	cfg_desc_mon_err_mask,
	cfg_desc_mon_timeout_mask,
	cfg_desc_mon_compl_mask,
	cfg_desc_mon_thresh_mask,
	cfg_desc_mon_perf_mask,
	cfg_desc_mon_addr_mask,
	cfg_desc_mon_debug_mask,
	cfg_rdeng_mon_enable,
	cfg_rdeng_mon_err_enable,
	cfg_rdeng_mon_perf_enable,
	cfg_rdeng_mon_timeout_enable,
	cfg_rdeng_mon_timeout_cycles,
	cfg_rdeng_mon_latency_thresh,
	cfg_rdeng_mon_pkt_mask,
	cfg_rdeng_mon_err_select,
	cfg_rdeng_mon_err_mask,
	cfg_rdeng_mon_timeout_mask,
	cfg_rdeng_mon_compl_mask,
	cfg_rdeng_mon_thresh_mask,
	cfg_rdeng_mon_perf_mask,
	cfg_rdeng_mon_addr_mask,
	cfg_rdeng_mon_debug_mask,
	cfg_wreng_mon_enable,
	cfg_wreng_mon_err_enable,
	cfg_wreng_mon_perf_enable,
	cfg_wreng_mon_timeout_enable,
	cfg_wreng_mon_timeout_cycles,
	cfg_wreng_mon_latency_thresh,
	cfg_wreng_mon_pkt_mask,
	cfg_wreng_mon_err_select,
	cfg_wreng_mon_err_mask,
	cfg_wreng_mon_timeout_mask,
	cfg_wreng_mon_compl_mask,
	cfg_wreng_mon_thresh_mask,
	cfg_wreng_mon_perf_mask,
	cfg_wreng_mon_addr_mask,
	cfg_wreng_mon_debug_mask,
	cfg_axi_rd_xfer_beats,
	cfg_axi_wr_xfer_beats,
	cfg_perf_enable,
	cfg_perf_mode,
	cfg_perf_clear
);
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	input wire clk;
	input wire rst_n;
	input wire reg_global_ctrl_global_en;
	input wire reg_global_ctrl_global_rst;
	input wire [7:0] reg_channel_enable_ch_en;
	input wire [7:0] reg_channel_reset_ch_rst;
	input wire [15:0] reg_sched_timeout_cycles_timeout_cycles;
	input wire reg_sched_config_sched_en;
	input wire reg_sched_config_timeout_en;
	input wire reg_sched_config_err_en;
	input wire reg_sched_config_compl_en;
	input wire reg_sched_config_perf_en;
	input wire reg_desceng_config_desceng_en;
	input wire reg_desceng_config_prefetch_en;
	input wire [3:0] reg_desceng_config_fifo_thresh;
	input wire [31:0] reg_desceng_addr0_base_addr0_base;
	input wire [31:0] reg_desceng_addr0_limit_addr0_limit;
	input wire [31:0] reg_desceng_addr1_base_addr1_base;
	input wire [31:0] reg_desceng_addr1_limit_addr1_limit;
	input wire reg_daxmon_enable_mon_en;
	input wire reg_daxmon_enable_err_en;
	input wire reg_daxmon_enable_compl_en;
	input wire reg_daxmon_enable_timeout_en;
	input wire reg_daxmon_enable_perf_en;
	input wire [31:0] reg_daxmon_timeout_timeout_cycles;
	input wire [31:0] reg_daxmon_latency_thresh_latency_thresh;
	input wire [15:0] reg_daxmon_pkt_mask_pkt_mask;
	input wire [3:0] reg_daxmon_err_cfg_err_select;
	input wire [7:0] reg_daxmon_err_cfg_err_mask;
	input wire [7:0] reg_daxmon_mask1_timeout_mask;
	input wire [7:0] reg_daxmon_mask1_compl_mask;
	input wire [7:0] reg_daxmon_mask2_thresh_mask;
	input wire [7:0] reg_daxmon_mask2_perf_mask;
	input wire [7:0] reg_daxmon_mask3_addr_mask;
	input wire [7:0] reg_daxmon_mask3_debug_mask;
	input wire reg_rdmon_enable_mon_en;
	input wire reg_rdmon_enable_err_en;
	input wire reg_rdmon_enable_compl_en;
	input wire reg_rdmon_enable_timeout_en;
	input wire reg_rdmon_enable_perf_en;
	input wire [31:0] reg_rdmon_timeout_timeout_cycles;
	input wire [31:0] reg_rdmon_latency_thresh_latency_thresh;
	input wire [15:0] reg_rdmon_pkt_mask_pkt_mask;
	input wire [3:0] reg_rdmon_err_cfg_err_select;
	input wire [7:0] reg_rdmon_err_cfg_err_mask;
	input wire [7:0] reg_rdmon_mask1_timeout_mask;
	input wire [7:0] reg_rdmon_mask1_compl_mask;
	input wire [7:0] reg_rdmon_mask2_thresh_mask;
	input wire [7:0] reg_rdmon_mask2_perf_mask;
	input wire [7:0] reg_rdmon_mask3_addr_mask;
	input wire [7:0] reg_rdmon_mask3_debug_mask;
	input wire reg_wrmon_enable_mon_en;
	input wire reg_wrmon_enable_err_en;
	input wire reg_wrmon_enable_compl_en;
	input wire reg_wrmon_enable_timeout_en;
	input wire reg_wrmon_enable_perf_en;
	input wire [31:0] reg_wrmon_timeout_timeout_cycles;
	input wire [31:0] reg_wrmon_latency_thresh_latency_thresh;
	input wire [15:0] reg_wrmon_pkt_mask_pkt_mask;
	input wire [3:0] reg_wrmon_err_cfg_err_select;
	input wire [7:0] reg_wrmon_err_cfg_err_mask;
	input wire [7:0] reg_wrmon_mask1_timeout_mask;
	input wire [7:0] reg_wrmon_mask1_compl_mask;
	input wire [7:0] reg_wrmon_mask2_thresh_mask;
	input wire [7:0] reg_wrmon_mask2_perf_mask;
	input wire [7:0] reg_wrmon_mask3_addr_mask;
	input wire [7:0] reg_wrmon_mask3_debug_mask;
	input wire [7:0] reg_axi_xfer_config_rd_xfer_beats;
	input wire [7:0] reg_axi_xfer_config_wr_xfer_beats;
	input wire reg_perf_config_perf_en;
	input wire reg_perf_config_perf_mode;
	input wire reg_perf_config_perf_clear;
	output wire [NUM_CHANNELS - 1:0] cfg_channel_enable;
	output wire [NUM_CHANNELS - 1:0] cfg_channel_reset;
	output wire cfg_sched_enable;
	output wire [15:0] cfg_sched_timeout_cycles;
	output wire cfg_sched_timeout_enable;
	output wire cfg_sched_err_enable;
	output wire cfg_sched_compl_enable;
	output wire cfg_sched_perf_enable;
	output wire cfg_desceng_enable;
	output wire cfg_desceng_prefetch;
	output wire [3:0] cfg_desceng_fifo_thresh;
	output wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_base;
	output wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_limit;
	output wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_base;
	output wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_limit;
	output wire cfg_desc_mon_enable;
	output wire cfg_desc_mon_err_enable;
	output wire cfg_desc_mon_perf_enable;
	output wire cfg_desc_mon_timeout_enable;
	output wire [31:0] cfg_desc_mon_timeout_cycles;
	output wire [31:0] cfg_desc_mon_latency_thresh;
	output wire [15:0] cfg_desc_mon_pkt_mask;
	output wire [3:0] cfg_desc_mon_err_select;
	output wire [7:0] cfg_desc_mon_err_mask;
	output wire [7:0] cfg_desc_mon_timeout_mask;
	output wire [7:0] cfg_desc_mon_compl_mask;
	output wire [7:0] cfg_desc_mon_thresh_mask;
	output wire [7:0] cfg_desc_mon_perf_mask;
	output wire [7:0] cfg_desc_mon_addr_mask;
	output wire [7:0] cfg_desc_mon_debug_mask;
	output wire cfg_rdeng_mon_enable;
	output wire cfg_rdeng_mon_err_enable;
	output wire cfg_rdeng_mon_perf_enable;
	output wire cfg_rdeng_mon_timeout_enable;
	output wire [31:0] cfg_rdeng_mon_timeout_cycles;
	output wire [31:0] cfg_rdeng_mon_latency_thresh;
	output wire [15:0] cfg_rdeng_mon_pkt_mask;
	output wire [3:0] cfg_rdeng_mon_err_select;
	output wire [7:0] cfg_rdeng_mon_err_mask;
	output wire [7:0] cfg_rdeng_mon_timeout_mask;
	output wire [7:0] cfg_rdeng_mon_compl_mask;
	output wire [7:0] cfg_rdeng_mon_thresh_mask;
	output wire [7:0] cfg_rdeng_mon_perf_mask;
	output wire [7:0] cfg_rdeng_mon_addr_mask;
	output wire [7:0] cfg_rdeng_mon_debug_mask;
	output wire cfg_wreng_mon_enable;
	output wire cfg_wreng_mon_err_enable;
	output wire cfg_wreng_mon_perf_enable;
	output wire cfg_wreng_mon_timeout_enable;
	output wire [31:0] cfg_wreng_mon_timeout_cycles;
	output wire [31:0] cfg_wreng_mon_latency_thresh;
	output wire [15:0] cfg_wreng_mon_pkt_mask;
	output wire [3:0] cfg_wreng_mon_err_select;
	output wire [7:0] cfg_wreng_mon_err_mask;
	output wire [7:0] cfg_wreng_mon_timeout_mask;
	output wire [7:0] cfg_wreng_mon_compl_mask;
	output wire [7:0] cfg_wreng_mon_thresh_mask;
	output wire [7:0] cfg_wreng_mon_perf_mask;
	output wire [7:0] cfg_wreng_mon_addr_mask;
	output wire [7:0] cfg_wreng_mon_debug_mask;
	output wire [7:0] cfg_axi_rd_xfer_beats;
	output wire [7:0] cfg_axi_wr_xfer_beats;
	output wire cfg_perf_enable;
	output wire cfg_perf_mode;
	output wire cfg_perf_clear;
	assign cfg_channel_enable = reg_channel_enable_ch_en & {NUM_CHANNELS {reg_global_ctrl_global_en}};
	assign cfg_channel_reset = reg_channel_reset_ch_rst | {NUM_CHANNELS {reg_global_ctrl_global_rst}};
	assign cfg_sched_enable = reg_sched_config_sched_en & reg_global_ctrl_global_en;
	assign cfg_sched_timeout_cycles = reg_sched_timeout_cycles_timeout_cycles;
	assign cfg_sched_timeout_enable = reg_sched_config_timeout_en;
	assign cfg_sched_err_enable = reg_sched_config_err_en;
	assign cfg_sched_compl_enable = reg_sched_config_compl_en;
	assign cfg_sched_perf_enable = reg_sched_config_perf_en;
	assign cfg_desceng_enable = reg_desceng_config_desceng_en & reg_global_ctrl_global_en;
	assign cfg_desceng_prefetch = reg_desceng_config_prefetch_en;
	assign cfg_desceng_fifo_thresh = reg_desceng_config_fifo_thresh;
	assign cfg_desceng_addr0_base = {{ADDR_WIDTH - 32 {1'b0}}, reg_desceng_addr0_base_addr0_base};
	assign cfg_desceng_addr0_limit = {{ADDR_WIDTH - 32 {1'b0}}, reg_desceng_addr0_limit_addr0_limit};
	assign cfg_desceng_addr1_base = {{ADDR_WIDTH - 32 {1'b0}}, reg_desceng_addr1_base_addr1_base};
	assign cfg_desceng_addr1_limit = {{ADDR_WIDTH - 32 {1'b0}}, reg_desceng_addr1_limit_addr1_limit};
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
	assign cfg_axi_rd_xfer_beats = reg_axi_xfer_config_rd_xfer_beats;
	assign cfg_axi_wr_xfer_beats = reg_axi_xfer_config_wr_xfer_beats;
	assign cfg_perf_enable = reg_perf_config_perf_en & reg_global_ctrl_global_en;
	assign cfg_perf_mode = reg_perf_config_perf_mode;
	assign cfg_perf_clear = reg_perf_config_perf_clear;
endmodule
