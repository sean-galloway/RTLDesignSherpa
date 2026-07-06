/* Machine-generated using Migen */
module a7ddrphy(
	output [12:0] ddram_a,
	output [2:0] ddram_ba,
	output ddram_ras_n,
	output ddram_cas_n,
	output ddram_we_n,
	output [1:0] ddram_dm,
	inout [15:0] ddram_dq,
	inout [1:0] ddram_dqs_p,
	inout [1:0] ddram_dqs_n,
	output ddram_clk_p,
	output ddram_clk_n,
	output ddram_cke,
	output ddram_odt,
	output ddram_cs_n,
	input sys_clk,
	input sys_rst,
	input sys2x_clk,
	input sys2x_rst,
	input sys4x_clk,
	input sys4x_rst,
	input sys4x_dqs_clk,
	input sys4x_dqs_rst,
	input [12:0] dfi_p0_address,
	input [2:0] dfi_p0_bank,
	input dfi_p0_cas_n,
	input dfi_p0_cs_n,
	input dfi_p0_ras_n,
	input dfi_p0_we_n,
	input dfi_p0_cke,
	input dfi_p0_odt,
	input dfi_p0_reset_n,
	input dfi_p0_act_n,
	input [31:0] dfi_p0_wrdata,
	input dfi_p0_wrdata_en,
	input [3:0] dfi_p0_wrdata_mask,
	input dfi_p0_rddata_en,
	output reg [31:0] dfi_p0_rddata,
	output dfi_p0_rddata_valid,
	input [12:0] dfi_p1_address,
	input [2:0] dfi_p1_bank,
	input dfi_p1_cas_n,
	input dfi_p1_cs_n,
	input dfi_p1_ras_n,
	input dfi_p1_we_n,
	input dfi_p1_cke,
	input dfi_p1_odt,
	input dfi_p1_reset_n,
	input dfi_p1_act_n,
	input [31:0] dfi_p1_wrdata,
	input dfi_p1_wrdata_en,
	input [3:0] dfi_p1_wrdata_mask,
	input dfi_p1_rddata_en,
	output reg [31:0] dfi_p1_rddata,
	output dfi_p1_rddata_valid,
	input [12:0] dfi_p2_address,
	input [2:0] dfi_p2_bank,
	input dfi_p2_cas_n,
	input dfi_p2_cs_n,
	input dfi_p2_ras_n,
	input dfi_p2_we_n,
	input dfi_p2_cke,
	input dfi_p2_odt,
	input dfi_p2_reset_n,
	input dfi_p2_act_n,
	input [31:0] dfi_p2_wrdata,
	input dfi_p2_wrdata_en,
	input [3:0] dfi_p2_wrdata_mask,
	input dfi_p2_rddata_en,
	output reg [31:0] dfi_p2_rddata,
	output dfi_p2_rddata_valid,
	input [12:0] dfi_p3_address,
	input [2:0] dfi_p3_bank,
	input dfi_p3_cas_n,
	input dfi_p3_cs_n,
	input dfi_p3_ras_n,
	input dfi_p3_we_n,
	input dfi_p3_cke,
	input dfi_p3_odt,
	input dfi_p3_reset_n,
	input dfi_p3_act_n,
	input [31:0] dfi_p3_wrdata,
	input dfi_p3_wrdata_en,
	input [3:0] dfi_p3_wrdata_mask,
	input dfi_p3_rddata_en,
	output reg [31:0] dfi_p3_rddata,
	output dfi_p3_rddata_valid,
	input [9:0] adr,
	input we,
	input [31:0] dat_w,
	output reg [31:0] dat_r
);

reg a7ddrphy_rst_storage = 1'd0;
reg a7ddrphy_rst_re = 1'd0;
reg [1:0] a7ddrphy_dly_sel_storage = 2'd0;
reg a7ddrphy_dly_sel_re = 1'd0;
reg [4:0] a7ddrphy_half_sys8x_taps_storage = 5'd21;
reg a7ddrphy_half_sys8x_taps_re = 1'd0;
reg a7ddrphy_wlevel_en_storage = 1'd0;
reg a7ddrphy_wlevel_en_re = 1'd0;
reg a7ddrphy_wlevel_strobe_re;
wire a7ddrphy_wlevel_strobe_r;
reg a7ddrphy_wlevel_strobe_we;
reg a7ddrphy_wlevel_strobe_w = 1'd0;
reg a7ddrphy_rdly_dq_rst_re;
wire a7ddrphy_rdly_dq_rst_r;
reg a7ddrphy_rdly_dq_rst_we;
reg a7ddrphy_rdly_dq_rst_w = 1'd0;
reg a7ddrphy_rdly_dq_inc_re;
wire a7ddrphy_rdly_dq_inc_r;
reg a7ddrphy_rdly_dq_inc_we;
reg a7ddrphy_rdly_dq_inc_w = 1'd0;
reg a7ddrphy_rdly_dq_bitslip_rst_re;
wire a7ddrphy_rdly_dq_bitslip_rst_r;
reg a7ddrphy_rdly_dq_bitslip_rst_we;
reg a7ddrphy_rdly_dq_bitslip_rst_w = 1'd0;
reg a7ddrphy_rdly_dq_bitslip_re;
wire a7ddrphy_rdly_dq_bitslip_r;
reg a7ddrphy_rdly_dq_bitslip_we;
reg a7ddrphy_rdly_dq_bitslip_w = 1'd0;
reg a7ddrphy_wdly_dq_bitslip_rst_re;
wire a7ddrphy_wdly_dq_bitslip_rst_r;
reg a7ddrphy_wdly_dq_bitslip_rst_we;
reg a7ddrphy_wdly_dq_bitslip_rst_w = 1'd0;
reg a7ddrphy_wdly_dq_bitslip_re;
wire a7ddrphy_wdly_dq_bitslip_r;
reg a7ddrphy_wdly_dq_bitslip_we;
reg a7ddrphy_wdly_dq_bitslip_w = 1'd0;
reg [1:0] a7ddrphy_rdphase_storage = 2'd1;
reg a7ddrphy_rdphase_re = 1'd0;
reg [1:0] a7ddrphy_wrphase_storage = 2'd2;
reg a7ddrphy_wrphase_re = 1'd0;
wire a7ddrphy_sd_clk_se_nodelay;
wire [2:0] a7ddrphy_pads_ba;
reg a7ddrphy_dqs_oe;
wire a7ddrphy_dqs_preamble;
wire a7ddrphy_dqs_postamble;
wire a7ddrphy_dqs_oe_delay_tappeddelayline;
reg a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline0 = 1'd0;
reg a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline1 = 1'd0;
reg a7ddrphy_dqspattern0 = 1'd0;
reg a7ddrphy_dqspattern1 = 1'd0;
reg [7:0] a7ddrphy_dqspattern_o0;
reg [7:0] a7ddrphy_dqspattern_o1 = 8'd0;
wire a7ddrphy_dqs_o_no_delay0;
wire a7ddrphy_dqs_t0;
reg [7:0] a7ddrphy_bitslip00;
reg [2:0] a7ddrphy_bitslip0_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip0_r0 = 16'd0;
wire a7ddrphy0;
wire a7ddrphy_dqs_o_no_delay1;
wire a7ddrphy_dqs_t1;
reg [7:0] a7ddrphy_bitslip10;
reg [2:0] a7ddrphy_bitslip1_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip1_r0 = 16'd0;
wire a7ddrphy1;
reg [7:0] a7ddrphy_bitslip01;
reg [2:0] a7ddrphy_bitslip0_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip0_r1 = 16'd0;
reg [7:0] a7ddrphy_bitslip11;
reg [2:0] a7ddrphy_bitslip1_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip1_r1 = 16'd0;
wire a7ddrphy_dq_oe;
wire a7ddrphy_dq_oe_delay_tappeddelayline;
reg a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline0 = 1'd0;
reg a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1 = 1'd0;
wire a7ddrphy_dq_o_nodelay0;
wire a7ddrphy_dq_i_nodelay0;
wire a7ddrphy_dq_i_delayed0;
wire a7ddrphy_dq_t0;
reg [7:0] a7ddrphy_bitslip02;
reg [2:0] a7ddrphy_bitslip0_value2 = 3'd7;
reg [15:0] a7ddrphy_bitslip0_r2 = 16'd0;
wire [7:0] a7ddrphy_bitslip03;
reg [7:0] a7ddrphy_bitslip04;
reg [2:0] a7ddrphy_bitslip0_value3 = 3'd7;
reg [15:0] a7ddrphy_bitslip0_r3 = 16'd0;
wire a7ddrphy_dq_o_nodelay1;
wire a7ddrphy_dq_i_nodelay1;
wire a7ddrphy_dq_i_delayed1;
wire a7ddrphy_dq_t1;
reg [7:0] a7ddrphy_bitslip12;
reg [2:0] a7ddrphy_bitslip1_value2 = 3'd7;
reg [15:0] a7ddrphy_bitslip1_r2 = 16'd0;
wire [7:0] a7ddrphy_bitslip13;
reg [7:0] a7ddrphy_bitslip14;
reg [2:0] a7ddrphy_bitslip1_value3 = 3'd7;
reg [15:0] a7ddrphy_bitslip1_r3 = 16'd0;
wire a7ddrphy_dq_o_nodelay2;
wire a7ddrphy_dq_i_nodelay2;
wire a7ddrphy_dq_i_delayed2;
wire a7ddrphy_dq_t2;
reg [7:0] a7ddrphy_bitslip20;
reg [2:0] a7ddrphy_bitslip2_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip2_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip21;
reg [7:0] a7ddrphy_bitslip22;
reg [2:0] a7ddrphy_bitslip2_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip2_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay3;
wire a7ddrphy_dq_i_nodelay3;
wire a7ddrphy_dq_i_delayed3;
wire a7ddrphy_dq_t3;
reg [7:0] a7ddrphy_bitslip30;
reg [2:0] a7ddrphy_bitslip3_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip3_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip31;
reg [7:0] a7ddrphy_bitslip32;
reg [2:0] a7ddrphy_bitslip3_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip3_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay4;
wire a7ddrphy_dq_i_nodelay4;
wire a7ddrphy_dq_i_delayed4;
wire a7ddrphy_dq_t4;
reg [7:0] a7ddrphy_bitslip40;
reg [2:0] a7ddrphy_bitslip4_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip4_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip41;
reg [7:0] a7ddrphy_bitslip42;
reg [2:0] a7ddrphy_bitslip4_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip4_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay5;
wire a7ddrphy_dq_i_nodelay5;
wire a7ddrphy_dq_i_delayed5;
wire a7ddrphy_dq_t5;
reg [7:0] a7ddrphy_bitslip50;
reg [2:0] a7ddrphy_bitslip5_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip5_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip51;
reg [7:0] a7ddrphy_bitslip52;
reg [2:0] a7ddrphy_bitslip5_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip5_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay6;
wire a7ddrphy_dq_i_nodelay6;
wire a7ddrphy_dq_i_delayed6;
wire a7ddrphy_dq_t6;
reg [7:0] a7ddrphy_bitslip60;
reg [2:0] a7ddrphy_bitslip6_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip6_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip61;
reg [7:0] a7ddrphy_bitslip62;
reg [2:0] a7ddrphy_bitslip6_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip6_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay7;
wire a7ddrphy_dq_i_nodelay7;
wire a7ddrphy_dq_i_delayed7;
wire a7ddrphy_dq_t7;
reg [7:0] a7ddrphy_bitslip70;
reg [2:0] a7ddrphy_bitslip7_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip7_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip71;
reg [7:0] a7ddrphy_bitslip72;
reg [2:0] a7ddrphy_bitslip7_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip7_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay8;
wire a7ddrphy_dq_i_nodelay8;
wire a7ddrphy_dq_i_delayed8;
wire a7ddrphy_dq_t8;
reg [7:0] a7ddrphy_bitslip80;
reg [2:0] a7ddrphy_bitslip8_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip8_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip81;
reg [7:0] a7ddrphy_bitslip82;
reg [2:0] a7ddrphy_bitslip8_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip8_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay9;
wire a7ddrphy_dq_i_nodelay9;
wire a7ddrphy_dq_i_delayed9;
wire a7ddrphy_dq_t9;
reg [7:0] a7ddrphy_bitslip90;
reg [2:0] a7ddrphy_bitslip9_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip9_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip91;
reg [7:0] a7ddrphy_bitslip92;
reg [2:0] a7ddrphy_bitslip9_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip9_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay10;
wire a7ddrphy_dq_i_nodelay10;
wire a7ddrphy_dq_i_delayed10;
wire a7ddrphy_dq_t10;
reg [7:0] a7ddrphy_bitslip100;
reg [2:0] a7ddrphy_bitslip10_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip10_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip101;
reg [7:0] a7ddrphy_bitslip102;
reg [2:0] a7ddrphy_bitslip10_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip10_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay11;
wire a7ddrphy_dq_i_nodelay11;
wire a7ddrphy_dq_i_delayed11;
wire a7ddrphy_dq_t11;
reg [7:0] a7ddrphy_bitslip110;
reg [2:0] a7ddrphy_bitslip11_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip11_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip111;
reg [7:0] a7ddrphy_bitslip112;
reg [2:0] a7ddrphy_bitslip11_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip11_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay12;
wire a7ddrphy_dq_i_nodelay12;
wire a7ddrphy_dq_i_delayed12;
wire a7ddrphy_dq_t12;
reg [7:0] a7ddrphy_bitslip120;
reg [2:0] a7ddrphy_bitslip12_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip12_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip121;
reg [7:0] a7ddrphy_bitslip122;
reg [2:0] a7ddrphy_bitslip12_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip12_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay13;
wire a7ddrphy_dq_i_nodelay13;
wire a7ddrphy_dq_i_delayed13;
wire a7ddrphy_dq_t13;
reg [7:0] a7ddrphy_bitslip130;
reg [2:0] a7ddrphy_bitslip13_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip13_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip131;
reg [7:0] a7ddrphy_bitslip132;
reg [2:0] a7ddrphy_bitslip13_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip13_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay14;
wire a7ddrphy_dq_i_nodelay14;
wire a7ddrphy_dq_i_delayed14;
wire a7ddrphy_dq_t14;
reg [7:0] a7ddrphy_bitslip140;
reg [2:0] a7ddrphy_bitslip14_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip14_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip141;
reg [7:0] a7ddrphy_bitslip142;
reg [2:0] a7ddrphy_bitslip14_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip14_r1 = 16'd0;
wire a7ddrphy_dq_o_nodelay15;
wire a7ddrphy_dq_i_nodelay15;
wire a7ddrphy_dq_i_delayed15;
wire a7ddrphy_dq_t15;
reg [7:0] a7ddrphy_bitslip150;
reg [2:0] a7ddrphy_bitslip15_value0 = 3'd7;
reg [15:0] a7ddrphy_bitslip15_r0 = 16'd0;
wire [7:0] a7ddrphy_bitslip151;
reg [7:0] a7ddrphy_bitslip152;
reg [2:0] a7ddrphy_bitslip15_value1 = 3'd7;
reg [15:0] a7ddrphy_bitslip15_r1 = 16'd0;
reg a7ddrphy_rddata_en_tappeddelayline0 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline1 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline2 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline3 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline4 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline5 = 1'd0;
reg a7ddrphy_rddata_en_tappeddelayline6 = 1'd0;
reg a7ddrphy_wrdata_en_tappeddelayline0 = 1'd0;
reg a7ddrphy_wrdata_en_tappeddelayline1 = 1'd0;
reg re = 1'd0;
reg rst0_re;
wire rst0_r;
reg rst0_we;
wire rst0_w;
reg dly_sel0_re;
wire [1:0] dly_sel0_r;
reg dly_sel0_we;
wire [1:0] dly_sel0_w;
reg half_sys8x_taps0_re;
wire [4:0] half_sys8x_taps0_r;
reg half_sys8x_taps0_we;
wire [4:0] half_sys8x_taps0_w;
reg wlevel_en0_re;
wire wlevel_en0_r;
reg wlevel_en0_we;
wire wlevel_en0_w;
reg rdphase0_re;
wire [1:0] rdphase0_r;
reg rdphase0_we;
wire [1:0] rdphase0_w;
reg wrphase0_re;
wire [1:0] wrphase0_r;
reg wrphase0_we;
wire [1:0] wrphase0_w;
wire sel;

// synthesis translate_off
reg dummy_s;
initial dummy_s <= 1'd0;
// synthesis translate_on

assign ddram_ba = a7ddrphy_pads_ba;
assign a7ddrphy_dqs_oe_delay_tappeddelayline = ((a7ddrphy_dqs_preamble | a7ddrphy_dqs_oe) | a7ddrphy_dqs_postamble);
assign a7ddrphy_dq_oe_delay_tappeddelayline = ((a7ddrphy_dqs_preamble | a7ddrphy_dq_oe) | a7ddrphy_dqs_postamble);

// synthesis translate_off
reg dummy_d;
// synthesis translate_on
always @(*) begin
	dfi_p0_rddata <= 32'd0;
	dfi_p0_rddata[0] <= a7ddrphy_bitslip04[0];
	dfi_p0_rddata[16] <= a7ddrphy_bitslip04[1];
	dfi_p0_rddata[1] <= a7ddrphy_bitslip14[0];
	dfi_p0_rddata[17] <= a7ddrphy_bitslip14[1];
	dfi_p0_rddata[2] <= a7ddrphy_bitslip22[0];
	dfi_p0_rddata[18] <= a7ddrphy_bitslip22[1];
	dfi_p0_rddata[3] <= a7ddrphy_bitslip32[0];
	dfi_p0_rddata[19] <= a7ddrphy_bitslip32[1];
	dfi_p0_rddata[4] <= a7ddrphy_bitslip42[0];
	dfi_p0_rddata[20] <= a7ddrphy_bitslip42[1];
	dfi_p0_rddata[5] <= a7ddrphy_bitslip52[0];
	dfi_p0_rddata[21] <= a7ddrphy_bitslip52[1];
	dfi_p0_rddata[6] <= a7ddrphy_bitslip62[0];
	dfi_p0_rddata[22] <= a7ddrphy_bitslip62[1];
	dfi_p0_rddata[7] <= a7ddrphy_bitslip72[0];
	dfi_p0_rddata[23] <= a7ddrphy_bitslip72[1];
	dfi_p0_rddata[8] <= a7ddrphy_bitslip82[0];
	dfi_p0_rddata[24] <= a7ddrphy_bitslip82[1];
	dfi_p0_rddata[9] <= a7ddrphy_bitslip92[0];
	dfi_p0_rddata[25] <= a7ddrphy_bitslip92[1];
	dfi_p0_rddata[10] <= a7ddrphy_bitslip102[0];
	dfi_p0_rddata[26] <= a7ddrphy_bitslip102[1];
	dfi_p0_rddata[11] <= a7ddrphy_bitslip112[0];
	dfi_p0_rddata[27] <= a7ddrphy_bitslip112[1];
	dfi_p0_rddata[12] <= a7ddrphy_bitslip122[0];
	dfi_p0_rddata[28] <= a7ddrphy_bitslip122[1];
	dfi_p0_rddata[13] <= a7ddrphy_bitslip132[0];
	dfi_p0_rddata[29] <= a7ddrphy_bitslip132[1];
	dfi_p0_rddata[14] <= a7ddrphy_bitslip142[0];
	dfi_p0_rddata[30] <= a7ddrphy_bitslip142[1];
	dfi_p0_rddata[15] <= a7ddrphy_bitslip152[0];
	dfi_p0_rddata[31] <= a7ddrphy_bitslip152[1];
// synthesis translate_off
	dummy_d <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_1;
// synthesis translate_on
always @(*) begin
	dfi_p1_rddata <= 32'd0;
	dfi_p1_rddata[0] <= a7ddrphy_bitslip04[2];
	dfi_p1_rddata[16] <= a7ddrphy_bitslip04[3];
	dfi_p1_rddata[1] <= a7ddrphy_bitslip14[2];
	dfi_p1_rddata[17] <= a7ddrphy_bitslip14[3];
	dfi_p1_rddata[2] <= a7ddrphy_bitslip22[2];
	dfi_p1_rddata[18] <= a7ddrphy_bitslip22[3];
	dfi_p1_rddata[3] <= a7ddrphy_bitslip32[2];
	dfi_p1_rddata[19] <= a7ddrphy_bitslip32[3];
	dfi_p1_rddata[4] <= a7ddrphy_bitslip42[2];
	dfi_p1_rddata[20] <= a7ddrphy_bitslip42[3];
	dfi_p1_rddata[5] <= a7ddrphy_bitslip52[2];
	dfi_p1_rddata[21] <= a7ddrphy_bitslip52[3];
	dfi_p1_rddata[6] <= a7ddrphy_bitslip62[2];
	dfi_p1_rddata[22] <= a7ddrphy_bitslip62[3];
	dfi_p1_rddata[7] <= a7ddrphy_bitslip72[2];
	dfi_p1_rddata[23] <= a7ddrphy_bitslip72[3];
	dfi_p1_rddata[8] <= a7ddrphy_bitslip82[2];
	dfi_p1_rddata[24] <= a7ddrphy_bitslip82[3];
	dfi_p1_rddata[9] <= a7ddrphy_bitslip92[2];
	dfi_p1_rddata[25] <= a7ddrphy_bitslip92[3];
	dfi_p1_rddata[10] <= a7ddrphy_bitslip102[2];
	dfi_p1_rddata[26] <= a7ddrphy_bitslip102[3];
	dfi_p1_rddata[11] <= a7ddrphy_bitslip112[2];
	dfi_p1_rddata[27] <= a7ddrphy_bitslip112[3];
	dfi_p1_rddata[12] <= a7ddrphy_bitslip122[2];
	dfi_p1_rddata[28] <= a7ddrphy_bitslip122[3];
	dfi_p1_rddata[13] <= a7ddrphy_bitslip132[2];
	dfi_p1_rddata[29] <= a7ddrphy_bitslip132[3];
	dfi_p1_rddata[14] <= a7ddrphy_bitslip142[2];
	dfi_p1_rddata[30] <= a7ddrphy_bitslip142[3];
	dfi_p1_rddata[15] <= a7ddrphy_bitslip152[2];
	dfi_p1_rddata[31] <= a7ddrphy_bitslip152[3];
// synthesis translate_off
	dummy_d_1 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_2;
// synthesis translate_on
always @(*) begin
	dfi_p2_rddata <= 32'd0;
	dfi_p2_rddata[0] <= a7ddrphy_bitslip04[4];
	dfi_p2_rddata[16] <= a7ddrphy_bitslip04[5];
	dfi_p2_rddata[1] <= a7ddrphy_bitslip14[4];
	dfi_p2_rddata[17] <= a7ddrphy_bitslip14[5];
	dfi_p2_rddata[2] <= a7ddrphy_bitslip22[4];
	dfi_p2_rddata[18] <= a7ddrphy_bitslip22[5];
	dfi_p2_rddata[3] <= a7ddrphy_bitslip32[4];
	dfi_p2_rddata[19] <= a7ddrphy_bitslip32[5];
	dfi_p2_rddata[4] <= a7ddrphy_bitslip42[4];
	dfi_p2_rddata[20] <= a7ddrphy_bitslip42[5];
	dfi_p2_rddata[5] <= a7ddrphy_bitslip52[4];
	dfi_p2_rddata[21] <= a7ddrphy_bitslip52[5];
	dfi_p2_rddata[6] <= a7ddrphy_bitslip62[4];
	dfi_p2_rddata[22] <= a7ddrphy_bitslip62[5];
	dfi_p2_rddata[7] <= a7ddrphy_bitslip72[4];
	dfi_p2_rddata[23] <= a7ddrphy_bitslip72[5];
	dfi_p2_rddata[8] <= a7ddrphy_bitslip82[4];
	dfi_p2_rddata[24] <= a7ddrphy_bitslip82[5];
	dfi_p2_rddata[9] <= a7ddrphy_bitslip92[4];
	dfi_p2_rddata[25] <= a7ddrphy_bitslip92[5];
	dfi_p2_rddata[10] <= a7ddrphy_bitslip102[4];
	dfi_p2_rddata[26] <= a7ddrphy_bitslip102[5];
	dfi_p2_rddata[11] <= a7ddrphy_bitslip112[4];
	dfi_p2_rddata[27] <= a7ddrphy_bitslip112[5];
	dfi_p2_rddata[12] <= a7ddrphy_bitslip122[4];
	dfi_p2_rddata[28] <= a7ddrphy_bitslip122[5];
	dfi_p2_rddata[13] <= a7ddrphy_bitslip132[4];
	dfi_p2_rddata[29] <= a7ddrphy_bitslip132[5];
	dfi_p2_rddata[14] <= a7ddrphy_bitslip142[4];
	dfi_p2_rddata[30] <= a7ddrphy_bitslip142[5];
	dfi_p2_rddata[15] <= a7ddrphy_bitslip152[4];
	dfi_p2_rddata[31] <= a7ddrphy_bitslip152[5];
// synthesis translate_off
	dummy_d_2 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_3;
// synthesis translate_on
always @(*) begin
	dfi_p3_rddata <= 32'd0;
	dfi_p3_rddata[0] <= a7ddrphy_bitslip04[6];
	dfi_p3_rddata[16] <= a7ddrphy_bitslip04[7];
	dfi_p3_rddata[1] <= a7ddrphy_bitslip14[6];
	dfi_p3_rddata[17] <= a7ddrphy_bitslip14[7];
	dfi_p3_rddata[2] <= a7ddrphy_bitslip22[6];
	dfi_p3_rddata[18] <= a7ddrphy_bitslip22[7];
	dfi_p3_rddata[3] <= a7ddrphy_bitslip32[6];
	dfi_p3_rddata[19] <= a7ddrphy_bitslip32[7];
	dfi_p3_rddata[4] <= a7ddrphy_bitslip42[6];
	dfi_p3_rddata[20] <= a7ddrphy_bitslip42[7];
	dfi_p3_rddata[5] <= a7ddrphy_bitslip52[6];
	dfi_p3_rddata[21] <= a7ddrphy_bitslip52[7];
	dfi_p3_rddata[6] <= a7ddrphy_bitslip62[6];
	dfi_p3_rddata[22] <= a7ddrphy_bitslip62[7];
	dfi_p3_rddata[7] <= a7ddrphy_bitslip72[6];
	dfi_p3_rddata[23] <= a7ddrphy_bitslip72[7];
	dfi_p3_rddata[8] <= a7ddrphy_bitslip82[6];
	dfi_p3_rddata[24] <= a7ddrphy_bitslip82[7];
	dfi_p3_rddata[9] <= a7ddrphy_bitslip92[6];
	dfi_p3_rddata[25] <= a7ddrphy_bitslip92[7];
	dfi_p3_rddata[10] <= a7ddrphy_bitslip102[6];
	dfi_p3_rddata[26] <= a7ddrphy_bitslip102[7];
	dfi_p3_rddata[11] <= a7ddrphy_bitslip112[6];
	dfi_p3_rddata[27] <= a7ddrphy_bitslip112[7];
	dfi_p3_rddata[12] <= a7ddrphy_bitslip122[6];
	dfi_p3_rddata[28] <= a7ddrphy_bitslip122[7];
	dfi_p3_rddata[13] <= a7ddrphy_bitslip132[6];
	dfi_p3_rddata[29] <= a7ddrphy_bitslip132[7];
	dfi_p3_rddata[14] <= a7ddrphy_bitslip142[6];
	dfi_p3_rddata[30] <= a7ddrphy_bitslip142[7];
	dfi_p3_rddata[15] <= a7ddrphy_bitslip152[6];
	dfi_p3_rddata[31] <= a7ddrphy_bitslip152[7];
// synthesis translate_off
	dummy_d_3 <= dummy_s;
// synthesis translate_on
end
assign dfi_p0_rddata_valid = (a7ddrphy_rddata_en_tappeddelayline6 | a7ddrphy_wlevel_en_storage);
assign dfi_p1_rddata_valid = (a7ddrphy_rddata_en_tappeddelayline6 | a7ddrphy_wlevel_en_storage);
assign dfi_p2_rddata_valid = (a7ddrphy_rddata_en_tappeddelayline6 | a7ddrphy_wlevel_en_storage);
assign dfi_p3_rddata_valid = (a7ddrphy_rddata_en_tappeddelayline6 | a7ddrphy_wlevel_en_storage);
assign a7ddrphy_dq_oe = a7ddrphy_wrdata_en_tappeddelayline0;

// synthesis translate_off
reg dummy_d_4;
// synthesis translate_on
always @(*) begin
	a7ddrphy_dqs_oe <= 1'd0;
	if (a7ddrphy_wlevel_en_storage) begin
		a7ddrphy_dqs_oe <= 1'd1;
	end else begin
		a7ddrphy_dqs_oe <= a7ddrphy_dq_oe;
	end
// synthesis translate_off
	dummy_d_4 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_dqs_preamble = (a7ddrphy_wrdata_en_tappeddelayline1 & (~a7ddrphy_wrdata_en_tappeddelayline0));
assign a7ddrphy_dqs_postamble = (a7ddrphy_wrdata_en_tappeddelayline1 & (~a7ddrphy_wrdata_en_tappeddelayline0));

// synthesis translate_off
reg dummy_d_5;
// synthesis translate_on
always @(*) begin
	a7ddrphy_dqspattern_o0 <= 8'd0;
	a7ddrphy_dqspattern_o0 <= 7'd85;
	if (a7ddrphy_dqspattern0) begin
		a7ddrphy_dqspattern_o0 <= 5'd21;
	end
	if (a7ddrphy_dqspattern1) begin
		a7ddrphy_dqspattern_o0 <= 7'd84;
	end
	if (a7ddrphy_wlevel_en_storage) begin
		a7ddrphy_dqspattern_o0 <= 1'd0;
		if (a7ddrphy_wlevel_strobe_re) begin
			a7ddrphy_dqspattern_o0 <= 1'd1;
		end
	end
// synthesis translate_off
	dummy_d_5 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_6;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip00 <= 8'd0;
	case (a7ddrphy_bitslip0_value0)
		1'd0: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip00 <= a7ddrphy_bitslip0_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_6 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_7;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip10 <= 8'd0;
	case (a7ddrphy_bitslip1_value0)
		1'd0: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip10 <= a7ddrphy_bitslip1_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_7 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_8;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip01 <= 8'd0;
	case (a7ddrphy_bitslip0_value1)
		1'd0: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip01 <= a7ddrphy_bitslip0_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_8 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_9;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip11 <= 8'd0;
	case (a7ddrphy_bitslip1_value1)
		1'd0: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip11 <= a7ddrphy_bitslip1_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_9 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_10;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip02 <= 8'd0;
	case (a7ddrphy_bitslip0_value2)
		1'd0: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip02 <= a7ddrphy_bitslip0_r2[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_10 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_11;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip04 <= 8'd0;
	case (a7ddrphy_bitslip0_value3)
		1'd0: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip04 <= a7ddrphy_bitslip0_r3[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_11 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_12;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip12 <= 8'd0;
	case (a7ddrphy_bitslip1_value2)
		1'd0: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip12 <= a7ddrphy_bitslip1_r2[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_12 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_13;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip14 <= 8'd0;
	case (a7ddrphy_bitslip1_value3)
		1'd0: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip14 <= a7ddrphy_bitslip1_r3[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_13 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_14;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip20 <= 8'd0;
	case (a7ddrphy_bitslip2_value0)
		1'd0: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip20 <= a7ddrphy_bitslip2_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_14 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_15;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip22 <= 8'd0;
	case (a7ddrphy_bitslip2_value1)
		1'd0: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip22 <= a7ddrphy_bitslip2_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_15 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_16;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip30 <= 8'd0;
	case (a7ddrphy_bitslip3_value0)
		1'd0: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip30 <= a7ddrphy_bitslip3_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_16 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_17;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip32 <= 8'd0;
	case (a7ddrphy_bitslip3_value1)
		1'd0: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip32 <= a7ddrphy_bitslip3_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_17 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_18;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip40 <= 8'd0;
	case (a7ddrphy_bitslip4_value0)
		1'd0: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip40 <= a7ddrphy_bitslip4_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_18 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_19;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip42 <= 8'd0;
	case (a7ddrphy_bitslip4_value1)
		1'd0: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip42 <= a7ddrphy_bitslip4_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_19 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_20;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip50 <= 8'd0;
	case (a7ddrphy_bitslip5_value0)
		1'd0: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip50 <= a7ddrphy_bitslip5_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_20 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_21;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip52 <= 8'd0;
	case (a7ddrphy_bitslip5_value1)
		1'd0: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip52 <= a7ddrphy_bitslip5_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_21 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_22;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip60 <= 8'd0;
	case (a7ddrphy_bitslip6_value0)
		1'd0: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip60 <= a7ddrphy_bitslip6_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_22 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_23;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip62 <= 8'd0;
	case (a7ddrphy_bitslip6_value1)
		1'd0: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip62 <= a7ddrphy_bitslip6_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_23 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_24;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip70 <= 8'd0;
	case (a7ddrphy_bitslip7_value0)
		1'd0: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip70 <= a7ddrphy_bitslip7_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_24 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_25;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip72 <= 8'd0;
	case (a7ddrphy_bitslip7_value1)
		1'd0: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip72 <= a7ddrphy_bitslip7_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_25 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_26;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip80 <= 8'd0;
	case (a7ddrphy_bitslip8_value0)
		1'd0: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip80 <= a7ddrphy_bitslip8_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_26 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_27;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip82 <= 8'd0;
	case (a7ddrphy_bitslip8_value1)
		1'd0: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip82 <= a7ddrphy_bitslip8_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_27 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_28;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip90 <= 8'd0;
	case (a7ddrphy_bitslip9_value0)
		1'd0: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip90 <= a7ddrphy_bitslip9_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_28 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_29;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip92 <= 8'd0;
	case (a7ddrphy_bitslip9_value1)
		1'd0: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip92 <= a7ddrphy_bitslip9_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_29 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_30;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip100 <= 8'd0;
	case (a7ddrphy_bitslip10_value0)
		1'd0: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip100 <= a7ddrphy_bitslip10_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_30 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_31;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip102 <= 8'd0;
	case (a7ddrphy_bitslip10_value1)
		1'd0: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip102 <= a7ddrphy_bitslip10_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_31 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_32;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip110 <= 8'd0;
	case (a7ddrphy_bitslip11_value0)
		1'd0: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip110 <= a7ddrphy_bitslip11_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_32 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_33;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip112 <= 8'd0;
	case (a7ddrphy_bitslip11_value1)
		1'd0: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip112 <= a7ddrphy_bitslip11_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_33 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_34;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip120 <= 8'd0;
	case (a7ddrphy_bitslip12_value0)
		1'd0: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip120 <= a7ddrphy_bitslip12_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_34 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_35;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip122 <= 8'd0;
	case (a7ddrphy_bitslip12_value1)
		1'd0: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip122 <= a7ddrphy_bitslip12_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_35 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_36;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip130 <= 8'd0;
	case (a7ddrphy_bitslip13_value0)
		1'd0: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip130 <= a7ddrphy_bitslip13_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_36 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_37;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip132 <= 8'd0;
	case (a7ddrphy_bitslip13_value1)
		1'd0: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip132 <= a7ddrphy_bitslip13_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_37 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_38;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip140 <= 8'd0;
	case (a7ddrphy_bitslip14_value0)
		1'd0: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip140 <= a7ddrphy_bitslip14_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_38 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_39;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip142 <= 8'd0;
	case (a7ddrphy_bitslip14_value1)
		1'd0: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip142 <= a7ddrphy_bitslip14_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_39 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_40;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip150 <= 8'd0;
	case (a7ddrphy_bitslip15_value0)
		1'd0: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip150 <= a7ddrphy_bitslip15_r0[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_40 <= dummy_s;
// synthesis translate_on
end

// synthesis translate_off
reg dummy_d_41;
// synthesis translate_on
always @(*) begin
	a7ddrphy_bitslip152 <= 8'd0;
	case (a7ddrphy_bitslip15_value1)
		1'd0: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[8:1];
		end
		1'd1: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[9:2];
		end
		2'd2: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[10:3];
		end
		2'd3: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[11:4];
		end
		3'd4: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[12:5];
		end
		3'd5: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[13:6];
		end
		3'd6: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[14:7];
		end
		3'd7: begin
			a7ddrphy_bitslip152 <= a7ddrphy_bitslip15_r1[15:8];
		end
	endcase
// synthesis translate_off
	dummy_d_41 <= dummy_s;
// synthesis translate_on
end
assign sel = (adr[9] == 1'd0);
assign rst0_r = dat_w[0];

// synthesis translate_off
reg dummy_d_42;
// synthesis translate_on
always @(*) begin
	rst0_re <= 1'd0;
	rst0_we <= 1'd0;
	if ((sel & (adr[8:0] == 1'd0))) begin
		rst0_re <= we;
		rst0_we <= re;
	end
// synthesis translate_off
	dummy_d_42 <= dummy_s;
// synthesis translate_on
end
assign dly_sel0_r = dat_w[1:0];

// synthesis translate_off
reg dummy_d_43;
// synthesis translate_on
always @(*) begin
	dly_sel0_re <= 1'd0;
	dly_sel0_we <= 1'd0;
	if ((sel & (adr[8:0] == 1'd1))) begin
		dly_sel0_re <= we;
		dly_sel0_we <= re;
	end
// synthesis translate_off
	dummy_d_43 <= dummy_s;
// synthesis translate_on
end
assign half_sys8x_taps0_r = dat_w[4:0];

// synthesis translate_off
reg dummy_d_44;
// synthesis translate_on
always @(*) begin
	half_sys8x_taps0_re <= 1'd0;
	half_sys8x_taps0_we <= 1'd0;
	if ((sel & (adr[8:0] == 2'd2))) begin
		half_sys8x_taps0_re <= we;
		half_sys8x_taps0_we <= re;
	end
// synthesis translate_off
	dummy_d_44 <= dummy_s;
// synthesis translate_on
end
assign wlevel_en0_r = dat_w[0];

// synthesis translate_off
reg dummy_d_45;
// synthesis translate_on
always @(*) begin
	wlevel_en0_re <= 1'd0;
	wlevel_en0_we <= 1'd0;
	if ((sel & (adr[8:0] == 2'd3))) begin
		wlevel_en0_re <= we;
		wlevel_en0_we <= re;
	end
// synthesis translate_off
	dummy_d_45 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_wlevel_strobe_r = dat_w[0];

// synthesis translate_off
reg dummy_d_46;
// synthesis translate_on
always @(*) begin
	a7ddrphy_wlevel_strobe_re <= 1'd0;
	a7ddrphy_wlevel_strobe_we <= 1'd0;
	if ((sel & (adr[8:0] == 3'd4))) begin
		a7ddrphy_wlevel_strobe_re <= we;
		a7ddrphy_wlevel_strobe_we <= re;
	end
// synthesis translate_off
	dummy_d_46 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_rdly_dq_rst_r = dat_w[0];

// synthesis translate_off
reg dummy_d_47;
// synthesis translate_on
always @(*) begin
	a7ddrphy_rdly_dq_rst_re <= 1'd0;
	a7ddrphy_rdly_dq_rst_we <= 1'd0;
	if ((sel & (adr[8:0] == 3'd5))) begin
		a7ddrphy_rdly_dq_rst_re <= we;
		a7ddrphy_rdly_dq_rst_we <= re;
	end
// synthesis translate_off
	dummy_d_47 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_rdly_dq_inc_r = dat_w[0];

// synthesis translate_off
reg dummy_d_48;
// synthesis translate_on
always @(*) begin
	a7ddrphy_rdly_dq_inc_re <= 1'd0;
	a7ddrphy_rdly_dq_inc_we <= 1'd0;
	if ((sel & (adr[8:0] == 3'd6))) begin
		a7ddrphy_rdly_dq_inc_re <= we;
		a7ddrphy_rdly_dq_inc_we <= re;
	end
// synthesis translate_off
	dummy_d_48 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_rdly_dq_bitslip_rst_r = dat_w[0];

// synthesis translate_off
reg dummy_d_49;
// synthesis translate_on
always @(*) begin
	a7ddrphy_rdly_dq_bitslip_rst_re <= 1'd0;
	a7ddrphy_rdly_dq_bitslip_rst_we <= 1'd0;
	if ((sel & (adr[8:0] == 3'd7))) begin
		a7ddrphy_rdly_dq_bitslip_rst_re <= we;
		a7ddrphy_rdly_dq_bitslip_rst_we <= re;
	end
// synthesis translate_off
	dummy_d_49 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_rdly_dq_bitslip_r = dat_w[0];

// synthesis translate_off
reg dummy_d_50;
// synthesis translate_on
always @(*) begin
	a7ddrphy_rdly_dq_bitslip_re <= 1'd0;
	a7ddrphy_rdly_dq_bitslip_we <= 1'd0;
	if ((sel & (adr[8:0] == 4'd8))) begin
		a7ddrphy_rdly_dq_bitslip_re <= we;
		a7ddrphy_rdly_dq_bitslip_we <= re;
	end
// synthesis translate_off
	dummy_d_50 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_wdly_dq_bitslip_rst_r = dat_w[0];

// synthesis translate_off
reg dummy_d_51;
// synthesis translate_on
always @(*) begin
	a7ddrphy_wdly_dq_bitslip_rst_re <= 1'd0;
	a7ddrphy_wdly_dq_bitslip_rst_we <= 1'd0;
	if ((sel & (adr[8:0] == 4'd9))) begin
		a7ddrphy_wdly_dq_bitslip_rst_re <= we;
		a7ddrphy_wdly_dq_bitslip_rst_we <= re;
	end
// synthesis translate_off
	dummy_d_51 <= dummy_s;
// synthesis translate_on
end
assign a7ddrphy_wdly_dq_bitslip_r = dat_w[0];

// synthesis translate_off
reg dummy_d_52;
// synthesis translate_on
always @(*) begin
	a7ddrphy_wdly_dq_bitslip_re <= 1'd0;
	a7ddrphy_wdly_dq_bitslip_we <= 1'd0;
	if ((sel & (adr[8:0] == 4'd10))) begin
		a7ddrphy_wdly_dq_bitslip_re <= we;
		a7ddrphy_wdly_dq_bitslip_we <= re;
	end
// synthesis translate_off
	dummy_d_52 <= dummy_s;
// synthesis translate_on
end
assign rdphase0_r = dat_w[1:0];

// synthesis translate_off
reg dummy_d_53;
// synthesis translate_on
always @(*) begin
	rdphase0_re <= 1'd0;
	rdphase0_we <= 1'd0;
	if ((sel & (adr[8:0] == 4'd11))) begin
		rdphase0_re <= we;
		rdphase0_we <= re;
	end
// synthesis translate_off
	dummy_d_53 <= dummy_s;
// synthesis translate_on
end
assign wrphase0_r = dat_w[1:0];

// synthesis translate_off
reg dummy_d_54;
// synthesis translate_on
always @(*) begin
	wrphase0_re <= 1'd0;
	wrphase0_we <= 1'd0;
	if ((sel & (adr[8:0] == 4'd12))) begin
		wrphase0_re <= we;
		wrphase0_we <= re;
	end
// synthesis translate_off
	dummy_d_54 <= dummy_s;
// synthesis translate_on
end
assign rst0_w = a7ddrphy_rst_storage;
assign dly_sel0_w = a7ddrphy_dly_sel_storage[1:0];
assign half_sys8x_taps0_w = a7ddrphy_half_sys8x_taps_storage[4:0];
assign wlevel_en0_w = a7ddrphy_wlevel_en_storage;
assign rdphase0_w = a7ddrphy_rdphase_storage[1:0];
assign wrphase0_w = a7ddrphy_wrphase_storage[1:0];

always @(posedge sys_clk) begin
	a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline0 <= a7ddrphy_dqs_oe_delay_tappeddelayline;
	a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline1 <= a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline0;
	a7ddrphy_dqspattern_o1 <= a7ddrphy_dqspattern_o0;
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip0_value0 <= (a7ddrphy_bitslip0_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip0_value0 <= 3'd7;
	end
	a7ddrphy_bitslip0_r0 <= {a7ddrphy_dqspattern_o1, a7ddrphy_bitslip0_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip1_value0 <= (a7ddrphy_bitslip1_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip1_value0 <= 3'd7;
	end
	a7ddrphy_bitslip1_r0 <= {a7ddrphy_dqspattern_o1, a7ddrphy_bitslip1_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip0_value1 <= (a7ddrphy_bitslip0_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip0_value1 <= 3'd7;
	end
	a7ddrphy_bitslip0_r1 <= {{dfi_p3_wrdata_mask[2], dfi_p3_wrdata_mask[0], dfi_p2_wrdata_mask[2], dfi_p2_wrdata_mask[0], dfi_p1_wrdata_mask[2], dfi_p1_wrdata_mask[0], dfi_p0_wrdata_mask[2], dfi_p0_wrdata_mask[0]}, a7ddrphy_bitslip0_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip1_value1 <= (a7ddrphy_bitslip1_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip1_value1 <= 3'd7;
	end
	a7ddrphy_bitslip1_r1 <= {{dfi_p3_wrdata_mask[3], dfi_p3_wrdata_mask[1], dfi_p2_wrdata_mask[3], dfi_p2_wrdata_mask[1], dfi_p1_wrdata_mask[3], dfi_p1_wrdata_mask[1], dfi_p0_wrdata_mask[3], dfi_p0_wrdata_mask[1]}, a7ddrphy_bitslip1_r1[15:8]};
	a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline0 <= a7ddrphy_dq_oe_delay_tappeddelayline;
	a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1 <= a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline0;
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip0_value2 <= (a7ddrphy_bitslip0_value2 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip0_value2 <= 3'd7;
	end
	a7ddrphy_bitslip0_r2 <= {{dfi_p3_wrdata[16], dfi_p3_wrdata[0], dfi_p2_wrdata[16], dfi_p2_wrdata[0], dfi_p1_wrdata[16], dfi_p1_wrdata[0], dfi_p0_wrdata[16], dfi_p0_wrdata[0]}, a7ddrphy_bitslip0_r2[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip0_value3 <= (a7ddrphy_bitslip0_value3 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip0_value3 <= 3'd7;
	end
	a7ddrphy_bitslip0_r3 <= {a7ddrphy_bitslip03, a7ddrphy_bitslip0_r3[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip1_value2 <= (a7ddrphy_bitslip1_value2 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip1_value2 <= 3'd7;
	end
	a7ddrphy_bitslip1_r2 <= {{dfi_p3_wrdata[17], dfi_p3_wrdata[1], dfi_p2_wrdata[17], dfi_p2_wrdata[1], dfi_p1_wrdata[17], dfi_p1_wrdata[1], dfi_p0_wrdata[17], dfi_p0_wrdata[1]}, a7ddrphy_bitslip1_r2[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip1_value3 <= (a7ddrphy_bitslip1_value3 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip1_value3 <= 3'd7;
	end
	a7ddrphy_bitslip1_r3 <= {a7ddrphy_bitslip13, a7ddrphy_bitslip1_r3[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip2_value0 <= (a7ddrphy_bitslip2_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip2_value0 <= 3'd7;
	end
	a7ddrphy_bitslip2_r0 <= {{dfi_p3_wrdata[18], dfi_p3_wrdata[2], dfi_p2_wrdata[18], dfi_p2_wrdata[2], dfi_p1_wrdata[18], dfi_p1_wrdata[2], dfi_p0_wrdata[18], dfi_p0_wrdata[2]}, a7ddrphy_bitslip2_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip2_value1 <= (a7ddrphy_bitslip2_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip2_value1 <= 3'd7;
	end
	a7ddrphy_bitslip2_r1 <= {a7ddrphy_bitslip21, a7ddrphy_bitslip2_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip3_value0 <= (a7ddrphy_bitslip3_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip3_value0 <= 3'd7;
	end
	a7ddrphy_bitslip3_r0 <= {{dfi_p3_wrdata[19], dfi_p3_wrdata[3], dfi_p2_wrdata[19], dfi_p2_wrdata[3], dfi_p1_wrdata[19], dfi_p1_wrdata[3], dfi_p0_wrdata[19], dfi_p0_wrdata[3]}, a7ddrphy_bitslip3_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip3_value1 <= (a7ddrphy_bitslip3_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip3_value1 <= 3'd7;
	end
	a7ddrphy_bitslip3_r1 <= {a7ddrphy_bitslip31, a7ddrphy_bitslip3_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip4_value0 <= (a7ddrphy_bitslip4_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip4_value0 <= 3'd7;
	end
	a7ddrphy_bitslip4_r0 <= {{dfi_p3_wrdata[20], dfi_p3_wrdata[4], dfi_p2_wrdata[20], dfi_p2_wrdata[4], dfi_p1_wrdata[20], dfi_p1_wrdata[4], dfi_p0_wrdata[20], dfi_p0_wrdata[4]}, a7ddrphy_bitslip4_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip4_value1 <= (a7ddrphy_bitslip4_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip4_value1 <= 3'd7;
	end
	a7ddrphy_bitslip4_r1 <= {a7ddrphy_bitslip41, a7ddrphy_bitslip4_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip5_value0 <= (a7ddrphy_bitslip5_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip5_value0 <= 3'd7;
	end
	a7ddrphy_bitslip5_r0 <= {{dfi_p3_wrdata[21], dfi_p3_wrdata[5], dfi_p2_wrdata[21], dfi_p2_wrdata[5], dfi_p1_wrdata[21], dfi_p1_wrdata[5], dfi_p0_wrdata[21], dfi_p0_wrdata[5]}, a7ddrphy_bitslip5_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip5_value1 <= (a7ddrphy_bitslip5_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip5_value1 <= 3'd7;
	end
	a7ddrphy_bitslip5_r1 <= {a7ddrphy_bitslip51, a7ddrphy_bitslip5_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip6_value0 <= (a7ddrphy_bitslip6_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip6_value0 <= 3'd7;
	end
	a7ddrphy_bitslip6_r0 <= {{dfi_p3_wrdata[22], dfi_p3_wrdata[6], dfi_p2_wrdata[22], dfi_p2_wrdata[6], dfi_p1_wrdata[22], dfi_p1_wrdata[6], dfi_p0_wrdata[22], dfi_p0_wrdata[6]}, a7ddrphy_bitslip6_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip6_value1 <= (a7ddrphy_bitslip6_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip6_value1 <= 3'd7;
	end
	a7ddrphy_bitslip6_r1 <= {a7ddrphy_bitslip61, a7ddrphy_bitslip6_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip7_value0 <= (a7ddrphy_bitslip7_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip7_value0 <= 3'd7;
	end
	a7ddrphy_bitslip7_r0 <= {{dfi_p3_wrdata[23], dfi_p3_wrdata[7], dfi_p2_wrdata[23], dfi_p2_wrdata[7], dfi_p1_wrdata[23], dfi_p1_wrdata[7], dfi_p0_wrdata[23], dfi_p0_wrdata[7]}, a7ddrphy_bitslip7_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip7_value1 <= (a7ddrphy_bitslip7_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip7_value1 <= 3'd7;
	end
	a7ddrphy_bitslip7_r1 <= {a7ddrphy_bitslip71, a7ddrphy_bitslip7_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip8_value0 <= (a7ddrphy_bitslip8_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip8_value0 <= 3'd7;
	end
	a7ddrphy_bitslip8_r0 <= {{dfi_p3_wrdata[24], dfi_p3_wrdata[8], dfi_p2_wrdata[24], dfi_p2_wrdata[8], dfi_p1_wrdata[24], dfi_p1_wrdata[8], dfi_p0_wrdata[24], dfi_p0_wrdata[8]}, a7ddrphy_bitslip8_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip8_value1 <= (a7ddrphy_bitslip8_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip8_value1 <= 3'd7;
	end
	a7ddrphy_bitslip8_r1 <= {a7ddrphy_bitslip81, a7ddrphy_bitslip8_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip9_value0 <= (a7ddrphy_bitslip9_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip9_value0 <= 3'd7;
	end
	a7ddrphy_bitslip9_r0 <= {{dfi_p3_wrdata[25], dfi_p3_wrdata[9], dfi_p2_wrdata[25], dfi_p2_wrdata[9], dfi_p1_wrdata[25], dfi_p1_wrdata[9], dfi_p0_wrdata[25], dfi_p0_wrdata[9]}, a7ddrphy_bitslip9_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip9_value1 <= (a7ddrphy_bitslip9_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip9_value1 <= 3'd7;
	end
	a7ddrphy_bitslip9_r1 <= {a7ddrphy_bitslip91, a7ddrphy_bitslip9_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip10_value0 <= (a7ddrphy_bitslip10_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip10_value0 <= 3'd7;
	end
	a7ddrphy_bitslip10_r0 <= {{dfi_p3_wrdata[26], dfi_p3_wrdata[10], dfi_p2_wrdata[26], dfi_p2_wrdata[10], dfi_p1_wrdata[26], dfi_p1_wrdata[10], dfi_p0_wrdata[26], dfi_p0_wrdata[10]}, a7ddrphy_bitslip10_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip10_value1 <= (a7ddrphy_bitslip10_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip10_value1 <= 3'd7;
	end
	a7ddrphy_bitslip10_r1 <= {a7ddrphy_bitslip101, a7ddrphy_bitslip10_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip11_value0 <= (a7ddrphy_bitslip11_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip11_value0 <= 3'd7;
	end
	a7ddrphy_bitslip11_r0 <= {{dfi_p3_wrdata[27], dfi_p3_wrdata[11], dfi_p2_wrdata[27], dfi_p2_wrdata[11], dfi_p1_wrdata[27], dfi_p1_wrdata[11], dfi_p0_wrdata[27], dfi_p0_wrdata[11]}, a7ddrphy_bitslip11_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip11_value1 <= (a7ddrphy_bitslip11_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip11_value1 <= 3'd7;
	end
	a7ddrphy_bitslip11_r1 <= {a7ddrphy_bitslip111, a7ddrphy_bitslip11_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip12_value0 <= (a7ddrphy_bitslip12_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip12_value0 <= 3'd7;
	end
	a7ddrphy_bitslip12_r0 <= {{dfi_p3_wrdata[28], dfi_p3_wrdata[12], dfi_p2_wrdata[28], dfi_p2_wrdata[12], dfi_p1_wrdata[28], dfi_p1_wrdata[12], dfi_p0_wrdata[28], dfi_p0_wrdata[12]}, a7ddrphy_bitslip12_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip12_value1 <= (a7ddrphy_bitslip12_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip12_value1 <= 3'd7;
	end
	a7ddrphy_bitslip12_r1 <= {a7ddrphy_bitslip121, a7ddrphy_bitslip12_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip13_value0 <= (a7ddrphy_bitslip13_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip13_value0 <= 3'd7;
	end
	a7ddrphy_bitslip13_r0 <= {{dfi_p3_wrdata[29], dfi_p3_wrdata[13], dfi_p2_wrdata[29], dfi_p2_wrdata[13], dfi_p1_wrdata[29], dfi_p1_wrdata[13], dfi_p0_wrdata[29], dfi_p0_wrdata[13]}, a7ddrphy_bitslip13_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip13_value1 <= (a7ddrphy_bitslip13_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip13_value1 <= 3'd7;
	end
	a7ddrphy_bitslip13_r1 <= {a7ddrphy_bitslip131, a7ddrphy_bitslip13_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip14_value0 <= (a7ddrphy_bitslip14_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip14_value0 <= 3'd7;
	end
	a7ddrphy_bitslip14_r0 <= {{dfi_p3_wrdata[30], dfi_p3_wrdata[14], dfi_p2_wrdata[30], dfi_p2_wrdata[14], dfi_p1_wrdata[30], dfi_p1_wrdata[14], dfi_p0_wrdata[30], dfi_p0_wrdata[14]}, a7ddrphy_bitslip14_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip14_value1 <= (a7ddrphy_bitslip14_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip14_value1 <= 3'd7;
	end
	a7ddrphy_bitslip14_r1 <= {a7ddrphy_bitslip141, a7ddrphy_bitslip14_r1[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip15_value0 <= (a7ddrphy_bitslip15_value0 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_wdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip15_value0 <= 3'd7;
	end
	a7ddrphy_bitslip15_r0 <= {{dfi_p3_wrdata[31], dfi_p3_wrdata[15], dfi_p2_wrdata[31], dfi_p2_wrdata[15], dfi_p1_wrdata[31], dfi_p1_wrdata[15], dfi_p0_wrdata[31], dfi_p0_wrdata[15]}, a7ddrphy_bitslip15_r0[15:8]};
	if ((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_re)) begin
		a7ddrphy_bitslip15_value1 <= (a7ddrphy_bitslip15_value1 + 1'd1);
	end
	if (((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_bitslip_rst_re) | a7ddrphy_rst_storage)) begin
		a7ddrphy_bitslip15_value1 <= 3'd7;
	end
	a7ddrphy_bitslip15_r1 <= {a7ddrphy_bitslip151, a7ddrphy_bitslip15_r1[15:8]};
	a7ddrphy_rddata_en_tappeddelayline0 <= (((dfi_p0_rddata_en | dfi_p1_rddata_en) | dfi_p2_rddata_en) | dfi_p3_rddata_en);
	a7ddrphy_rddata_en_tappeddelayline1 <= a7ddrphy_rddata_en_tappeddelayline0;
	a7ddrphy_rddata_en_tappeddelayline2 <= a7ddrphy_rddata_en_tappeddelayline1;
	a7ddrphy_rddata_en_tappeddelayline3 <= a7ddrphy_rddata_en_tappeddelayline2;
	a7ddrphy_rddata_en_tappeddelayline4 <= a7ddrphy_rddata_en_tappeddelayline3;
	a7ddrphy_rddata_en_tappeddelayline5 <= a7ddrphy_rddata_en_tappeddelayline4;
	a7ddrphy_rddata_en_tappeddelayline6 <= a7ddrphy_rddata_en_tappeddelayline5;
	a7ddrphy_wrdata_en_tappeddelayline0 <= (((dfi_p0_wrdata_en | dfi_p1_wrdata_en) | dfi_p2_wrdata_en) | dfi_p3_wrdata_en);
	a7ddrphy_wrdata_en_tappeddelayline1 <= a7ddrphy_wrdata_en_tappeddelayline0;
	dat_r <= 1'd0;
	if (sel) begin
		case (adr[8:0])
			1'd0: begin
				dat_r <= rst0_w;
			end
			1'd1: begin
				dat_r <= dly_sel0_w;
			end
			2'd2: begin
				dat_r <= half_sys8x_taps0_w;
			end
			2'd3: begin
				dat_r <= wlevel_en0_w;
			end
			3'd4: begin
				dat_r <= a7ddrphy_wlevel_strobe_w;
			end
			3'd5: begin
				dat_r <= a7ddrphy_rdly_dq_rst_w;
			end
			3'd6: begin
				dat_r <= a7ddrphy_rdly_dq_inc_w;
			end
			3'd7: begin
				dat_r <= a7ddrphy_rdly_dq_bitslip_rst_w;
			end
			4'd8: begin
				dat_r <= a7ddrphy_rdly_dq_bitslip_w;
			end
			4'd9: begin
				dat_r <= a7ddrphy_wdly_dq_bitslip_rst_w;
			end
			4'd10: begin
				dat_r <= a7ddrphy_wdly_dq_bitslip_w;
			end
			4'd11: begin
				dat_r <= rdphase0_w;
			end
			4'd12: begin
				dat_r <= wrphase0_w;
			end
		endcase
	end
	if (rst0_re) begin
		a7ddrphy_rst_storage <= rst0_r;
	end
	a7ddrphy_rst_re <= rst0_re;
	if (dly_sel0_re) begin
		a7ddrphy_dly_sel_storage[1:0] <= dly_sel0_r;
	end
	a7ddrphy_dly_sel_re <= dly_sel0_re;
	if (half_sys8x_taps0_re) begin
		a7ddrphy_half_sys8x_taps_storage[4:0] <= half_sys8x_taps0_r;
	end
	a7ddrphy_half_sys8x_taps_re <= half_sys8x_taps0_re;
	if (wlevel_en0_re) begin
		a7ddrphy_wlevel_en_storage <= wlevel_en0_r;
	end
	a7ddrphy_wlevel_en_re <= wlevel_en0_re;
	if (rdphase0_re) begin
		a7ddrphy_rdphase_storage[1:0] <= rdphase0_r;
	end
	a7ddrphy_rdphase_re <= rdphase0_re;
	if (wrphase0_re) begin
		a7ddrphy_wrphase_storage[1:0] <= wrphase0_r;
	end
	a7ddrphy_wrphase_re <= wrphase0_re;
	if (sys_rst) begin
		a7ddrphy_rst_storage <= 1'd0;
		a7ddrphy_rst_re <= 1'd0;
		a7ddrphy_dly_sel_storage <= 2'd0;
		a7ddrphy_dly_sel_re <= 1'd0;
		a7ddrphy_half_sys8x_taps_storage <= 5'd21;
		a7ddrphy_half_sys8x_taps_re <= 1'd0;
		a7ddrphy_wlevel_en_storage <= 1'd0;
		a7ddrphy_wlevel_en_re <= 1'd0;
		a7ddrphy_rdphase_storage <= 2'd1;
		a7ddrphy_rdphase_re <= 1'd0;
		a7ddrphy_wrphase_storage <= 2'd2;
		a7ddrphy_wrphase_re <= 1'd0;
		a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline0 <= 1'd0;
		a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline1 <= 1'd0;
		a7ddrphy_dqspattern_o1 <= 8'd0;
		a7ddrphy_bitslip0_value0 <= 3'd7;
		a7ddrphy_bitslip1_value0 <= 3'd7;
		a7ddrphy_bitslip0_value1 <= 3'd7;
		a7ddrphy_bitslip1_value1 <= 3'd7;
		a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline0 <= 1'd0;
		a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1 <= 1'd0;
		a7ddrphy_bitslip0_value2 <= 3'd7;
		a7ddrphy_bitslip0_value3 <= 3'd7;
		a7ddrphy_bitslip1_value2 <= 3'd7;
		a7ddrphy_bitslip1_value3 <= 3'd7;
		a7ddrphy_bitslip2_value0 <= 3'd7;
		a7ddrphy_bitslip2_value1 <= 3'd7;
		a7ddrphy_bitslip3_value0 <= 3'd7;
		a7ddrphy_bitslip3_value1 <= 3'd7;
		a7ddrphy_bitslip4_value0 <= 3'd7;
		a7ddrphy_bitslip4_value1 <= 3'd7;
		a7ddrphy_bitslip5_value0 <= 3'd7;
		a7ddrphy_bitslip5_value1 <= 3'd7;
		a7ddrphy_bitslip6_value0 <= 3'd7;
		a7ddrphy_bitslip6_value1 <= 3'd7;
		a7ddrphy_bitslip7_value0 <= 3'd7;
		a7ddrphy_bitslip7_value1 <= 3'd7;
		a7ddrphy_bitslip8_value0 <= 3'd7;
		a7ddrphy_bitslip8_value1 <= 3'd7;
		a7ddrphy_bitslip9_value0 <= 3'd7;
		a7ddrphy_bitslip9_value1 <= 3'd7;
		a7ddrphy_bitslip10_value0 <= 3'd7;
		a7ddrphy_bitslip10_value1 <= 3'd7;
		a7ddrphy_bitslip11_value0 <= 3'd7;
		a7ddrphy_bitslip11_value1 <= 3'd7;
		a7ddrphy_bitslip12_value0 <= 3'd7;
		a7ddrphy_bitslip12_value1 <= 3'd7;
		a7ddrphy_bitslip13_value0 <= 3'd7;
		a7ddrphy_bitslip13_value1 <= 3'd7;
		a7ddrphy_bitslip14_value0 <= 3'd7;
		a7ddrphy_bitslip14_value1 <= 3'd7;
		a7ddrphy_bitslip15_value0 <= 3'd7;
		a7ddrphy_bitslip15_value1 <= 3'd7;
		a7ddrphy_rddata_en_tappeddelayline0 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline1 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline2 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline3 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline4 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline5 <= 1'd0;
		a7ddrphy_rddata_en_tappeddelayline6 <= 1'd0;
		a7ddrphy_wrdata_en_tappeddelayline0 <= 1'd0;
		a7ddrphy_wrdata_en_tappeddelayline1 <= 1'd0;
	end
end

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(1'd0),
	.D2(1'd1),
	.D3(1'd0),
	.D4(1'd1),
	.D5(1'd0),
	.D6(1'd1),
	.D7(1'd0),
	.D8(1'd1),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(a7ddrphy_sd_clk_se_nodelay)
);

OBUFDS OBUFDS(
	.I(a7ddrphy_sd_clk_se_nodelay),
	.O(ddram_clk_p),
	.OB(ddram_clk_n)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_1 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_cs_n),
	.D2(dfi_p0_cs_n),
	.D3(dfi_p1_cs_n),
	.D4(dfi_p1_cs_n),
	.D5(dfi_p2_cs_n),
	.D6(dfi_p2_cs_n),
	.D7(dfi_p3_cs_n),
	.D8(dfi_p3_cs_n),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_cs_n)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_2 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[0]),
	.D2(dfi_p0_address[0]),
	.D3(dfi_p1_address[0]),
	.D4(dfi_p1_address[0]),
	.D5(dfi_p2_address[0]),
	.D6(dfi_p2_address[0]),
	.D7(dfi_p3_address[0]),
	.D8(dfi_p3_address[0]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[0])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_3 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[1]),
	.D2(dfi_p0_address[1]),
	.D3(dfi_p1_address[1]),
	.D4(dfi_p1_address[1]),
	.D5(dfi_p2_address[1]),
	.D6(dfi_p2_address[1]),
	.D7(dfi_p3_address[1]),
	.D8(dfi_p3_address[1]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[1])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_4 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[2]),
	.D2(dfi_p0_address[2]),
	.D3(dfi_p1_address[2]),
	.D4(dfi_p1_address[2]),
	.D5(dfi_p2_address[2]),
	.D6(dfi_p2_address[2]),
	.D7(dfi_p3_address[2]),
	.D8(dfi_p3_address[2]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[2])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_5 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[3]),
	.D2(dfi_p0_address[3]),
	.D3(dfi_p1_address[3]),
	.D4(dfi_p1_address[3]),
	.D5(dfi_p2_address[3]),
	.D6(dfi_p2_address[3]),
	.D7(dfi_p3_address[3]),
	.D8(dfi_p3_address[3]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[3])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_6 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[4]),
	.D2(dfi_p0_address[4]),
	.D3(dfi_p1_address[4]),
	.D4(dfi_p1_address[4]),
	.D5(dfi_p2_address[4]),
	.D6(dfi_p2_address[4]),
	.D7(dfi_p3_address[4]),
	.D8(dfi_p3_address[4]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[4])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_7 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[5]),
	.D2(dfi_p0_address[5]),
	.D3(dfi_p1_address[5]),
	.D4(dfi_p1_address[5]),
	.D5(dfi_p2_address[5]),
	.D6(dfi_p2_address[5]),
	.D7(dfi_p3_address[5]),
	.D8(dfi_p3_address[5]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[5])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_8 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[6]),
	.D2(dfi_p0_address[6]),
	.D3(dfi_p1_address[6]),
	.D4(dfi_p1_address[6]),
	.D5(dfi_p2_address[6]),
	.D6(dfi_p2_address[6]),
	.D7(dfi_p3_address[6]),
	.D8(dfi_p3_address[6]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[6])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_9 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[7]),
	.D2(dfi_p0_address[7]),
	.D3(dfi_p1_address[7]),
	.D4(dfi_p1_address[7]),
	.D5(dfi_p2_address[7]),
	.D6(dfi_p2_address[7]),
	.D7(dfi_p3_address[7]),
	.D8(dfi_p3_address[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[7])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_10 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[8]),
	.D2(dfi_p0_address[8]),
	.D3(dfi_p1_address[8]),
	.D4(dfi_p1_address[8]),
	.D5(dfi_p2_address[8]),
	.D6(dfi_p2_address[8]),
	.D7(dfi_p3_address[8]),
	.D8(dfi_p3_address[8]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[8])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_11 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[9]),
	.D2(dfi_p0_address[9]),
	.D3(dfi_p1_address[9]),
	.D4(dfi_p1_address[9]),
	.D5(dfi_p2_address[9]),
	.D6(dfi_p2_address[9]),
	.D7(dfi_p3_address[9]),
	.D8(dfi_p3_address[9]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[9])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_12 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[10]),
	.D2(dfi_p0_address[10]),
	.D3(dfi_p1_address[10]),
	.D4(dfi_p1_address[10]),
	.D5(dfi_p2_address[10]),
	.D6(dfi_p2_address[10]),
	.D7(dfi_p3_address[10]),
	.D8(dfi_p3_address[10]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[10])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_13 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[11]),
	.D2(dfi_p0_address[11]),
	.D3(dfi_p1_address[11]),
	.D4(dfi_p1_address[11]),
	.D5(dfi_p2_address[11]),
	.D6(dfi_p2_address[11]),
	.D7(dfi_p3_address[11]),
	.D8(dfi_p3_address[11]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[11])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_14 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_address[12]),
	.D2(dfi_p0_address[12]),
	.D3(dfi_p1_address[12]),
	.D4(dfi_p1_address[12]),
	.D5(dfi_p2_address[12]),
	.D6(dfi_p2_address[12]),
	.D7(dfi_p3_address[12]),
	.D8(dfi_p3_address[12]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_a[12])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_15 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_bank[0]),
	.D2(dfi_p0_bank[0]),
	.D3(dfi_p1_bank[0]),
	.D4(dfi_p1_bank[0]),
	.D5(dfi_p2_bank[0]),
	.D6(dfi_p2_bank[0]),
	.D7(dfi_p3_bank[0]),
	.D8(dfi_p3_bank[0]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(a7ddrphy_pads_ba[0])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_16 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_bank[1]),
	.D2(dfi_p0_bank[1]),
	.D3(dfi_p1_bank[1]),
	.D4(dfi_p1_bank[1]),
	.D5(dfi_p2_bank[1]),
	.D6(dfi_p2_bank[1]),
	.D7(dfi_p3_bank[1]),
	.D8(dfi_p3_bank[1]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(a7ddrphy_pads_ba[1])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_17 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_bank[2]),
	.D2(dfi_p0_bank[2]),
	.D3(dfi_p1_bank[2]),
	.D4(dfi_p1_bank[2]),
	.D5(dfi_p2_bank[2]),
	.D6(dfi_p2_bank[2]),
	.D7(dfi_p3_bank[2]),
	.D8(dfi_p3_bank[2]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(a7ddrphy_pads_ba[2])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_18 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_ras_n),
	.D2(dfi_p0_ras_n),
	.D3(dfi_p1_ras_n),
	.D4(dfi_p1_ras_n),
	.D5(dfi_p2_ras_n),
	.D6(dfi_p2_ras_n),
	.D7(dfi_p3_ras_n),
	.D8(dfi_p3_ras_n),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_ras_n)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_19 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_cas_n),
	.D2(dfi_p0_cas_n),
	.D3(dfi_p1_cas_n),
	.D4(dfi_p1_cas_n),
	.D5(dfi_p2_cas_n),
	.D6(dfi_p2_cas_n),
	.D7(dfi_p3_cas_n),
	.D8(dfi_p3_cas_n),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_cas_n)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_20 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_we_n),
	.D2(dfi_p0_we_n),
	.D3(dfi_p1_we_n),
	.D4(dfi_p1_we_n),
	.D5(dfi_p2_we_n),
	.D6(dfi_p2_we_n),
	.D7(dfi_p3_we_n),
	.D8(dfi_p3_we_n),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_we_n)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_21 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_cke),
	.D2(dfi_p0_cke),
	.D3(dfi_p1_cke),
	.D4(dfi_p1_cke),
	.D5(dfi_p2_cke),
	.D6(dfi_p2_cke),
	.D7(dfi_p3_cke),
	.D8(dfi_p3_cke),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_cke)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_22 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(dfi_p0_odt),
	.D2(dfi_p0_odt),
	.D3(dfi_p1_odt),
	.D4(dfi_p1_odt),
	.D5(dfi_p2_odt),
	.D6(dfi_p2_odt),
	.D7(dfi_p3_odt),
	.D8(dfi_p3_odt),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_odt)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_23 (
	.CLK(sys4x_dqs_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip00[0]),
	.D2(a7ddrphy_bitslip00[1]),
	.D3(a7ddrphy_bitslip00[2]),
	.D4(a7ddrphy_bitslip00[3]),
	.D5(a7ddrphy_bitslip00[4]),
	.D6(a7ddrphy_bitslip00[5]),
	.D7(a7ddrphy_bitslip00[6]),
	.D8(a7ddrphy_bitslip00[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OFB(a7ddrphy0),
	.OQ(a7ddrphy_dqs_o_no_delay0),
	.TQ(a7ddrphy_dqs_t0)
);

IOBUFDS IOBUFDS(
	.I(a7ddrphy_dqs_o_no_delay0),
	.T(a7ddrphy_dqs_t0),
	.IO(ddram_dqs_p[0]),
	.IOB(ddram_dqs_n[0])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_24 (
	.CLK(sys4x_dqs_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip10[0]),
	.D2(a7ddrphy_bitslip10[1]),
	.D3(a7ddrphy_bitslip10[2]),
	.D4(a7ddrphy_bitslip10[3]),
	.D5(a7ddrphy_bitslip10[4]),
	.D6(a7ddrphy_bitslip10[5]),
	.D7(a7ddrphy_bitslip10[6]),
	.D8(a7ddrphy_bitslip10[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OFB(a7ddrphy1),
	.OQ(a7ddrphy_dqs_o_no_delay1),
	.TQ(a7ddrphy_dqs_t1)
);

IOBUFDS IOBUFDS_1(
	.I(a7ddrphy_dqs_o_no_delay1),
	.T(a7ddrphy_dqs_t1),
	.IO(ddram_dqs_p[1]),
	.IOB(ddram_dqs_n[1])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_25 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip01[0]),
	.D2(a7ddrphy_bitslip01[1]),
	.D3(a7ddrphy_bitslip01[2]),
	.D4(a7ddrphy_bitslip01[3]),
	.D5(a7ddrphy_bitslip01[4]),
	.D6(a7ddrphy_bitslip01[5]),
	.D7(a7ddrphy_bitslip01[6]),
	.D8(a7ddrphy_bitslip01[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_dm[0])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_26 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip11[0]),
	.D2(a7ddrphy_bitslip11[1]),
	.D3(a7ddrphy_bitslip11[2]),
	.D4(a7ddrphy_bitslip11[3]),
	.D5(a7ddrphy_bitslip11[4]),
	.D6(a7ddrphy_bitslip11[5]),
	.D7(a7ddrphy_bitslip11[6]),
	.D8(a7ddrphy_bitslip11[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.OQ(ddram_dm[1])
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_27 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip02[0]),
	.D2(a7ddrphy_bitslip02[1]),
	.D3(a7ddrphy_bitslip02[2]),
	.D4(a7ddrphy_bitslip02[3]),
	.D5(a7ddrphy_bitslip02[4]),
	.D6(a7ddrphy_bitslip02[5]),
	.D7(a7ddrphy_bitslip02[6]),
	.D8(a7ddrphy_bitslip02[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay0),
	.TQ(a7ddrphy_dq_t0)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed0),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip03[7]),
	.Q2(a7ddrphy_bitslip03[6]),
	.Q3(a7ddrphy_bitslip03[5]),
	.Q4(a7ddrphy_bitslip03[4]),
	.Q5(a7ddrphy_bitslip03[3]),
	.Q6(a7ddrphy_bitslip03[2]),
	.Q7(a7ddrphy_bitslip03[1]),
	.Q8(a7ddrphy_bitslip03[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay0),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed0)
);

IOBUF IOBUF(
	.I(a7ddrphy_dq_o_nodelay0),
	.T(a7ddrphy_dq_t0),
	.IO(ddram_dq[0]),
	.O(a7ddrphy_dq_i_nodelay0)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_28 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip12[0]),
	.D2(a7ddrphy_bitslip12[1]),
	.D3(a7ddrphy_bitslip12[2]),
	.D4(a7ddrphy_bitslip12[3]),
	.D5(a7ddrphy_bitslip12[4]),
	.D6(a7ddrphy_bitslip12[5]),
	.D7(a7ddrphy_bitslip12[6]),
	.D8(a7ddrphy_bitslip12[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay1),
	.TQ(a7ddrphy_dq_t1)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_1 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip13[7]),
	.Q2(a7ddrphy_bitslip13[6]),
	.Q3(a7ddrphy_bitslip13[5]),
	.Q4(a7ddrphy_bitslip13[4]),
	.Q5(a7ddrphy_bitslip13[3]),
	.Q6(a7ddrphy_bitslip13[2]),
	.Q7(a7ddrphy_bitslip13[1]),
	.Q8(a7ddrphy_bitslip13[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_1 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay1),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed1)
);

IOBUF IOBUF_1(
	.I(a7ddrphy_dq_o_nodelay1),
	.T(a7ddrphy_dq_t1),
	.IO(ddram_dq[1]),
	.O(a7ddrphy_dq_i_nodelay1)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_29 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip20[0]),
	.D2(a7ddrphy_bitslip20[1]),
	.D3(a7ddrphy_bitslip20[2]),
	.D4(a7ddrphy_bitslip20[3]),
	.D5(a7ddrphy_bitslip20[4]),
	.D6(a7ddrphy_bitslip20[5]),
	.D7(a7ddrphy_bitslip20[6]),
	.D8(a7ddrphy_bitslip20[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay2),
	.TQ(a7ddrphy_dq_t2)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_2 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed2),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip21[7]),
	.Q2(a7ddrphy_bitslip21[6]),
	.Q3(a7ddrphy_bitslip21[5]),
	.Q4(a7ddrphy_bitslip21[4]),
	.Q5(a7ddrphy_bitslip21[3]),
	.Q6(a7ddrphy_bitslip21[2]),
	.Q7(a7ddrphy_bitslip21[1]),
	.Q8(a7ddrphy_bitslip21[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_2 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay2),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed2)
);

IOBUF IOBUF_2(
	.I(a7ddrphy_dq_o_nodelay2),
	.T(a7ddrphy_dq_t2),
	.IO(ddram_dq[2]),
	.O(a7ddrphy_dq_i_nodelay2)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_30 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip30[0]),
	.D2(a7ddrphy_bitslip30[1]),
	.D3(a7ddrphy_bitslip30[2]),
	.D4(a7ddrphy_bitslip30[3]),
	.D5(a7ddrphy_bitslip30[4]),
	.D6(a7ddrphy_bitslip30[5]),
	.D7(a7ddrphy_bitslip30[6]),
	.D8(a7ddrphy_bitslip30[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay3),
	.TQ(a7ddrphy_dq_t3)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_3 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed3),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip31[7]),
	.Q2(a7ddrphy_bitslip31[6]),
	.Q3(a7ddrphy_bitslip31[5]),
	.Q4(a7ddrphy_bitslip31[4]),
	.Q5(a7ddrphy_bitslip31[3]),
	.Q6(a7ddrphy_bitslip31[2]),
	.Q7(a7ddrphy_bitslip31[1]),
	.Q8(a7ddrphy_bitslip31[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_3 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay3),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed3)
);

IOBUF IOBUF_3(
	.I(a7ddrphy_dq_o_nodelay3),
	.T(a7ddrphy_dq_t3),
	.IO(ddram_dq[3]),
	.O(a7ddrphy_dq_i_nodelay3)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_31 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip40[0]),
	.D2(a7ddrphy_bitslip40[1]),
	.D3(a7ddrphy_bitslip40[2]),
	.D4(a7ddrphy_bitslip40[3]),
	.D5(a7ddrphy_bitslip40[4]),
	.D6(a7ddrphy_bitslip40[5]),
	.D7(a7ddrphy_bitslip40[6]),
	.D8(a7ddrphy_bitslip40[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay4),
	.TQ(a7ddrphy_dq_t4)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_4 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed4),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip41[7]),
	.Q2(a7ddrphy_bitslip41[6]),
	.Q3(a7ddrphy_bitslip41[5]),
	.Q4(a7ddrphy_bitslip41[4]),
	.Q5(a7ddrphy_bitslip41[3]),
	.Q6(a7ddrphy_bitslip41[2]),
	.Q7(a7ddrphy_bitslip41[1]),
	.Q8(a7ddrphy_bitslip41[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_4 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay4),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed4)
);

IOBUF IOBUF_4(
	.I(a7ddrphy_dq_o_nodelay4),
	.T(a7ddrphy_dq_t4),
	.IO(ddram_dq[4]),
	.O(a7ddrphy_dq_i_nodelay4)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_32 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip50[0]),
	.D2(a7ddrphy_bitslip50[1]),
	.D3(a7ddrphy_bitslip50[2]),
	.D4(a7ddrphy_bitslip50[3]),
	.D5(a7ddrphy_bitslip50[4]),
	.D6(a7ddrphy_bitslip50[5]),
	.D7(a7ddrphy_bitslip50[6]),
	.D8(a7ddrphy_bitslip50[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay5),
	.TQ(a7ddrphy_dq_t5)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_5 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed5),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip51[7]),
	.Q2(a7ddrphy_bitslip51[6]),
	.Q3(a7ddrphy_bitslip51[5]),
	.Q4(a7ddrphy_bitslip51[4]),
	.Q5(a7ddrphy_bitslip51[3]),
	.Q6(a7ddrphy_bitslip51[2]),
	.Q7(a7ddrphy_bitslip51[1]),
	.Q8(a7ddrphy_bitslip51[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_5 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay5),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed5)
);

IOBUF IOBUF_5(
	.I(a7ddrphy_dq_o_nodelay5),
	.T(a7ddrphy_dq_t5),
	.IO(ddram_dq[5]),
	.O(a7ddrphy_dq_i_nodelay5)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_33 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip60[0]),
	.D2(a7ddrphy_bitslip60[1]),
	.D3(a7ddrphy_bitslip60[2]),
	.D4(a7ddrphy_bitslip60[3]),
	.D5(a7ddrphy_bitslip60[4]),
	.D6(a7ddrphy_bitslip60[5]),
	.D7(a7ddrphy_bitslip60[6]),
	.D8(a7ddrphy_bitslip60[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay6),
	.TQ(a7ddrphy_dq_t6)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_6 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed6),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip61[7]),
	.Q2(a7ddrphy_bitslip61[6]),
	.Q3(a7ddrphy_bitslip61[5]),
	.Q4(a7ddrphy_bitslip61[4]),
	.Q5(a7ddrphy_bitslip61[3]),
	.Q6(a7ddrphy_bitslip61[2]),
	.Q7(a7ddrphy_bitslip61[1]),
	.Q8(a7ddrphy_bitslip61[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_6 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay6),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed6)
);

IOBUF IOBUF_6(
	.I(a7ddrphy_dq_o_nodelay6),
	.T(a7ddrphy_dq_t6),
	.IO(ddram_dq[6]),
	.O(a7ddrphy_dq_i_nodelay6)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_34 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip70[0]),
	.D2(a7ddrphy_bitslip70[1]),
	.D3(a7ddrphy_bitslip70[2]),
	.D4(a7ddrphy_bitslip70[3]),
	.D5(a7ddrphy_bitslip70[4]),
	.D6(a7ddrphy_bitslip70[5]),
	.D7(a7ddrphy_bitslip70[6]),
	.D8(a7ddrphy_bitslip70[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay7),
	.TQ(a7ddrphy_dq_t7)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_7 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed7),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip71[7]),
	.Q2(a7ddrphy_bitslip71[6]),
	.Q3(a7ddrphy_bitslip71[5]),
	.Q4(a7ddrphy_bitslip71[4]),
	.Q5(a7ddrphy_bitslip71[3]),
	.Q6(a7ddrphy_bitslip71[2]),
	.Q7(a7ddrphy_bitslip71[1]),
	.Q8(a7ddrphy_bitslip71[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_7 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay7),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[0] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed7)
);

IOBUF IOBUF_7(
	.I(a7ddrphy_dq_o_nodelay7),
	.T(a7ddrphy_dq_t7),
	.IO(ddram_dq[7]),
	.O(a7ddrphy_dq_i_nodelay7)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_35 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip80[0]),
	.D2(a7ddrphy_bitslip80[1]),
	.D3(a7ddrphy_bitslip80[2]),
	.D4(a7ddrphy_bitslip80[3]),
	.D5(a7ddrphy_bitslip80[4]),
	.D6(a7ddrphy_bitslip80[5]),
	.D7(a7ddrphy_bitslip80[6]),
	.D8(a7ddrphy_bitslip80[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay8),
	.TQ(a7ddrphy_dq_t8)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_8 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed8),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip81[7]),
	.Q2(a7ddrphy_bitslip81[6]),
	.Q3(a7ddrphy_bitslip81[5]),
	.Q4(a7ddrphy_bitslip81[4]),
	.Q5(a7ddrphy_bitslip81[3]),
	.Q6(a7ddrphy_bitslip81[2]),
	.Q7(a7ddrphy_bitslip81[1]),
	.Q8(a7ddrphy_bitslip81[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_8 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay8),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed8)
);

IOBUF IOBUF_8(
	.I(a7ddrphy_dq_o_nodelay8),
	.T(a7ddrphy_dq_t8),
	.IO(ddram_dq[8]),
	.O(a7ddrphy_dq_i_nodelay8)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_36 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip90[0]),
	.D2(a7ddrphy_bitslip90[1]),
	.D3(a7ddrphy_bitslip90[2]),
	.D4(a7ddrphy_bitslip90[3]),
	.D5(a7ddrphy_bitslip90[4]),
	.D6(a7ddrphy_bitslip90[5]),
	.D7(a7ddrphy_bitslip90[6]),
	.D8(a7ddrphy_bitslip90[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay9),
	.TQ(a7ddrphy_dq_t9)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_9 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed9),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip91[7]),
	.Q2(a7ddrphy_bitslip91[6]),
	.Q3(a7ddrphy_bitslip91[5]),
	.Q4(a7ddrphy_bitslip91[4]),
	.Q5(a7ddrphy_bitslip91[3]),
	.Q6(a7ddrphy_bitslip91[2]),
	.Q7(a7ddrphy_bitslip91[1]),
	.Q8(a7ddrphy_bitslip91[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_9 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay9),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed9)
);

IOBUF IOBUF_9(
	.I(a7ddrphy_dq_o_nodelay9),
	.T(a7ddrphy_dq_t9),
	.IO(ddram_dq[9]),
	.O(a7ddrphy_dq_i_nodelay9)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_37 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip100[0]),
	.D2(a7ddrphy_bitslip100[1]),
	.D3(a7ddrphy_bitslip100[2]),
	.D4(a7ddrphy_bitslip100[3]),
	.D5(a7ddrphy_bitslip100[4]),
	.D6(a7ddrphy_bitslip100[5]),
	.D7(a7ddrphy_bitslip100[6]),
	.D8(a7ddrphy_bitslip100[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay10),
	.TQ(a7ddrphy_dq_t10)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_10 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed10),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip101[7]),
	.Q2(a7ddrphy_bitslip101[6]),
	.Q3(a7ddrphy_bitslip101[5]),
	.Q4(a7ddrphy_bitslip101[4]),
	.Q5(a7ddrphy_bitslip101[3]),
	.Q6(a7ddrphy_bitslip101[2]),
	.Q7(a7ddrphy_bitslip101[1]),
	.Q8(a7ddrphy_bitslip101[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_10 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay10),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed10)
);

IOBUF IOBUF_10(
	.I(a7ddrphy_dq_o_nodelay10),
	.T(a7ddrphy_dq_t10),
	.IO(ddram_dq[10]),
	.O(a7ddrphy_dq_i_nodelay10)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_38 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip110[0]),
	.D2(a7ddrphy_bitslip110[1]),
	.D3(a7ddrphy_bitslip110[2]),
	.D4(a7ddrphy_bitslip110[3]),
	.D5(a7ddrphy_bitslip110[4]),
	.D6(a7ddrphy_bitslip110[5]),
	.D7(a7ddrphy_bitslip110[6]),
	.D8(a7ddrphy_bitslip110[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay11),
	.TQ(a7ddrphy_dq_t11)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_11 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed11),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip111[7]),
	.Q2(a7ddrphy_bitslip111[6]),
	.Q3(a7ddrphy_bitslip111[5]),
	.Q4(a7ddrphy_bitslip111[4]),
	.Q5(a7ddrphy_bitslip111[3]),
	.Q6(a7ddrphy_bitslip111[2]),
	.Q7(a7ddrphy_bitslip111[1]),
	.Q8(a7ddrphy_bitslip111[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_11 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay11),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed11)
);

IOBUF IOBUF_11(
	.I(a7ddrphy_dq_o_nodelay11),
	.T(a7ddrphy_dq_t11),
	.IO(ddram_dq[11]),
	.O(a7ddrphy_dq_i_nodelay11)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_39 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip120[0]),
	.D2(a7ddrphy_bitslip120[1]),
	.D3(a7ddrphy_bitslip120[2]),
	.D4(a7ddrphy_bitslip120[3]),
	.D5(a7ddrphy_bitslip120[4]),
	.D6(a7ddrphy_bitslip120[5]),
	.D7(a7ddrphy_bitslip120[6]),
	.D8(a7ddrphy_bitslip120[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay12),
	.TQ(a7ddrphy_dq_t12)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_12 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed12),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip121[7]),
	.Q2(a7ddrphy_bitslip121[6]),
	.Q3(a7ddrphy_bitslip121[5]),
	.Q4(a7ddrphy_bitslip121[4]),
	.Q5(a7ddrphy_bitslip121[3]),
	.Q6(a7ddrphy_bitslip121[2]),
	.Q7(a7ddrphy_bitslip121[1]),
	.Q8(a7ddrphy_bitslip121[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_12 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay12),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed12)
);

IOBUF IOBUF_12(
	.I(a7ddrphy_dq_o_nodelay12),
	.T(a7ddrphy_dq_t12),
	.IO(ddram_dq[12]),
	.O(a7ddrphy_dq_i_nodelay12)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_40 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip130[0]),
	.D2(a7ddrphy_bitslip130[1]),
	.D3(a7ddrphy_bitslip130[2]),
	.D4(a7ddrphy_bitslip130[3]),
	.D5(a7ddrphy_bitslip130[4]),
	.D6(a7ddrphy_bitslip130[5]),
	.D7(a7ddrphy_bitslip130[6]),
	.D8(a7ddrphy_bitslip130[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay13),
	.TQ(a7ddrphy_dq_t13)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_13 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed13),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip131[7]),
	.Q2(a7ddrphy_bitslip131[6]),
	.Q3(a7ddrphy_bitslip131[5]),
	.Q4(a7ddrphy_bitslip131[4]),
	.Q5(a7ddrphy_bitslip131[3]),
	.Q6(a7ddrphy_bitslip131[2]),
	.Q7(a7ddrphy_bitslip131[1]),
	.Q8(a7ddrphy_bitslip131[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_13 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay13),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed13)
);

IOBUF IOBUF_13(
	.I(a7ddrphy_dq_o_nodelay13),
	.T(a7ddrphy_dq_t13),
	.IO(ddram_dq[13]),
	.O(a7ddrphy_dq_i_nodelay13)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_41 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip140[0]),
	.D2(a7ddrphy_bitslip140[1]),
	.D3(a7ddrphy_bitslip140[2]),
	.D4(a7ddrphy_bitslip140[3]),
	.D5(a7ddrphy_bitslip140[4]),
	.D6(a7ddrphy_bitslip140[5]),
	.D7(a7ddrphy_bitslip140[6]),
	.D8(a7ddrphy_bitslip140[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay14),
	.TQ(a7ddrphy_dq_t14)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_14 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed14),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip141[7]),
	.Q2(a7ddrphy_bitslip141[6]),
	.Q3(a7ddrphy_bitslip141[5]),
	.Q4(a7ddrphy_bitslip141[4]),
	.Q5(a7ddrphy_bitslip141[3]),
	.Q6(a7ddrphy_bitslip141[2]),
	.Q7(a7ddrphy_bitslip141[1]),
	.Q8(a7ddrphy_bitslip141[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_14 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay14),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed14)
);

IOBUF IOBUF_14(
	.I(a7ddrphy_dq_o_nodelay14),
	.T(a7ddrphy_dq_t14),
	.IO(ddram_dq[14]),
	.O(a7ddrphy_dq_i_nodelay14)
);

OSERDESE2 #(
	.DATA_RATE_OQ("DDR"),
	.DATA_RATE_TQ("BUF"),
	.DATA_WIDTH(4'd8),
	.SERDES_MODE("MASTER"),
	.TRISTATE_WIDTH(1'd1)
) OSERDESE2_42 (
	.CLK(sys4x_clk),
	.CLKDIV(sys_clk),
	.D1(a7ddrphy_bitslip150[0]),
	.D2(a7ddrphy_bitslip150[1]),
	.D3(a7ddrphy_bitslip150[2]),
	.D4(a7ddrphy_bitslip150[3]),
	.D5(a7ddrphy_bitslip150[4]),
	.D6(a7ddrphy_bitslip150[5]),
	.D7(a7ddrphy_bitslip150[6]),
	.D8(a7ddrphy_bitslip150[7]),
	.OCE(1'd1),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.T1((~a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline1)),
	.TCE(1'd1),
	.OQ(a7ddrphy_dq_o_nodelay15),
	.TQ(a7ddrphy_dq_t15)
);

ISERDESE2 #(
	.DATA_RATE("DDR"),
	.DATA_WIDTH(4'd8),
	.INTERFACE_TYPE("NETWORKING"),
	.IOBDELAY("IFD"),
	.NUM_CE(1'd1),
	.SERDES_MODE("MASTER")
) ISERDESE2_15 (
	.BITSLIP(1'd0),
	.CE1(1'd1),
	.CLK(sys4x_clk),
	.CLKB((~sys4x_clk)),
	.CLKDIV(sys_clk),
	.DDLY(a7ddrphy_dq_i_delayed15),
	.RST((sys_rst | a7ddrphy_rst_storage)),
	.Q1(a7ddrphy_bitslip151[7]),
	.Q2(a7ddrphy_bitslip151[6]),
	.Q3(a7ddrphy_bitslip151[5]),
	.Q4(a7ddrphy_bitslip151[4]),
	.Q5(a7ddrphy_bitslip151[3]),
	.Q6(a7ddrphy_bitslip151[2]),
	.Q7(a7ddrphy_bitslip151[1]),
	.Q8(a7ddrphy_bitslip151[0])
);

IDELAYE2 #(
	.CINVCTRL_SEL("FALSE"),
	.DELAY_SRC("IDATAIN"),
	.HIGH_PERFORMANCE_MODE("TRUE"),
	.IDELAY_TYPE("VARIABLE"),
	.IDELAY_VALUE(1'd0),
	.PIPE_SEL("FALSE"),
	.REFCLK_FREQUENCY(200.0),
	.SIGNAL_PATTERN("DATA")
) IDELAYE2_15 (
	.C(sys_clk),
	.CE((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_inc_re)),
	.IDATAIN(a7ddrphy_dq_i_nodelay15),
	.INC(1'd1),
	.LD(((a7ddrphy_dly_sel_storage[1] & a7ddrphy_rdly_dq_rst_re) | a7ddrphy_rst_storage)),
	.LDPIPEEN(1'd0),
	.DATAOUT(a7ddrphy_dq_i_delayed15)
);

IOBUF IOBUF_15(
	.I(a7ddrphy_dq_o_nodelay15),
	.T(a7ddrphy_dq_t15),
	.IO(ddram_dq[15]),
	.O(a7ddrphy_dq_i_nodelay15)
);

endmodule
