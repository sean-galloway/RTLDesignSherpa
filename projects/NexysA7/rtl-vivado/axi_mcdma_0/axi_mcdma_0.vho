-- (c) Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
-- (c) Copyright 2022-2026 Advanced Micro Devices, Inc. All rights reserved.
-- 
-- This file contains confidential and proprietary information
-- of AMD and is protected under U.S. and international copyright
-- and other intellectual property laws.
-- 
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- AMD, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) AMD shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or AMD had been advised of the
-- possibility of the same.
-- 
-- CRITICAL APPLICATIONS
-- AMD products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of AMD products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
-- 
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-- 
-- DO NOT MODIFY THIS FILE.
-- IP VLNV: xilinx.com:ip:axi_mcdma:1.2
-- IP Revision: 2

-- The following code must appear in the VHDL architecture header.

------------- Begin Cut here for COMPONENT Declaration ------ COMP_TAG
COMPONENT axi_mcdma_0
  PORT (
    s_axi_aclk : IN STD_LOGIC;
    s_axi_lite_aclk : IN STD_LOGIC;
    axi_resetn : IN STD_LOGIC;
    s_axi_lite_awvalid : IN STD_LOGIC;
    s_axi_lite_awready : OUT STD_LOGIC;
    s_axi_lite_awaddr : IN STD_LOGIC_VECTOR(11 DOWNTO 0);
    s_axi_lite_wvalid : IN STD_LOGIC;
    s_axi_lite_wready : OUT STD_LOGIC;
    s_axi_lite_wdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axi_lite_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    s_axi_lite_bvalid : OUT STD_LOGIC;
    s_axi_lite_bready : IN STD_LOGIC;
    s_axi_lite_arvalid : IN STD_LOGIC;
    s_axi_lite_arready : OUT STD_LOGIC;
    s_axi_lite_araddr : IN STD_LOGIC_VECTOR(11 DOWNTO 0);
    s_axi_lite_rvalid : OUT STD_LOGIC;
    s_axi_lite_rready : IN STD_LOGIC;
    s_axi_lite_rdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axi_lite_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_sg_awaddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_sg_awlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_sg_awsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_sg_awburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_sg_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_sg_awuser : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_sg_awcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_sg_awvalid : OUT STD_LOGIC;
    m_axi_sg_awready : IN STD_LOGIC;
    m_axi_sg_wdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_sg_wstrb : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_sg_wlast : OUT STD_LOGIC;
    m_axi_sg_wvalid : OUT STD_LOGIC;
    m_axi_sg_wready : IN STD_LOGIC;
    m_axi_sg_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_sg_bvalid : IN STD_LOGIC;
    m_axi_sg_bready : OUT STD_LOGIC;
    m_axi_sg_araddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_sg_arlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_sg_arsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_sg_arburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_sg_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_sg_aruser : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_sg_arcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_sg_arvalid : OUT STD_LOGIC;
    m_axi_sg_arready : IN STD_LOGIC;
    m_axi_sg_rdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_sg_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_sg_rlast : IN STD_LOGIC;
    m_axi_sg_rvalid : IN STD_LOGIC;
    m_axi_sg_rready : OUT STD_LOGIC;
    m_axi_mm2s_araddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_mm2s_arlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_mm2s_arsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_mm2s_arburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_mm2s_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_mm2s_arcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_mm2s_aruser : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_mm2s_arvalid : OUT STD_LOGIC;
    m_axi_mm2s_arready : IN STD_LOGIC;
    m_axi_mm2s_rdata : IN STD_LOGIC_VECTOR(127 DOWNTO 0);
    m_axi_mm2s_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_mm2s_rlast : IN STD_LOGIC;
    m_axi_mm2s_rvalid : IN STD_LOGIC;
    m_axi_mm2s_rready : OUT STD_LOGIC;
    mm2s_prmry_reset_out_n : OUT STD_LOGIC;
    mm2s_prmry_reset_out_perch_n : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axis_mm2s_tdata : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axis_mm2s_tkeep : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axis_mm2s_tvalid : OUT STD_LOGIC;
    m_axis_mm2s_tready : IN STD_LOGIC;
    m_axis_mm2s_tlast : OUT STD_LOGIC;
    m_axis_mm2s_tuser : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    m_axis_mm2s_tid : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axis_mm2s_tdest : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_s2mm_awaddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
    m_axi_s2mm_awlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
    m_axi_s2mm_awsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_s2mm_awburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_s2mm_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
    m_axi_s2mm_awcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_s2mm_awuser : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    m_axi_s2mm_awvalid : OUT STD_LOGIC;
    m_axi_s2mm_awready : IN STD_LOGIC;
    m_axi_s2mm_wdata : OUT STD_LOGIC_VECTOR(127 DOWNTO 0);
    m_axi_s2mm_wstrb : OUT STD_LOGIC_VECTOR(15 DOWNTO 0);
    m_axi_s2mm_wlast : OUT STD_LOGIC;
    m_axi_s2mm_wvalid : OUT STD_LOGIC;
    m_axi_s2mm_wready : IN STD_LOGIC;
    m_axi_s2mm_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
    m_axi_s2mm_bvalid : IN STD_LOGIC;
    m_axi_s2mm_bready : OUT STD_LOGIC;
    s2mm_prmry_reset_out_n : OUT STD_LOGIC;
    s2mm_prmry_reset_out_perch_n : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axis_s2mm_tdata : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
    s_axis_s2mm_tkeep : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    s_axis_s2mm_tvalid : IN STD_LOGIC;
    s_axis_s2mm_tready : OUT STD_LOGIC;
    s_axis_s2mm_tlast : IN STD_LOGIC;
    s_axis_s2mm_tuser : IN STD_LOGIC_VECTOR(15 DOWNTO 0);
    s_axis_s2mm_tid : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
    s_axis_s2mm_tdest : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
    mm2s_ch1_introut : OUT STD_LOGIC;
    mm2s_ch2_introut : OUT STD_LOGIC;
    mm2s_ch3_introut : OUT STD_LOGIC;
    mm2s_ch4_introut : OUT STD_LOGIC;
    s2mm_ch1_introut : OUT STD_LOGIC;
    s2mm_ch2_introut : OUT STD_LOGIC;
    s2mm_ch3_introut : OUT STD_LOGIC;
    s2mm_ch4_introut : OUT STD_LOGIC 
  );
END COMPONENT;
-- COMP_TAG_END ------ End COMPONENT Declaration ------------

-- The following code must appear in the VHDL architecture
-- body. Substitute your own instance name and net names.

------------- Begin Cut here for INSTANTIATION Template ----- INST_TAG
your_instance_name : axi_mcdma_0
  PORT MAP (
    s_axi_aclk => s_axi_aclk,
    s_axi_lite_aclk => s_axi_lite_aclk,
    axi_resetn => axi_resetn,
    s_axi_lite_awvalid => s_axi_lite_awvalid,
    s_axi_lite_awready => s_axi_lite_awready,
    s_axi_lite_awaddr => s_axi_lite_awaddr,
    s_axi_lite_wvalid => s_axi_lite_wvalid,
    s_axi_lite_wready => s_axi_lite_wready,
    s_axi_lite_wdata => s_axi_lite_wdata,
    s_axi_lite_bresp => s_axi_lite_bresp,
    s_axi_lite_bvalid => s_axi_lite_bvalid,
    s_axi_lite_bready => s_axi_lite_bready,
    s_axi_lite_arvalid => s_axi_lite_arvalid,
    s_axi_lite_arready => s_axi_lite_arready,
    s_axi_lite_araddr => s_axi_lite_araddr,
    s_axi_lite_rvalid => s_axi_lite_rvalid,
    s_axi_lite_rready => s_axi_lite_rready,
    s_axi_lite_rdata => s_axi_lite_rdata,
    s_axi_lite_rresp => s_axi_lite_rresp,
    m_axi_sg_awaddr => m_axi_sg_awaddr,
    m_axi_sg_awlen => m_axi_sg_awlen,
    m_axi_sg_awsize => m_axi_sg_awsize,
    m_axi_sg_awburst => m_axi_sg_awburst,
    m_axi_sg_awprot => m_axi_sg_awprot,
    m_axi_sg_awuser => m_axi_sg_awuser,
    m_axi_sg_awcache => m_axi_sg_awcache,
    m_axi_sg_awvalid => m_axi_sg_awvalid,
    m_axi_sg_awready => m_axi_sg_awready,
    m_axi_sg_wdata => m_axi_sg_wdata,
    m_axi_sg_wstrb => m_axi_sg_wstrb,
    m_axi_sg_wlast => m_axi_sg_wlast,
    m_axi_sg_wvalid => m_axi_sg_wvalid,
    m_axi_sg_wready => m_axi_sg_wready,
    m_axi_sg_bresp => m_axi_sg_bresp,
    m_axi_sg_bvalid => m_axi_sg_bvalid,
    m_axi_sg_bready => m_axi_sg_bready,
    m_axi_sg_araddr => m_axi_sg_araddr,
    m_axi_sg_arlen => m_axi_sg_arlen,
    m_axi_sg_arsize => m_axi_sg_arsize,
    m_axi_sg_arburst => m_axi_sg_arburst,
    m_axi_sg_arprot => m_axi_sg_arprot,
    m_axi_sg_aruser => m_axi_sg_aruser,
    m_axi_sg_arcache => m_axi_sg_arcache,
    m_axi_sg_arvalid => m_axi_sg_arvalid,
    m_axi_sg_arready => m_axi_sg_arready,
    m_axi_sg_rdata => m_axi_sg_rdata,
    m_axi_sg_rresp => m_axi_sg_rresp,
    m_axi_sg_rlast => m_axi_sg_rlast,
    m_axi_sg_rvalid => m_axi_sg_rvalid,
    m_axi_sg_rready => m_axi_sg_rready,
    m_axi_mm2s_araddr => m_axi_mm2s_araddr,
    m_axi_mm2s_arlen => m_axi_mm2s_arlen,
    m_axi_mm2s_arsize => m_axi_mm2s_arsize,
    m_axi_mm2s_arburst => m_axi_mm2s_arburst,
    m_axi_mm2s_arprot => m_axi_mm2s_arprot,
    m_axi_mm2s_arcache => m_axi_mm2s_arcache,
    m_axi_mm2s_aruser => m_axi_mm2s_aruser,
    m_axi_mm2s_arvalid => m_axi_mm2s_arvalid,
    m_axi_mm2s_arready => m_axi_mm2s_arready,
    m_axi_mm2s_rdata => m_axi_mm2s_rdata,
    m_axi_mm2s_rresp => m_axi_mm2s_rresp,
    m_axi_mm2s_rlast => m_axi_mm2s_rlast,
    m_axi_mm2s_rvalid => m_axi_mm2s_rvalid,
    m_axi_mm2s_rready => m_axi_mm2s_rready,
    mm2s_prmry_reset_out_n => mm2s_prmry_reset_out_n,
    mm2s_prmry_reset_out_perch_n => mm2s_prmry_reset_out_perch_n,
    m_axis_mm2s_tdata => m_axis_mm2s_tdata,
    m_axis_mm2s_tkeep => m_axis_mm2s_tkeep,
    m_axis_mm2s_tvalid => m_axis_mm2s_tvalid,
    m_axis_mm2s_tready => m_axis_mm2s_tready,
    m_axis_mm2s_tlast => m_axis_mm2s_tlast,
    m_axis_mm2s_tuser => m_axis_mm2s_tuser,
    m_axis_mm2s_tid => m_axis_mm2s_tid,
    m_axis_mm2s_tdest => m_axis_mm2s_tdest,
    m_axi_s2mm_awaddr => m_axi_s2mm_awaddr,
    m_axi_s2mm_awlen => m_axi_s2mm_awlen,
    m_axi_s2mm_awsize => m_axi_s2mm_awsize,
    m_axi_s2mm_awburst => m_axi_s2mm_awburst,
    m_axi_s2mm_awprot => m_axi_s2mm_awprot,
    m_axi_s2mm_awcache => m_axi_s2mm_awcache,
    m_axi_s2mm_awuser => m_axi_s2mm_awuser,
    m_axi_s2mm_awvalid => m_axi_s2mm_awvalid,
    m_axi_s2mm_awready => m_axi_s2mm_awready,
    m_axi_s2mm_wdata => m_axi_s2mm_wdata,
    m_axi_s2mm_wstrb => m_axi_s2mm_wstrb,
    m_axi_s2mm_wlast => m_axi_s2mm_wlast,
    m_axi_s2mm_wvalid => m_axi_s2mm_wvalid,
    m_axi_s2mm_wready => m_axi_s2mm_wready,
    m_axi_s2mm_bresp => m_axi_s2mm_bresp,
    m_axi_s2mm_bvalid => m_axi_s2mm_bvalid,
    m_axi_s2mm_bready => m_axi_s2mm_bready,
    s2mm_prmry_reset_out_n => s2mm_prmry_reset_out_n,
    s2mm_prmry_reset_out_perch_n => s2mm_prmry_reset_out_perch_n,
    s_axis_s2mm_tdata => s_axis_s2mm_tdata,
    s_axis_s2mm_tkeep => s_axis_s2mm_tkeep,
    s_axis_s2mm_tvalid => s_axis_s2mm_tvalid,
    s_axis_s2mm_tready => s_axis_s2mm_tready,
    s_axis_s2mm_tlast => s_axis_s2mm_tlast,
    s_axis_s2mm_tuser => s_axis_s2mm_tuser,
    s_axis_s2mm_tid => s_axis_s2mm_tid,
    s_axis_s2mm_tdest => s_axis_s2mm_tdest,
    mm2s_ch1_introut => mm2s_ch1_introut,
    mm2s_ch2_introut => mm2s_ch2_introut,
    mm2s_ch3_introut => mm2s_ch3_introut,
    mm2s_ch4_introut => mm2s_ch4_introut,
    s2mm_ch1_introut => s2mm_ch1_introut,
    s2mm_ch2_introut => s2mm_ch2_introut,
    s2mm_ch3_introut => s2mm_ch3_introut,
    s2mm_ch4_introut => s2mm_ch4_introut
  );
-- INST_TAG_END ------ End INSTANTIATION Template ---------

-- You must compile the wrapper file axi_mcdma_0.vhd when simulating
-- the core, axi_mcdma_0. When compiling the wrapper file, be sure to
-- reference the VHDL simulation library.



