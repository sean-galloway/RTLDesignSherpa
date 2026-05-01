
# file: axi_mcdma_0.xdc
# (c) Copyright 2009 - 2023 Advanced Micro Devices, Inc. All rights reserved.
# 
# This file contains confidential and proprietary information
# of Advanced Micro Devices, Inc. and is protected under U.S. and
# international copyright and other intellectual property
# laws.
# 
# DISCLAIMER
# This disclaimer is not a license and does not grant any
# rights to the materials distributed herewith. Except as
# otherwise provided in a valid license issued to you by
# AMD, and to the maximum extent permitted by applicable
# law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
# WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
# AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
# BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
# INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
# (2) AMD shall not be liable (whether in contract or tort,
# including negligence, or under any other theory of
# liability) for any loss or damage of any kind or nature
# related to, arising under or in connection with these
# materials, including for any direct, or any indirect,
# special, incidental, or consequential loss or damage
# (including loss of data, profits, goodwill, or any type of
# loss or damage suffered as a result of any action brought
# by a third party) even if such damage or loss was
# reasonably foreseeable or AMD had been advised of the
# possibility of the same.
# 
# CRITICAL APPLICATIONS
# AMD products are not designed or intended to be fail-
# safe, or for use in any application requiring fail-safe
# performance, such as life-support or safety devices or
# systems, Class III medical devices, nuclear facilities,
# applications related to the deployment of airbags, or any
# other applications that could lead to death, personal
# injury, or severe property or environmental damage
# (individually and collectively, "Critical
# Applications"). Customer assumes the sole risk and
# liability of any use of AMD products in Critical
# Applications, subject only to applicable laws and
# regulations governing limitations on product liability.
# 
# THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
# PART OF THIS FILE AT ALL TIMES.

set_false_path -quiet -to [get_pins  -quiet -hier *cdc_to*/D]

create_waiver -internal -scope -type CDC -id {CDC-1} -user "axi_mcdma" -tags "9601"\
-desc "The CDC-1 warning is waived as it is safe in the context of AXI MCDMA. The Address and Data value does not change until AXI transaction is complete." \
-to [get_pins -hier -quiet -filter {NAME =~*I_AXI_DMA_REG_MODULE/GEN_AXI_LITE_IF.AXI_LITE_IF_I/GEN_ASYNC_WRITE.REG_WADDR_TO_IPCLK/syncstages_ff_reg*/D}]

create_waiver -internal -scope -type CDC -id {CDC-1} -user "axi_mcdma" -tags "9601"\
-desc "The CDC-1 warning is waived as it is safe in the context of AXI MCDMA. The Address and Data value does not change until AXI transaction is complete." \
-to [get_pins -hier -quiet -filter {NAME =~*I_AXI_DMA_REG_MODULE/GEN_AXI_LITE_IF.AXI_LITE_IF_I/GEN_ASYNC_WRITE.REG_WADDR_TO_IPCLK1/syncstages_ff_reg*/D}]


set_max_delay 15 -from [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*I_PRMRY_DATAMOVER/GEN_MM2S_FULL.I_MM2S_FULL_WRAPPER/ENABLE_AXIS_SKID.I_MM2S_SKID_BUF/sig_last_reg_out_reg*}] -filter {REF_PIN_NAME == C}] \
                   -to [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*INCLUDE_MM2S_SOF_EOF_GENERATOR.INCLUDE_SOFT_RESET_PER_CHANNEL.I_MM2S_MULTI_CHANNEL_RST_MNGR/mm2s_sideband_out_reg[*]}]  -filter {REF_PIN_NAME == D}] \
                   -datapath_only
set_max_delay 15 -from [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*I_PRMRY_DATAMOVER/GEN_MM2S_FULL.I_MM2S_FULL_WRAPPER/ENABLE_AXIS_SKID.I_MM2S_SKID_BUF/sig_m_valid_out_reg*}] -filter {REF_PIN_NAME == C}] \
                   -to [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*INCLUDE_MM2S_SOF_EOF_GENERATOR.INCLUDE_SOFT_RESET_PER_CHANNEL.I_MM2S_MULTI_CHANNEL_RST_MNGR/mm2s_sideband_out_reg[*]}]  -filter {REF_PIN_NAME == D}] \
                   -datapath_only
set_max_delay 15 -from [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*INCLUDE_MM2S_SOF_EOF_GENERATOR.I_MM2S_DMA_MNGR/GEN_MM2S_DMA_CONTROL.GEN_SCATTER_GATHER_MODE.I_MM2S_TDEST_FIFO/*doutb_pipe_reg*}] -filter {REF_PIN_NAME == C}] \
                   -to [get_pins -quiet -of [get_cells -hierarchical -filter {NAME =~*INCLUDE_MM2S_SOF_EOF_GENERATOR.INCLUDE_SOFT_RESET_PER_CHANNEL.I_MM2S_MULTI_CHANNEL_RST_MNGR/mm2s_sideband_out_reg[*]}]  -filter {REF_PIN_NAME == D}] \
                   -datapath_only

