# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Bridge stress model -- Genesys 2 pins and clocks (bs_genesys2_top).

# 200 MHz system clock (LVDS); the MMCM derives aclk (100) and cclk (75)
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sys_clk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sys_clk_n]
create_clock -period 5.000 -name clk200 [get_ports sys_clk_p]

set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

# UART (FT232R): names are the HOST's view, as on every Genesys 2 build
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_tx_in]
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_rx_out]
set_false_path -from [get_ports uart_tx_in]
set_false_path -to   [get_ports uart_rx_out]

set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
set_false_path -to [get_ports {led[*]}]

# aclk <-> cclk: every crossing is a gray-pointer async FIFO (the bridge's
# CDC ports), a toggle handshake (apb4_slave_cdc, sync_pulse) or a quasi-static
# synchronizer (data seed, status bits). Bound the data paths to one
# destination period rather than cutting them, so a crossing whose pointers
# skew more than a cycle is a timing failure, not a silent one.
set clk_a [get_clocks -of_objects [get_pins u_mmcm/CLKOUT0]]
set clk_c [get_clocks -of_objects [get_pins u_mmcm/CLKOUT1]]
set_max_delay -datapath_only -from $clk_a -to $clk_c 13.333
set_max_delay -datapath_only -from $clk_c -to $clk_a 10.000

set_property CFGBVS VCCO        [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
