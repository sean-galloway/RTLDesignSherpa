# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Bridge stress model -- Genesys 2 pins and clocks, build-xil
# (bs_genesys2_xil_top). The DDR3 pins are the board-proven LiteDRAM pin
# file (mem-ctrl-ip/scoria/build-litedram/fpga/constraints/ddr3_pins.xdc) and
# bs_litedram's own XDC carries its internal false paths; create_project.tcl
# adds both. This file has the board clock, the I/O and the crossings.

# 200 MHz system clock (LVDS) into u_litedram's PLL
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sys_clk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sys_clk_n]
create_clock -period 5.000 -name clk200 [get_ports sys_clk_p]

# DDR3 banks: internal VREF (as the LiteDRAM memtest build)
set_property INTERNAL_VREF 0.750 [get_iobanks 32]
set_property INTERNAL_VREF 0.750 [get_iobanks 33]
set_property INTERNAL_VREF 0.750 [get_iobanks 34]

# LiteDRAM's reset chain runs on the 200 MHz input clock; only its first stage
# takes D from another domain, so that pin is the crossing (same constraint
# and reason as the memtest build and the fabric benchmark). No -quiet: a
# renamed cell then fails timing instead of passing silently.
set_false_path -to [get_pins u_litedram/FDCE/D]

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

# aclk (LiteDRAM user_clk) <-> cclk (u_mmcm, cascaded from it): every crossing
# is a gray-pointer async FIFO (the bridge's CDC ports), a toggle handshake
# (apb4_slave_cdc, sync_pulse) or a quasi-static synchronizer (data seed,
# status bits). Bound the data paths to one destination period rather than
# cutting them, as in bs_genesys2_top.xdc.
# aclk is taken where it enters u_mmcm: the LiteDRAM core is flattened in
# synthesis, so its user_clk port is not a pin that survives.
set clk_a [get_clocks -of_objects [get_pins u_mmcm/CLKIN1]]
set clk_c [get_clocks -of_objects [get_pins u_mmcm/CLKOUT0]]
set_max_delay -datapath_only -from $clk_a -to $clk_c 13.333
set_max_delay -datapath_only -from $clk_c -to $clk_a 10.000

set_property CFGBVS VCCO        [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
