## =============================================================================
## fb_genesys2_top.xdc -- Genesys 2 (xc7k325tffg900-2), fabric benchmark board
## =============================================================================
## The DDR3 pins are the generated Genesys 2 pin file the LiteDRAM memtest
## proved on this board (mem-ctrl-ip/scoria/build-litedram/fpga/constraints/
## ddr3_pins.xdc, added by create_project.tcl), and fb_litedram's own XDC
## carries its CDC false paths. This file holds the board clock and I/O and
## the clock-crossing rules of the top.

## ---- Board clock: 200 MHz LVDS into fb_litedram's PLL ------------------------
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sys_clk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sys_clk_n]
create_clock -period 5.000 -name clk200 [get_ports sys_clk_p]

## DDR3 banks: internal VREF (as the memtest build).
set_property INTERNAL_VREF 0.750 [get_iobanks 32]
set_property INTERNAL_VREF 0.750 [get_iobanks 33]
set_property INTERNAL_VREF 0.750 [get_iobanks 34]

## ---- Board I/O (same pins as the STREAM Genesys 2 top) ----------------------
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

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

## fb_litedram's reset chain (FDCE -> FDCE_1 ... FDCE_7) runs on the 200 MHz
## input clock; only its first stage takes D from another domain (the sys
## domain's CSR soft-reset strobe), so that one pin is the crossing point and
## is asynchronous by design. Same constraint and reasoning as the LiteDRAM
## memtest build (mem-ctrl-ip/scoria/build-litedram/fpga/constraints/
## board_pins.xdc). No -quiet: a renamed cell matches nothing and the build
## then reports timing not met, so the constraint checks itself.
set_false_path -to [get_pins u_litedram/FDCE/D]

## ---- aclk (fb_litedram user_clk) <-> ep_clk -----------------------------------
## ep_clk is cascaded from aclk (u_ep_mmcm), so Vivado would time the two as
## related clocks. They are crossed only through synchronizers -- the
## axi4_cdc_{rd,wr} async FIFOs (Gray pointers), pulse and snapshot crossings in
## fb_endpoints, and the ep reset synchronizer -- so every path between them is
## bounded by the DESTINATION period instead of being timed as synchronous.
## Not set_clock_groups: that would drop the Gray-pointer paths entirely, and
## their skew must stay under one destination cycle.
## aclk is taken where it enters u_ep_mmcm: the LiteDRAM core is flattened in
## synthesis, so its user_clk port is not a pin that survives.
set clk_a  [get_clocks -of_objects [get_pins u_ep_mmcm/CLKIN1]]
set clk_ep [get_clocks -of_objects [get_pins u_ep_bufg/O]]
set_max_delay -datapath_only -from $clk_a  -to $clk_ep 8.000
set_max_delay -datapath_only -from $clk_ep -to $clk_a  10.000

## ep reset synchronizer: async assertion from the aclk domain.
set_false_path -to [get_pins -hier -filter {NAME =~ r_ep_rst_meta_reg/CLR}]
set_false_path -to [get_pins -hier -filter {NAME =~ r_ep_rst_sync_reg/CLR}]

## ---- LED driver (slow-domain CDC, as in the STREAM boards) -------------------
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by 1000000 \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]
set_clock_groups -asynchronous -group $clk_a -group [get_clocks led_slow_clk]

set led_hs_pre {NAME =~ *u_led_status_driver/u_hs/}
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_req_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_req_sync_reg[0]/D"] \
    5.000
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_ack_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_ack_sync_reg[0]/D"] \
    10.000
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_src_data_hold_reg[*]/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_dst_data_reg[*]/D"] \
    5.000

## ---- Bitstream ----------------------------------------------------------------
set_property CFGBVS VCCO        [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
