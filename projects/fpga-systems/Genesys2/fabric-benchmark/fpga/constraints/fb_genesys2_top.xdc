## =============================================================================
## fb_genesys2_top.xdc -- Genesys 2 (xc7k325tffg900-2), fabric benchmark board
## =============================================================================
## sys_clk_p/n (AD12/AD11, 200 MHz) and every ddr3_* pin are placed and timed
## by fb_mig's own XDC (generated from rtl/generated/fb_mig_prj/fb_mig.prj),
## so they are not repeated here. This file holds the board I/O the MIG core
## does not own, and the clock-crossing rules of the top.

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

## ---- aclk (ui_clk) <-> ep_clk ------------------------------------------------
## ep_clk is cascaded from ui_clk (u_ep_mmcm), so Vivado would time the two as
## related clocks. They are crossed only through synchronizers -- the
## axi4_cdc_{rd,wr} async FIFOs (Gray pointers), pulse and snapshot crossings in
## fb_endpoints, and the ep reset synchronizer -- so every path between them is
## bounded by the DESTINATION period instead of being timed as synchronous.
## Not set_clock_groups: that would drop the Gray-pointer paths entirely, and
## their skew must stay under one destination cycle.
set clk_a  [get_clocks -of_objects [get_pins u_mig/ui_clk]]
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
