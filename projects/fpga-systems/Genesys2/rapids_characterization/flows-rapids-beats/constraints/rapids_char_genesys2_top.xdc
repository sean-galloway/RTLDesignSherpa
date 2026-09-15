##==============================================================================
## Genesys 2 Constraints — RAPIDS beats Characterization Harness
##==============================================================================
## Board: Digilent Genesys 2 (Kintex-7 XC7K325T-2FFG900C)
## Top:   rapids_char_genesys2_top  (MMCM: 200 MHz LVDS sysclk -> 100 MHz)
## Host:  single USB-UART link (115200 8N1 via FT2232HL)
## Pins from the Digilent Genesys-2-Master.xdc (Rev H).
##==============================================================================

##==============================================================================
## Primary Clock — 200 MHz LVDS system clock (AD12/AD11)
##==============================================================================
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sysclk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sysclk_n]
create_clock -period 5.000 -name sysclk_200 -waveform {0.000 2.500} [get_ports sysclk_p]
## The MMCM (u_mmcm) derives the 100 MHz DUT clock; Vivado auto-generates it.

##==============================================================================
## CPU reset button (R19, active-low) — asynchronous
##==============================================================================
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

##==============================================================================
## USB-UART (FT2232HL). Async at 115.2 kbaud — relaxed timing.
##==============================================================================
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_tx_in]
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_rx_out]
set_false_path -from [get_ports uart_tx_in]
set_false_path -to   [get_ports uart_rx_out]

##==============================================================================
## User LEDs (low 8 of the harness status bank)
##==============================================================================
set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
set_false_path -to [get_ports {led[*]}]

##==============================================================================
## Reset-synchronizer CDC (r_rst_meta/r_rst_sync in rapids_char_top). The -hier
## filters match regardless of the u_char_top wrapper prefix.
##==============================================================================
set_false_path -from [get_ports cpu_resetn] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

##==============================================================================
## LED status driver — slow generated clock + CDC handshake (same structure as
## the Nexys flow; source/target pins are found by -hier, and the DUT 100 MHz
## clock is referenced via the wrapper's clk100 BUFG output).
##==============================================================================
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by 1000000 \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]

set_clock_groups -asynchronous \
    -group [get_clocks -of_objects [get_pins u_bufg_c0/O]] \
    -group [get_clocks led_slow_clk]

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

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
