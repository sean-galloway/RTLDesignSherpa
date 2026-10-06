##==============================================================================
## Genesys 2 Constraints — Binary BCH Loop Harness
##==============================================================================
## Board: Digilent Genesys 2 (Kintex-7 XC7K325T-2FFG900C)
## Top:   bch_loop_genesys2_top  (MMCM: 200 MHz LVDS sysclk -> 100 MHz)
## Host:  single USB-UART link (115200 8N1 via FT2232HL/FT232R)
## Pins from the Digilent Genesys-2-Master.xdc (Rev H).
##==============================================================================

##==============================================================================
## Primary Clock — 200 MHz LVDS system clock (AD12/AD11)
##==============================================================================
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sysclk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sysclk_n]
create_clock -period 5.000 -name sysclk_200 -waveform {0.000 2.500} [get_ports sysclk_p]
## The MMCM (u_mmcm) derives the 100 MHz harness clock; Vivado auto-generates it.

##==============================================================================
## CPU reset button (R19, active-low) — asynchronous
##==============================================================================
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

##==============================================================================
## USB-UART (FT2232HL/FT232R). Async at 115.2 kbaud — relaxed timing.
##==============================================================================
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_tx_in]
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_rx_out]
set_false_path -from [get_ports uart_tx_in]
set_false_path -to   [get_ports uart_rx_out]

##==============================================================================
## User LEDs
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
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
