##==============================================================================
## Genesys 2 Constraints — jet pair-rig bring-up harness
##==============================================================================
## Board: Digilent Genesys 2 (Kintex-7 XC7K325T-2FFG900C)
## Top:   jet_pair_genesys2_top  (MMCM: 200 MHz LVDS sysclk -> 60 MHz)
## Host:  single USB-UART link (115200 8N1 via the board's FT232R)
## Pins from the Digilent Genesys-2-Master.xdc (Rev H), matching the proven
## stream_genesys2_top.xdc. Timing exceptions ported from the same file.
##==============================================================================

##==============================================================================
## Primary Clock — 200 MHz LVDS system clock (AD12/AD11)
##==============================================================================
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sysclk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sysclk_n]
create_clock -period 5.000 -name sysclk_200 -waveform {0.000 2.500} [get_ports sysclk_p]

##==============================================================================
## Timing budget: the placement spread is paid for in the constraint, not in
## the reading of the report (owner, 2026-11-08: "the config placement should
## not be a coin flip. We must be able to predict the timing"). The DDR2 boards
## measured a 0.2 ns WNS band across placer runs of one netlist; this rig shows
## the same band (jet bins 10 -> 11, an unchanged write-address cone, landed at
## +0.517 and +0.152). A report is "closed" only when WNS >= 0 UNDER this
## uncertainty; a design that lands at zero here has no margin and the fix is
## structural, not another placement.
##==============================================================================
set_clock_uncertainty -setup 0.200 [get_clocks -of_objects [get_pins u_mmcm/CLKOUT0]]

##==============================================================================
## CPU reset button (R19, active-low) — asynchronous
##==============================================================================
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

##==============================================================================
## USB-UART. Async at 115.2 kbaud — relaxed timing.
##==============================================================================
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_tx_in]
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_rx_out]
set_false_path -from [get_ports uart_tx_in]
set_false_path -to   [get_ports uart_rx_out]

##==============================================================================
## User LEDs (8)
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
## Reset-synchronizer CDC
##==============================================================================
set_false_path -from [get_ports cpu_resetn] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
