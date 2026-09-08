##==============================================================================
## Nexys A7-100T Constraints for CDC Counter Display Project
##==============================================================================
## Board: Digilent Nexys A7-100T (XC7A100T-1CSG324C)
## Project: CDC Counter Display with Button Debounce
## Description: Physical pin assignments and timing constraints
##==============================================================================

##==============================================================================
## Clock Signals
##==============================================================================

## Primary Clock (100 MHz oscillator)
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports CLK100MHZ]

##==============================================================================
## Buttons
##==============================================================================

## Center Button (BTNC) - Counter Increment
set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports btnC]

## Up Button (BTNU) - Reset
set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports btnU]

##==============================================================================
## 7-Segment Display
##==============================================================================

## Segment Cathodes (Active-Low)
set_property -dict {PACKAGE_PIN L3 IOSTANDARD LVCMOS33} [get_ports {seg[0]}];  # CA
set_property -dict {PACKAGE_PIN N1 IOSTANDARD LVCMOS33} [get_ports {seg[1]}];  # CB
set_property -dict {PACKAGE_PIN L5 IOSTANDARD LVCMOS33} [get_ports {seg[2]}];  # CC
set_property -dict {PACKAGE_PIN L4 IOSTANDARD LVCMOS33} [get_ports {seg[3]}];  # CD
set_property -dict {PACKAGE_PIN K3 IOSTANDARD LVCMOS33} [get_ports {seg[4]}];  # CE
set_property -dict {PACKAGE_PIN M2 IOSTANDARD LVCMOS33} [get_ports {seg[5]}];  # CF
set_property -dict {PACKAGE_PIN L6 IOSTANDARD LVCMOS33} [get_ports {seg[6]}];  # CG

## Digit Anodes (Active-Low)
set_property -dict {PACKAGE_PIN N6 IOSTANDARD LVCMOS33} [get_ports {an[7]}];   # AN7 (leftmost)
set_property -dict {PACKAGE_PIN M6 IOSTANDARD LVCMOS33} [get_ports {an[6]}];   # AN6
set_property -dict {PACKAGE_PIN M3 IOSTANDARD LVCMOS33} [get_ports {an[5]}];   # AN5
set_property -dict {PACKAGE_PIN N5 IOSTANDARD LVCMOS33} [get_ports {an[4]}];   # AN4
set_property -dict {PACKAGE_PIN N2 IOSTANDARD LVCMOS33} [get_ports {an[3]}];   # AN3
set_property -dict {PACKAGE_PIN N4 IOSTANDARD LVCMOS33} [get_ports {an[2]}];   # AN2
set_property -dict {PACKAGE_PIN L1 IOSTANDARD LVCMOS33} [get_ports {an[1]}];   # AN1
set_property -dict {PACKAGE_PIN M4 IOSTANDARD LVCMOS33} [get_ports {an[0]}];   # AN0 (rightmost)

##==============================================================================
## LEDs
##==============================================================================

## Heartbeat Indicators
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {led[0]}]; # Button domain heartbeat
set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {led[1]}]; # Display domain heartbeat

##==============================================================================
## Clock Domain Crossing (CDC) Constraints
##==============================================================================

## Generated Clocks (Created by clock_divider modules)

## Button Clock Domain (10 Hz derived from sys_clk)
## Path: CLK100MHZ → u_btn_clk_div → btn_clk
create_generated_clock -name btn_clk \
    -source [get_pins u_btn_clk_div/i_clk] \
    -divide_by 10000000 \
    [get_pins u_btn_clk_div/o_clk_out]

## Display Clock Domain (1 kHz derived from sys_clk)
## Path: CLK100MHZ → u_disp_clk_div → disp_clk
create_generated_clock -name disp_clk \
    -source [get_pins u_disp_clk_div/i_clk] \
    -divide_by 100000 \
    [get_pins u_disp_clk_div/o_clk_out]

## Asynchronous Clock Groups
## These clocks are completely independent - no timing relationship
set_clock_groups -asynchronous \
    -group [get_clocks sys_clk_pin] \
    -group [get_clocks btn_clk] \
    -group [get_clocks disp_clk]

## False Paths for CDC Crossings

## Crossing #1: Counter value (btn_clk → disp_clk)
## Safe: Quasi-static data sampled on synchronized pulse edge
## This is a MULTI-BIT bus crossing that is synchronized by the pulse handshake
set_false_path -from [get_cells -hier -filter {NAME =~ *r_count_value*}] \
               -to   [get_cells -hier -filter {NAME =~ *r_display_count*}]

## Crossing #2: Pulse CDC (handled internally by sync_pulse module)
## The sync_pulse module uses proper dual-FF synchronizer
## Vivado will automatically handle these paths correctly via the synchronizer
## We add this constraint to document the intentional CDC
set_false_path -from [get_cells -hier -filter {NAME =~ *btn_increment_pulse*}] \
               -to   [get_cells -hier -filter {NAME =~ *sync_pulse/r_src_pulse*}]

## Synchronizer Constraints
## Mark all synchronizer flip-flops to prevent optimization
set_property ASYNC_REG TRUE [get_cells -hier -filter {NAME =~ *sync_pulse*/r_sync*}]
set_property ASYNC_REG TRUE [get_cells -hier -filter {NAME =~ *sync_2ff*/r_sync*}]

## Max Delay Constraints for CDC Paths
## Ensure proper setup time for synchronizers (conservative)
set_max_delay -datapath_only -from [get_clocks btn_clk] -to [get_clocks disp_clk] 5.000
set_max_delay -datapath_only -from [get_clocks disp_clk] -to [get_clocks btn_clk] 5.000

##==============================================================================
## Input Delay Constraints
##==============================================================================

## Button inputs are asynchronous (no input delay constraint needed)
## Buttons go directly to synchronizers/debouncers

set_input_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports btnC]
set_input_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports btnU]

## Mark button inputs as asynchronous to sys_clk
set_false_path -from [get_ports btnC] -to [get_clocks sys_clk_pin]
set_false_path -from [get_ports btnU] -to [get_clocks sys_clk_pin]

##==============================================================================
## Output Delay Constraints
##==============================================================================

## 7-segment display outputs (relaxed timing, human-visible)
set_output_delay -clock [get_clocks disp_clk] 2.000 [get_ports {seg[*]}]
set_output_delay -clock [get_clocks disp_clk] 2.000 [get_ports {an[*]}]

## LED outputs (no critical timing)
set_output_delay -clock [get_clocks btn_clk] 0.000 [get_ports {led[0]}]
set_output_delay -clock [get_clocks disp_clk] 0.000 [get_ports {led[1]}]

##==============================================================================
## Physical Constraints
##==============================================================================

## Configuration Settings
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]

## Bitstream Settings
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]

##==============================================================================
## Design Rule Constraints
##==============================================================================

## Allow multi-cycle paths for slow clock domains (optional optimization)
## Button clock is very slow (10Hz) - give it multiple cycles to settle
set_multicycle_path -setup 2 -from [get_clocks btn_clk] -to [get_clocks btn_clk]
set_multicycle_path -hold 1  -from [get_clocks btn_clk] -to [get_clocks btn_clk]

## Display clock (1kHz) can also have relaxed timing
set_multicycle_path -setup 2 -from [get_clocks disp_clk] -to [get_clocks disp_clk]
set_multicycle_path -hold 1  -from [get_clocks disp_clk] -to [get_clocks disp_clk]

##==============================================================================
## Verification Constraints
##==============================================================================

## Report CDC violations (for verification)
## Run: report_cdc -file cdc_report.txt

## Report clock interaction (for debugging)
## Run: report_clock_interaction -file clock_interaction.txt

##==============================================================================
## Notes for Users
##==============================================================================
## 1. This design uses proper CDC techniques - all clock crossings are safe
## 2. Button inputs are asynchronous - debouncing handles metastability
## 3. Generated clocks (btn_clk, disp_clk) are derived from sys_clk
## 4. False paths are explicitly documented for each CDC crossing
## 5. ASYNC_REG property prevents optimization of synchronizer chains
## 6. Max delay constraints ensure proper synchronizer operation
##
## Verification Commands:
##   check_timing -verbose
##   report_cdc -details -verbose
##   report_clock_interaction -delay_type min_max
##==============================================================================
