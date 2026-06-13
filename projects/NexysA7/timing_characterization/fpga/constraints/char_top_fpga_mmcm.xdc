##==============================================================================
## char_top_fpga_mmcm.xdc — Nexys A7-100T pin map for the MMCM sweep wrapper
##==============================================================================
## Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
## Top:    char_top_fpga_mmcm
##
## Same pinout as char_top_fpga.xdc; adds generated-clock constraints on
## each MMCM output so Vivado STA reports per-test-clock WNS independently.
##==============================================================================

## 100 MHz onboard oscillator
set_property -dict { PACKAGE_PIN E3   IOSTANDARD LVCMOS33 } [get_ports { CLK100MHZ }]
create_clock -add -name sys_clk_pin -period 10.000 -waveform {0 5} [get_ports { CLK100MHZ }]

## CPU reset push-button (active-low)
set_property -dict { PACKAGE_PIN C12  IOSTANDARD LVCMOS33 } [get_ports { CPU_RESETN }]

## User switches SW0..SW3 (seed nibble + signature selector)
set_property -dict { PACKAGE_PIN J15  IOSTANDARD LVCMOS33 } [get_ports { SW[0] }]
set_property -dict { PACKAGE_PIN L16  IOSTANDARD LVCMOS33 } [get_ports { SW[1] }]
set_property -dict { PACKAGE_PIN M13  IOSTANDARD LVCMOS33 } [get_ports { SW[2] }]
set_property -dict { PACKAGE_PIN R15  IOSTANDARD LVCMOS33 } [get_ports { SW[3] }]

## User LEDs LD0..LD7
set_property -dict { PACKAGE_PIN H17  IOSTANDARD LVCMOS33 } [get_ports { LED[0] }]
set_property -dict { PACKAGE_PIN K15  IOSTANDARD LVCMOS33 } [get_ports { LED[1] }]
set_property -dict { PACKAGE_PIN J13  IOSTANDARD LVCMOS33 } [get_ports { LED[2] }]
set_property -dict { PACKAGE_PIN N14  IOSTANDARD LVCMOS33 } [get_ports { LED[3] }]
set_property -dict { PACKAGE_PIN R18  IOSTANDARD LVCMOS33 } [get_ports { LED[4] }]
set_property -dict { PACKAGE_PIN V17  IOSTANDARD LVCMOS33 } [get_ports { LED[5] }]
set_property -dict { PACKAGE_PIN U17  IOSTANDARD LVCMOS33 } [get_ports { LED[6] }]
set_property -dict { PACKAGE_PIN U16  IOSTANDARD LVCMOS33 } [get_ports { LED[7] }]

## MMCM-generated test clocks - declare them so Vivado treats each as its
## own clock domain and produces per-domain WNS in timing_summary.txt.
## Naming matches the LED roll-up: clk_test_0 .. clk_test_3.
create_generated_clock -name clk_test_0 -source [get_pins u_mmcm/CLKIN1] \
    -multiply_by 12 -divide_by 8 [get_pins u_mmcm/CLKOUT0]
create_generated_clock -name clk_test_1 -source [get_pins u_mmcm/CLKIN1] \
    -multiply_by 12 -divide_by 6 [get_pins u_mmcm/CLKOUT1]
create_generated_clock -name clk_test_2 -source [get_pins u_mmcm/CLKIN1] \
    -multiply_by 12 -divide_by 5 [get_pins u_mmcm/CLKOUT2]
create_generated_clock -name clk_test_3 -source [get_pins u_mmcm/CLKIN1] \
    -multiply_by 12 -divide_by 4 [get_pins u_mmcm/CLKOUT3]

## Mark the 100 MHz observation clock and each test clock as asynchronous
## to each other so the 2-flop CDC synchronisers inside sig_accum aren't
## false-pathed away.
set_clock_groups -asynchronous \
    -group [get_clocks sys_clk_pin] \
    -group [get_clocks clk_test_0]  \
    -group [get_clocks clk_test_1]  \
    -group [get_clocks clk_test_2]  \
    -group [get_clocks clk_test_3]

## Configuration / bitstream cleanup
set_property CONFIG_VOLTAGE 3.3   [current_design]
set_property CFGBVS         VCCO  [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLUP [current_design]
