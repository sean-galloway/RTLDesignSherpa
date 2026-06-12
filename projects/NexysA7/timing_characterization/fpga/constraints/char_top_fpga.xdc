##==============================================================================
## char_top_fpga.xdc — Digilent Nexys A7-100T pin map
##==============================================================================
## Board:  Digilent Nexys A7-100T (xc7a100tcsg324-1)
## Top:    char_top_fpga
## Source: Nexys A7 master XDC, trimmed to clk + reset button + 4 SW + 8 LED
##==============================================================================

## 100 MHz onboard oscillator
set_property -dict { PACKAGE_PIN E3   IOSTANDARD LVCMOS33 } [get_ports { CLK100MHZ }]
create_clock -add -name sys_clk_pin -period 10.000 -waveform {0 5} [get_ports { CLK100MHZ }]

## CPU reset push-button (active-low)
set_property -dict { PACKAGE_PIN C12  IOSTANDARD LVCMOS33 } [get_ports { CPU_RESETN }]

## User switches SW0..SW3 (seed lower nibble)
set_property -dict { PACKAGE_PIN J15  IOSTANDARD LVCMOS33 } [get_ports { SW[0] }]
set_property -dict { PACKAGE_PIN L16  IOSTANDARD LVCMOS33 } [get_ports { SW[1] }]
set_property -dict { PACKAGE_PIN M13  IOSTANDARD LVCMOS33 } [get_ports { SW[2] }]
set_property -dict { PACKAGE_PIN R15  IOSTANDARD LVCMOS33 } [get_ports { SW[3] }]

## User LEDs LD0..LD7 (per-FUB XOR-reduce observation)
set_property -dict { PACKAGE_PIN H17  IOSTANDARD LVCMOS33 } [get_ports { LED[0] }]
set_property -dict { PACKAGE_PIN K15  IOSTANDARD LVCMOS33 } [get_ports { LED[1] }]
set_property -dict { PACKAGE_PIN J13  IOSTANDARD LVCMOS33 } [get_ports { LED[2] }]
set_property -dict { PACKAGE_PIN N14  IOSTANDARD LVCMOS33 } [get_ports { LED[3] }]
set_property -dict { PACKAGE_PIN R18  IOSTANDARD LVCMOS33 } [get_ports { LED[4] }]
set_property -dict { PACKAGE_PIN V17  IOSTANDARD LVCMOS33 } [get_ports { LED[5] }]
set_property -dict { PACKAGE_PIN U17  IOSTANDARD LVCMOS33 } [get_ports { LED[6] }]
set_property -dict { PACKAGE_PIN U16  IOSTANDARD LVCMOS33 } [get_ports { LED[7] }]

## Configuration / bitstream cleanup
set_property CONFIG_VOLTAGE 3.3   [current_design]
set_property CFGBVS         VCCO  [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLUP [current_design]
