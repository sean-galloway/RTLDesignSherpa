##==============================================================================
## Nexys A7-100T Constraints — STREAM Characterization Harness
##==============================================================================
## Board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
## Top:   stream_char_top
## Pin table copied from the Digilent Nexys A7 master XDC.
## Host interface: single USB-UART link (115200 8N1 via FTDI).
##==============================================================================

##==============================================================================
## Primary Clock
##==============================================================================
## 100 MHz oscillator on E3
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports CLK100MHZ]

##==============================================================================
## Reset Button (BTNC — center pushbutton, active-low per top module)
##==============================================================================
## NOTE: the Nexys A7 master XDC labels the center button as btnC on E16.
## stream_char_top ties the top-level reset to CPU_RESETN which is C12 on
## older Nexys 4 DDR boards; on the A7-100T silkscreen the same pin is still
## C12 but labelled as the CPU_RESETN button at the top-right of the board.
set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]

## Reset is asynchronous — don't waste timing effort on it.
set_input_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports CPU_RESETN]
set_false_path -from [get_ports CPU_RESETN] -to [get_clocks sys_clk_pin]

##==============================================================================
## USB UART (FTDI chip — FT2232HQ)
##==============================================================================
## UART_TXD_IN  — FTDI → FPGA serial in  (pin C4)
## UART_RXD_OUT — FPGA → FTDI serial out (pin D4)
set_property -dict {PACKAGE_PIN C4 IOSTANDARD LVCMOS33} [get_ports UART_TXD_IN]
set_property -dict {PACKAGE_PIN D4 IOSTANDARD LVCMOS33} [get_ports UART_RXD_OUT]

## UART is async at 115.2 kbaud — timing is relaxed. Flag as async to sys_clk.
set_input_delay  -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_TXD_IN]
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_RXD_OUT]
set_false_path -from [get_ports UART_TXD_IN]  -to [get_clocks sys_clk_pin]
set_false_path -from [get_clocks sys_clk_pin] -to [get_ports UART_RXD_OUT]

##==============================================================================
## LEDs (16 user LEDs)
##==============================================================================
## Top uses LED[0..3] as status; [4..15] reserved for scratch / debug.
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {LED[0]}]
set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {LED[1]}]
set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports {LED[2]}]
set_property -dict {PACKAGE_PIN N14 IOSTANDARD LVCMOS33} [get_ports {LED[3]}]
set_property -dict {PACKAGE_PIN R18 IOSTANDARD LVCMOS33} [get_ports {LED[4]}]
set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports {LED[5]}]
set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports {LED[6]}]
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {LED[7]}]
set_property -dict {PACKAGE_PIN V16 IOSTANDARD LVCMOS33} [get_ports {LED[8]}]
set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS33} [get_ports {LED[9]}]
set_property -dict {PACKAGE_PIN U14 IOSTANDARD LVCMOS33} [get_ports {LED[10]}]
set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports {LED[11]}]
set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS33} [get_ports {LED[12]}]
set_property -dict {PACKAGE_PIN V14 IOSTANDARD LVCMOS33} [get_ports {LED[13]}]
set_property -dict {PACKAGE_PIN V12 IOSTANDARD LVCMOS33} [get_ports {LED[14]}]
set_property -dict {PACKAGE_PIN V11 IOSTANDARD LVCMOS33} [get_ports {LED[15]}]

## LED timing is human-visible; no input/output delay worth specifying.
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports {LED[*]}]

##==============================================================================
## CDC / Reset-synchronizer constraints
##==============================================================================
## Reset sync flops are tagged (* ASYNC_REG = "TRUE" *) in RTL. Add the
## false-path from the async reset input to the first sync stage so Vivado
## doesn't try to close timing on a path that's intentionally async.
set_false_path -from [get_ports CPU_RESETN] \
               -to   [get_pins -hier -filter {NAME =~ *u_harness*r_rst_meta_reg/D}]

## If CDC_ENABLE is ever turned on, add per-handshake set_max_delay here —
## one block per cdc_2_phase_handshake / cdc_4_phase_handshake instance.
## See rtl/amba/shared/cdc_2_phase_handshake.sv header for the template.

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
