##==============================================================================
## Nexys A7-100T Constraints — STREAM Characterization Harness
##==============================================================================
## Board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
## Top:   stream_char_top
## Pin table copied from the Digilent Nexys A7 master XDC (identical board /
## pinout to the RAPIDS characterization flow, whose XDC this file is derived
## from -- same clock, reset, UART, LED, and 7-seg pins, same CDC structure).
##
## NOTE: This file constrains the board I/O + reset synchronizer + LED slow-
## clock CDC. STREAM-DUT-internal timing exceptions (monitor-CAM pblocks,
## multicycle/false paths for the observer cones) are deliberately NOT included
## here; they are added during actual place-and-route once post-route timing
## reports identify the offending cones.
##==============================================================================

##==============================================================================
## Primary Clock
##==============================================================================
## 100 MHz oscillator on E3
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports CLK100MHZ]

##==============================================================================
## Reset Button (CPU_RESETN — active-low per top module)
##==============================================================================
set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]

## Reset is asynchronous — don't waste timing effort on it. Port-based (not
## clock-qualified) so it still matches when the derate MMCM renames the
## harness domain clk_unbuf.
set_input_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports CPU_RESETN]
set_false_path -from [get_ports CPU_RESETN]

##==============================================================================
## USB UART (FTDI chip — FT2232HQ)
##==============================================================================
## UART_TXD_IN  — FTDI → FPGA serial in  (pin C4)
## UART_RXD_OUT — FPGA → FTDI serial out (pin D4)
set_property -dict {PACKAGE_PIN C4 IOSTANDARD LVCMOS33} [get_ports UART_TXD_IN]
set_property -dict {PACKAGE_PIN D4 IOSTANDARD LVCMOS33} [get_ports UART_RXD_OUT]

## UART is async at 115.2 kbaud — timing is relaxed. Port-based false paths
## (NOT clock-qualified): when the harness clock runs through the derate MMCM
## its domain is named clk_unbuf, not sys_clk_pin, and a clock-qualified false
## path silently stops matching -- measured as a -1.561 ns inter-clock hit on
## UART_RXD_OUT in the 75 MHz build.
set_input_delay  -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_TXD_IN]
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_RXD_OUT]
set_false_path -from [get_ports UART_TXD_IN]
set_false_path -to   [get_ports UART_RXD_OUT]

##==============================================================================
## LEDs (16 user LEDs)
##==============================================================================
## Top uses LED[3:0] as live status ([0] irq [1] error [2] trace_overflow
## [3] heartbeat) and the full bank as the 0x0123/0x9999 PASS/FAIL ladder.
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
## 7-segment displays (8 multiplexed digits; we drive only AN[3:0]).
## Pins from Digilent Nexys A7-100T master XDC.
##==============================================================================
set_property -dict {PACKAGE_PIN T10 IOSTANDARD LVCMOS33} [get_ports CA]
set_property -dict {PACKAGE_PIN R10 IOSTANDARD LVCMOS33} [get_ports CB]
set_property -dict {PACKAGE_PIN K16 IOSTANDARD LVCMOS33} [get_ports CC]
set_property -dict {PACKAGE_PIN K13 IOSTANDARD LVCMOS33} [get_ports CD]
set_property -dict {PACKAGE_PIN P15 IOSTANDARD LVCMOS33} [get_ports CE]
set_property -dict {PACKAGE_PIN T11 IOSTANDARD LVCMOS33} [get_ports CF]
set_property -dict {PACKAGE_PIN L18 IOSTANDARD LVCMOS33} [get_ports CG]
set_property -dict {PACKAGE_PIN H15 IOSTANDARD LVCMOS33} [get_ports DP]

set_property -dict {PACKAGE_PIN J17 IOSTANDARD LVCMOS33} [get_ports {AN[0]}]
set_property -dict {PACKAGE_PIN J18 IOSTANDARD LVCMOS33} [get_ports {AN[1]}]
set_property -dict {PACKAGE_PIN T9  IOSTANDARD LVCMOS33} [get_ports {AN[2]}]
set_property -dict {PACKAGE_PIN J14 IOSTANDARD LVCMOS33} [get_ports {AN[3]}]
set_property -dict {PACKAGE_PIN P14 IOSTANDARD LVCMOS33} [get_ports {AN[4]}]
set_property -dict {PACKAGE_PIN T14 IOSTANDARD LVCMOS33} [get_ports {AN[5]}]
set_property -dict {PACKAGE_PIN K2  IOSTANDARD LVCMOS33} [get_ports {AN[6]}]
set_property -dict {PACKAGE_PIN U13 IOSTANDARD LVCMOS33} [get_ports {AN[7]}]

## Multiplexed at 1 kHz (250 Hz / digit), human-visible — no need to close
## tight timing on the cathode/anode driver flops.
set_false_path -to [get_ports {AN[*] CA CB CC CD CE CF CG DP}]

##==============================================================================
## CDC / Reset-synchronizer constraints
##==============================================================================
## Reset sync flops are tagged (* ASYNC_REG = "TRUE" *) in stream_char_top.
## Two flops: r_rst_meta (1st stage), r_rst_sync (2nd stage). aresetn is
## driven combinationally from r_rst_sync.
##
## (1) False-path from async input to the first sync stage.
set_false_path -from [get_ports CPU_RESETN] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]

## (2) False-path the entire reset distribution network. r_rst_sync_reg/Q
##     fans out to thousands of synchronous-reset pins. The design is held in
##     reset for many CLK100MHZ cycles after configuration, so a few hundred ps
##     of skew across the reset fan-out is harmless.
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

##==============================================================================
## LED status driver — slow clock domain + CDC handshake
##==============================================================================
## led_status_driver divides aclk to ~200 Hz through a BUFG and crosses the
## status word via cdc_2_phase_handshake. LED OBUFs then sit on the slow
## generated clock (5 ms budget) rather than sys_clk_pin (10 ns budget).
##
## Harness clock: 100 MHz default (CLK100MHZ direct). A derated build
## (A7_CLK_MHZ=75 etc.) exports HARNESS_CLK_HZ so the divide and the fast-leg
## max_delay follow the actual aclk. The slow period is constant: the divide
## count retargets to hold LED_UPDATE_HZ at 200.

set hclk_hz [expr {[info exists ::env(HARNESS_CLK_HZ)] ? $::env(HARNESS_CLK_HZ) : 100000000}]
set led_div [expr {2 * $hclk_hz / 200}]

## (1) Declare the divided clock at the BUFG input divide.
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter \
             {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by $led_div \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]

## (2) aclk and led_slow_clk are asynchronous. The CDC handshake handles all
##     real crossings; this stops Vivado timing paths it shouldn't.
set_clock_groups -asynchronous \
    -group [get_clocks sys_clk_pin] \
    -group [get_clocks led_slow_clk]

## (3) Bound the CDC datapath with set_max_delay -datapath_only (canonical
##     cdc_2_phase_handshake pattern). fast->slow uses the slow period (5 ms),
##     slow->fast uses the fast period (10 ns).
set led_hs_pre {NAME =~ *u_led_status_driver/u_hs/}
##     req toggle: src=aclk, dst=led_slow_clk
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_req_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_req_sync_reg[0]/D"] \
    5.000
##     ack toggle: src=led_slow_clk, dst=aclk (fast period follows hclk_hz)
set fast_period_ns [format %.3f [expr {1.0e9 / double($hclk_hz)}]]
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_ack_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_ack_sync_reg[0]/D"] \
    $fast_period_ns
##     Data bus (held stable in src across the toggle round trip)
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_src_data_hold_reg[*]/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_dst_data_reg[*]/D"] \
    5.000

## (4) Belt-and-braces LED OBUF false-path (endpoints already on led_slow_clk).
set_false_path -to [get_ports {LED[*]}]

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
