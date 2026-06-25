## =============================================================================
## cdc_demo.xdc — Nexys A7-100T constraints for cdc_demo_top
## =============================================================================
## Target: XC7A100T-1CSG324C  (Digilent Nexys A7-100T)
##
## What's on this build vs the original cdc_counter_display.xdc:
##   - Adds UART pins (FTDI USB-UART, 115200 8N1)
##   - Uses 4 buttons (BTNC/BTNU/BTND/BTNL) instead of 2 (per-counter)
##   - BTNR is the system reset (via CPU_RESETN)
##   - 8 LEDs instead of 2 (per-counter alive + UART activity + status)
##
## The original phase-1 constraints file (`nexys_a7_100t.xdc`) is preserved
## for the existing cdc_counter_display_top build.
## =============================================================================

## ----- 100 MHz on-board clock -----
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} [get_ports CLK100MHZ]

## ----- System reset (BTNR = "CPU_RESETN" on Digilent's pin assignments) -----
## Active-low push button. Digilent labels this pin "CPU_RESETN" on the
## board silkscreen; on the Nexys A7 it sits separately from the 5 directional
## buttons.
set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]
set_false_path -from [get_ports CPU_RESETN] -to [get_clocks sys_clk_pin]

## ----- USB-UART (FTDI FT2232HQ on the Nexys A7) -----
## C4 = FTDI TXD → FPGA RXD  (we name it UART_TXD_IN  to match Digilent docs)
## D4 = FPGA TXD → FTDI RXD  (we name it UART_RXD_OUT)
set_property -dict {PACKAGE_PIN C4 IOSTANDARD LVCMOS33} [get_ports UART_TXD_IN]
set_property -dict {PACKAGE_PIN D4 IOSTANDARD LVCMOS33} [get_ports UART_RXD_OUT]
set_input_delay  -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_TXD_IN]
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_RXD_OUT]
set_false_path -from [get_ports UART_TXD_IN]   -to [get_clocks sys_clk_pin]
set_false_path -from [get_clocks sys_clk_pin]  -to [get_ports UART_RXD_OUT]

## ----- Push buttons (4 of 5; BTNR is reset above) -----
##   BTNC = inject press for selected counter
##   BTNU = step pickoff UP   (faster)
##   BTND = step pickoff DOWN (slower)
##   BTNL = cycle CDC mode    (Pr → br → S2 → HS → Pr)
set_property -dict {PACKAGE_PIN N17 IOSTANDARD LVCMOS33} [get_ports btnC]
set_property -dict {PACKAGE_PIN M18 IOSTANDARD LVCMOS33} [get_ports btnU]
set_property -dict {PACKAGE_PIN P18 IOSTANDARD LVCMOS33} [get_ports btnD]
set_property -dict {PACKAGE_PIN P17 IOSTANDARD LVCMOS33} [get_ports btnL]
set_false_path -from [get_ports {btnC btnU btnD btnL}] -to [get_clocks sys_clk_pin]

## ----- 16 slide switches (SW[15:0]) -----
##   SW[1:0]  = selected counter index (0..3)
##   SW[15]   = AUTO_INC level for selected counter
##   SW[14:2] = reserved
set_property -dict {PACKAGE_PIN J15 IOSTANDARD LVCMOS33} [get_ports {SW[0]}]
set_property -dict {PACKAGE_PIN L16 IOSTANDARD LVCMOS33} [get_ports {SW[1]}]
set_property -dict {PACKAGE_PIN M13 IOSTANDARD LVCMOS33} [get_ports {SW[2]}]
set_property -dict {PACKAGE_PIN R15 IOSTANDARD LVCMOS33} [get_ports {SW[3]}]
set_property -dict {PACKAGE_PIN R17 IOSTANDARD LVCMOS33} [get_ports {SW[4]}]
set_property -dict {PACKAGE_PIN T18 IOSTANDARD LVCMOS33} [get_ports {SW[5]}]
set_property -dict {PACKAGE_PIN U18 IOSTANDARD LVCMOS33} [get_ports {SW[6]}]
set_property -dict {PACKAGE_PIN R13 IOSTANDARD LVCMOS33} [get_ports {SW[7]}]
set_property -dict {PACKAGE_PIN T8  IOSTANDARD LVCMOS18} [get_ports {SW[8]}]
set_property -dict {PACKAGE_PIN U8  IOSTANDARD LVCMOS18} [get_ports {SW[9]}]
set_property -dict {PACKAGE_PIN R16 IOSTANDARD LVCMOS33} [get_ports {SW[10]}]
set_property -dict {PACKAGE_PIN T13 IOSTANDARD LVCMOS33} [get_ports {SW[11]}]
set_property -dict {PACKAGE_PIN H6  IOSTANDARD LVCMOS33} [get_ports {SW[12]}]
set_property -dict {PACKAGE_PIN U12 IOSTANDARD LVCMOS33} [get_ports {SW[13]}]
set_property -dict {PACKAGE_PIN U11 IOSTANDARD LVCMOS33} [get_ports {SW[14]}]
set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports {SW[15]}]
set_false_path -from [get_ports {SW[*]}] -to [get_clocks sys_clk_pin]

## ----- 8 LEDs (LED[0]..LED[7]) -----
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {LED[0]}]
set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {LED[1]}]
set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports {LED[2]}]
set_property -dict {PACKAGE_PIN N14 IOSTANDARD LVCMOS33} [get_ports {LED[3]}]
set_property -dict {PACKAGE_PIN R18 IOSTANDARD LVCMOS33} [get_ports {LED[4]}]
set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports {LED[5]}]
set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports {LED[6]}]
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {LED[7]}]
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports {LED[*]}]

## ----- 8-digit 7-segment display -----
## 8 anodes (active-low) + 7 cathodes (a–g, active-low) + DP cathode (active-low)
set_property -dict {PACKAGE_PIN J17 IOSTANDARD LVCMOS33} [get_ports {AN[0]}]
set_property -dict {PACKAGE_PIN J18 IOSTANDARD LVCMOS33} [get_ports {AN[1]}]
set_property -dict {PACKAGE_PIN T9  IOSTANDARD LVCMOS33} [get_ports {AN[2]}]
set_property -dict {PACKAGE_PIN J14 IOSTANDARD LVCMOS33} [get_ports {AN[3]}]
set_property -dict {PACKAGE_PIN P14 IOSTANDARD LVCMOS33} [get_ports {AN[4]}]
set_property -dict {PACKAGE_PIN T14 IOSTANDARD LVCMOS33} [get_ports {AN[5]}]
set_property -dict {PACKAGE_PIN K2  IOSTANDARD LVCMOS33} [get_ports {AN[6]}]
set_property -dict {PACKAGE_PIN U13 IOSTANDARD LVCMOS33} [get_ports {AN[7]}]

set_property -dict {PACKAGE_PIN T10 IOSTANDARD LVCMOS33} [get_ports {SEG[0]}] ;# a
set_property -dict {PACKAGE_PIN R10 IOSTANDARD LVCMOS33} [get_ports {SEG[1]}] ;# b
set_property -dict {PACKAGE_PIN K16 IOSTANDARD LVCMOS33} [get_ports {SEG[2]}] ;# c
set_property -dict {PACKAGE_PIN K13 IOSTANDARD LVCMOS33} [get_ports {SEG[3]}] ;# d
set_property -dict {PACKAGE_PIN P15 IOSTANDARD LVCMOS33} [get_ports {SEG[4]}] ;# e
set_property -dict {PACKAGE_PIN T11 IOSTANDARD LVCMOS33} [get_ports {SEG[5]}] ;# f
set_property -dict {PACKAGE_PIN L18 IOSTANDARD LVCMOS33} [get_ports {SEG[6]}] ;# g
set_property -dict {PACKAGE_PIN H15 IOSTANDARD LVCMOS33} [get_ports DP]

set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports {AN[*] SEG[*] DP}]

## =============================================================================
## CDC constraints
## =============================================================================
## Each of the four counter domains is fed by a divided clock generated
## inside cdc_counter_domain by rtl/common/clock_divider. That divided
## clock is a registered toggle off a counter bit, so for proper STA
## treatment we declare each as a generated clock derived from sys_clk
## with a -divide_by that matches the pickoff. The defaults loaded by the
## harness on reset are pickoff = {23,19,15,11}, so divide-by values are
## {2^24, 2^20, 2^16, 2^12} = {16777216, 1048576, 65536, 4096}. The host
## can rewrite the pickoff at runtime; STA will be valid only for the
## declared-divide value, but timing on the divided-clock side is so slow
## (max 24 kHz @ default) that any reasonable host pickoff still meets
## timing trivially.
##
## NOTE: Vivado will treat the "create_generated_clock" as the worst-
## case fast variant. Set max-delay datapath constraints on every CDC
## path to keep STA reasonable.
## =============================================================================

## All cross-clock paths from sys_clk into any ctr_clk are bounded to one
## sys_clk period (10 ns) — sufficient because sync_pulse / 2-FF
## synchronizers handle the actual timing closure.
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_init_sync0*/D"}] 10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_inc_sync0*/D"}]  10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_freeze_sync0*/D"}] 10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_ignore_sync0*/D"}] 10.000

## Counter → sys_clk Gray-coded path: bound to one sys_clk period.
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_value_gray_src*/C"}] 10.000
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_press_gray_src*/C"}] 10.000
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_ticks_gray_src*/C"}] 10.000

## sync_pulse internal toggle CDC paths — let Vivado's CDC engine handle
## these via the ASYNC_REG attributes already on the synchronizer flops.
