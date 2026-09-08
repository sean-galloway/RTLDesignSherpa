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
## CDC constraints (v3 — MMCM-derived clocks + per-counter BUFGMUX tree)
## =============================================================================
## The MMCM creates four output clocks at co-prime divisors of 800 MHz
## VCO. Vivado auto-derives these from the MMCME2_BASE primitive — we
## don't need to declare them explicitly. Each MMCM output is buffered
## onto the global clock network with a BUFG.
##
## Per counter (4 instances), a BUFGMUX_CTRL tree selects one of:
##   idx 0: clk_mmcm_72m  (~72.7 MHz, MMCM CLKOUT0)
##   idx 1: clk_mmcm_27m  (~27.6 MHz, MMCM CLKOUT1)
##   idx 2: clk_mmcm_12m  (~11.9 MHz, MMCM CLKOUT2)
##   idx 3: clk_mmcm_6m   (~ 6.25 MHz, MMCM CLKOUT3)
##   idx 4: w_clk_div_bufg[i] (sys_clk-derived, runtime PICKOFF)
##
## Vivado treats the BUFGMUX_CTRL output as both possible input clocks
## (whichever is selected). STA will compute worst-case timing for each
## input → set_clock_groups -asynchronous covers cross-clock paths.
##
## All four MMCM outputs are async to each other (co-prime divisors →
## no shared edge alignment) AND async to sys_clk's divided clock.
## =============================================================================

## All four MMCM outputs are asynchronous to each other and to sys_clk.
## Vivado names them get_clocks clk_out1_<mmcm>, clk_out2_<mmcm>, etc.
## We use a name match pattern.
set_clock_groups -asynchronous \
    -group [get_clocks -include_generated_clocks sys_clk_pin] \
    -group [get_clocks -include_generated_clocks -of_objects [get_pins u_mmcm/CLKOUT0]] \
    -group [get_clocks -include_generated_clocks -of_objects [get_pins u_mmcm/CLKOUT1]] \
    -group [get_clocks -include_generated_clocks -of_objects [get_pins u_mmcm/CLKOUT2]] \
    -group [get_clocks -include_generated_clocks -of_objects [get_pins u_mmcm/CLKOUT3]]

## Per-counter divided clocks (one per counter) are derived from sys_clk
## by clock_divider. They live in the same clock group as sys_clk (all
## divide-by-2^N from the same root, so technically synchronous to it,
## but we still bound the CDC paths into ctr_clk with set_max_delay).
## Vivado auto-derives these as generated clocks from the clock_divider
## counter flop outputs.

## CDC paths from sys_clk into ctr_clk_*: per-bit synchronizer paths.
## Bounded to one sys_clk period (10 ns) — well within timing because the
## destination is on a slow divided clock or on a sub-100-MHz MMCM clock.
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_init_sync0*/D"}] 10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_inc_sync0*/D"}]  10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_freeze_sync0*/D"}] 10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_ignore_sync0*/D"}] 10.000
set_max_delay -datapath_only -from [get_clocks sys_clk_pin] \
    -to [get_pins -hier -filter {NAME =~ "*u_ctr*r_auto_sync0*/D"}] 10.000

## Counter → sys_clk Gray-coded path: bound to one sys_clk period.
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_value_gray_src*/C"}] 10.000
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_press_gray_src*/C"}] 10.000
set_max_delay -datapath_only -to [get_clocks sys_clk_pin] \
    -from [get_pins -hier -filter {NAME =~ "*u_ctr*r_ticks_gray_src*/C"}] 10.000

## sync_pulse, cdc_open_loop, cdc_2_phase_handshake, cdc_4_phase_handshake
## internal toggle CDC paths — these modules have ASYNC_REG attributes on
## the synchronizer flops and Vivado's CDC engine handles them through
## the set_clock_groups -asynchronous above. No additional constraints
## needed.
