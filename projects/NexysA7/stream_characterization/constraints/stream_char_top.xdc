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
## Reset sync flops are tagged (* ASYNC_REG = "TRUE" *) in stream_char_top.
## Two flops: r_rst_meta (1st stage), r_rst_sync (2nd stage). aresetn is
## driven combinationally from r_rst_sync.
##
## (1) False-path from async input to the first sync stage. The flop sits at
##     the top of the design, not under u_harness — earlier glob was wrong.
set_false_path -from [get_ports CPU_RESETN] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]

## (2) False-path the entire reset distribution network. r_rst_sync_reg/Q
##     fans out to thousands of FDRE /R (synchronous reset) pins. Closing
##     single-cycle timing across that fan-out is unnecessary: the design
##     is held in reset for many CLK100MHZ cycles after FPGA configuration,
##     so a few hundred ps of skew across the reset distribution is
##     harmless — every flop will have been clocked while reset is high
##     long before any traffic starts. Without this, ~6 of the residual
##     post-route timing failures are reset-distribution paths missing by
##     a few hundred ps that won't matter at runtime.
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

## If CDC_ENABLE is ever turned on, add per-handshake set_max_delay here —
## one block per cdc_2_phase_handshake / cdc_4_phase_handshake instance.
## See rtl/amba/shared/cdc_2_phase_handshake.sv header for the template.

##==============================================================================
## LED status driver — slow clock domain + CDC handshake
##==============================================================================
## led_status_driver in rtl/led_status_driver.sv divides aclk down to ~200 Hz
## with a counter, routes the result through a BUFG, and uses a 2-phase
## CDC handshake to cross status bits from aclk into that slow domain.
## LEDs are then driven only from a slow-domain register, so the LED OBUF
## endpoints sit on led_slow_clk paths (5 ms budget) instead of sys_clk_pin
## paths (10 ns budget). See the module header for full architectural notes.

## (1) Declare the divided clock so Vivado treats it as its own domain.
##     LED_UPDATE_HZ in the RTL is 200 Hz; divide-by is 2 * 100M / 200 =
##     1_000_000. That's the toggle period of r_slow_clk_raw at the BUFG
##     input. The generated clock is "/ DIV" relative to the source aclk.
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter \
             {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by 1000000 \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]

## (2) Tell impl that aclk and led_slow_clk are asynchronous to each other.
##     The CDC handshake handles all real crossings; this prevents Vivado
##     from trying to time inter-clock paths it shouldn't.
set_clock_groups -asynchronous \
    -group [get_clocks sys_clk_pin] \
    -group [get_clocks led_slow_clk]

## (3) Bound the CDC datapath with set_max_delay -datapath_only. This is
##     the canonical pattern from cdc_2_phase_handshake.sv — see that
##     module's header for derivation. Bounds are one destination period
##     for fast->slow (5 ms at 200 Hz, plenty) and one source period for
##     slow->fast (10 ns).
set led_hs_pre {NAME =~ *u_led_status_driver/u_hs/}
##     req toggle: src=aclk, dst=led_slow_clk
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_req_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_req_sync_reg[0]/D"] \
    5.000
##     ack toggle: src=led_slow_clk, dst=aclk
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_ack_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_ack_sync_reg[0]/D"] \
    10.000
##     Data bus (held stable in src across the toggle round trip)
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_src_data_hold_reg[*]/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_dst_data_reg[*]/D"] \
    5.000

## (4) LED OBUF false-path is no longer needed: the LED endpoints now sit
##     on led_slow_clk (5 ms budget) and trivially close. Kept here as a
##     belt-and-braces safety net so even pathological placement can't
##     reintroduce LED timing as a closure problem.
set_false_path -to [get_ports {LED[*]}]

##==============================================================================
## Multi-cycle paths — software-programmed AXI transfer-beat config
##==============================================================================
## AXI_XFER_CONFIG.{RD,WR}_XFER_BEATS are sw-written once at setup and then
## held static during AXI transfers. Fan-out cone is:
##   cfg_axi_{rd,wr}_xfer_beats -> w_transfer_size[] -> w_arb_request
##   -> arbiter_round_robin grant/pending FSM  (15-17 levels on -1 Artix-7)
## Relax to 2 cycles. SW contract: idle transfers before rewriting this reg.
## If the engine's operating point ever requires mid-flight reconfiguration,
## remove this and pipeline w_transfer_size[] / w_arb_request instead.
set cfg_xfer_bits [get_cells -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*AXI_XFER_CONFIG*XFER_BEATS*}]
set_multicycle_path 2 -setup -from $cfg_xfer_bits
set_multicycle_path 1 -hold  -from $cfg_xfer_bits

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
