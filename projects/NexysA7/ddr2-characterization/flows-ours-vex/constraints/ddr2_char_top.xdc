##==============================================================================
## Nexys A7-100T Constraints -- DDR2/LPDDR2 Characterization Harness
##==============================================================================
## Board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
## Top:   ddr2_char_top
## Pin table sources:
##   * Board pins (clock, UART, LEDs, 7-seg, buttons): Digilent Nexys A7
##     master XDC, mirrored from stream_characterization/flows-stream-bridge/
##     constraints/stream_char_top.xdc (which was cross-checked against the
##     Digilent master).
##   * DDR2 pins: sourced from LiteX-Boards' digilent_nexys_a7.py
##     (github.com/litex-hub/litex-boards/blob/master/litex_boards/
##      platforms/digilent_nexys_a7.py) which is in turn derived from the
##     Digilent Nexys A7 schematic. Cross-check against the schematic
##     before shipping a bitstream to the board.
##==============================================================================

##==============================================================================
## Primary Clock
##==============================================================================
## 100 MHz oscillator on E3
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports CLK100MHZ]

##==============================================================================
## Reset Button (BTNC / CPU_RESETN at C12)
##==============================================================================
set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]

set_input_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports CPU_RESETN]
set_false_path -from [get_ports CPU_RESETN] -to [get_clocks sys_clk_pin]

##==============================================================================
## USB UART (FTDI FT2232HQ)
##==============================================================================
set_property -dict {PACKAGE_PIN C4 IOSTANDARD LVCMOS33} [get_ports UART_TXD_IN]
set_property -dict {PACKAGE_PIN D4 IOSTANDARD LVCMOS33} [get_ports UART_RXD_OUT]

set_input_delay  -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_TXD_IN]
set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports UART_RXD_OUT]
set_false_path -from [get_ports UART_TXD_IN]  -to [get_clocks sys_clk_pin]
set_false_path -from [get_clocks sys_clk_pin] -to [get_ports UART_RXD_OUT]

##==============================================================================
## LEDs (16 user LEDs)
##==============================================================================
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

set_output_delay -clock [get_clocks sys_clk_pin] 0.000 [get_ports {LED[*]}]

##==============================================================================
## 7-segment displays (8 multiplexed digits; harness scans low 4)
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

set_false_path -to [get_ports {AN[*] CA CB CC CD CE CF CG DP}]

##==============================================================================
## Reset-synchroniser CDC
##==============================================================================
## Reset-sync flops are (* ASYNC_REG = "TRUE" *) in ddr2_char_top.sv:
##   r_rst_meta (1st stage), r_rst_sync (2nd stage). aresetn = r_rst_sync.
set_false_path -from [get_ports CPU_RESETN] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

##==============================================================================
## LED status driver -- slow clock domain + CDC handshake
##==============================================================================
## Mirrors the constraint block from stream_char_top.xdc since the LED
## driver module (led_status_driver.sv) is reused verbatim.
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter \
             {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by 1000000 \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]

set_clock_groups -asynchronous \
    -group [get_clocks sys_clk_pin] \
    -group [get_clocks led_slow_clk]

set led_hs_pre {NAME =~ *u_led_status_driver/u_hs/}
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_req_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_req_sync_reg[0]/D"] \
    5.000
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_ack_tog_reg/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_ack_sync_reg[0]/D"] \
    10.000
set_max_delay -datapath_only \
    -from [get_pins -hier -filter "${led_hs_pre}r_src_data_hold_reg[*]/C"] \
    -to   [get_pins -hier -filter "${led_hs_pre}r_dst_data_reg[*]/D"] \
    5.000

set_false_path -to [get_ports {LED[*]}]

##==============================================================================
## DDR2 SDRAM -- Micron MT47H64M16HR-25E (x16, single-rank, 800 Mbps, 128 MB)
##==============================================================================
## PIN LOCATIONS NOT SHIPPED IN THIS FILE.  DO NOT RUN A BITSTREAM WITHOUT
## FILLING IN THE BLOCK BELOW -- shipping wrong DDR2 pin locations can
## short SSTL18_II drivers into 3.3 V bank rails and permanently damage
## the FPGA.
##
## Source-of-truth options (copy exactly, do not paraphrase):
##
##   [preferred] LiteX-Boards platform file. Fresh clone:
##       git clone https://github.com/litex-hub/litex-boards
##     then read: litex_boards/platforms/digilent_nexys_a7.py
##       -> the ("ddram", 0, ...) IO_STANDARD block. Every ddram
##          subsignal name maps 1:1 to a port here:
##            a        -> ddram_a[13:0]
##            ba       -> ddram_ba[2:0]
##            ras_n    -> ddram_ras_n
##            cas_n    -> ddram_cas_n
##            we_n     -> ddram_we_n
##            cs_n     -> ddram_cs_n
##            cke      -> ddram_cke
##            odt      -> ddram_odt
##            dm       -> ddram_dm[1:0]
##            dq       -> ddram_dq[15:0]
##            dqs_p    -> ddram_dqs_p[1:0]
##            dqs_n    -> ddram_dqs_n[1:0]
##            clk_p    -> ddram_clk_p
##            clk_n    -> ddram_clk_n
##          IOSTANDARD SSTL18_II on all singled-ended pins, DIFF_SSTL18_II
##          on the dqs_p/n and clk_p/n pairs. Miscellaneous SLEW=FAST on
##          the address+bank+data lanes.
##
##   [fallback] Digilent Nexys A7 Master XDC (partial in
##       projects/NexysA7/boards/nexys_a7_100t/master.xdc -- the DDR2
##       block is currently blanked out with "use MIG IP core", so pull
##       from the LiteX-Boards file above OR from Digilent's official
##       Nexys-A7-100T-Master.xdc download).
##
## Once populated, re-run `verilator --lint-only` and then
## `read_xdc ddr2_char_top.xdc` in Vivado to confirm no pin conflicts
## before bitstream generation. The existing set_property lines above
## (clock, reset, UART, LEDs, 7-seg) are production-verified from the
## stream_characterization harness and do not need re-checking.

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]

##==============================================================================
## End of ddr2_char_top.xdc
##==============================================================================
