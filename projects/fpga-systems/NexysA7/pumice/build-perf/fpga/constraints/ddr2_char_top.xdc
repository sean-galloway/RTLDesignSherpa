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

## UART is async serial — no meaningful I/O timing. Clock-agnostic false_paths
## (the FFs now run on the MMCM-generated sys clock, not sys_clk_pin directly,
## so the old clock-keyed false_paths no longer matched → spurious violations).
set_false_path -from [get_ports UART_TXD_IN]
set_false_path -to   [get_ports UART_RXD_OUT]

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
## VERIFIED Nexys A7-100T (== Nexys4 DDR) DDR2 pinout, banks 34/35, copied 1:1
## from litex-boards litex_boards/platforms/digilent_nexys4ddr.py ("ddram",0)
## block. SSTL18_II single-ended / DIFF_SSTL18_II differential; dq/dqs
## IN_TERM=UNTUNED_SPLIT_50; SLEW=FAST applied to the whole ddram group below.
##
## HARDWARE-SAFETY: correct for the Nexys A7-100T (xc7a100tcsg324) ONLY. A
## different board/part needs its own pinout -- wrong DDR2 LOCs can short
## SSTL18_II drivers into 3.3 V bank rails. Confirm with `read_xdc` (no pin
## conflicts) BEFORE `make program`.

# Address a[0..12]
set_property -dict {PACKAGE_PIN M4 IOSTANDARD SSTL18_II} [get_ports {ddram_a[0]}]
set_property -dict {PACKAGE_PIN P4 IOSTANDARD SSTL18_II} [get_ports {ddram_a[1]}]
set_property -dict {PACKAGE_PIN M6 IOSTANDARD SSTL18_II} [get_ports {ddram_a[2]}]
set_property -dict {PACKAGE_PIN T1 IOSTANDARD SSTL18_II} [get_ports {ddram_a[3]}]
set_property -dict {PACKAGE_PIN L3 IOSTANDARD SSTL18_II} [get_ports {ddram_a[4]}]
set_property -dict {PACKAGE_PIN P5 IOSTANDARD SSTL18_II} [get_ports {ddram_a[5]}]
set_property -dict {PACKAGE_PIN M2 IOSTANDARD SSTL18_II} [get_ports {ddram_a[6]}]
set_property -dict {PACKAGE_PIN N1 IOSTANDARD SSTL18_II} [get_ports {ddram_a[7]}]
set_property -dict {PACKAGE_PIN L4 IOSTANDARD SSTL18_II} [get_ports {ddram_a[8]}]
set_property -dict {PACKAGE_PIN N5 IOSTANDARD SSTL18_II} [get_ports {ddram_a[9]}]
set_property -dict {PACKAGE_PIN R2 IOSTANDARD SSTL18_II} [get_ports {ddram_a[10]}]
set_property -dict {PACKAGE_PIN K5 IOSTANDARD SSTL18_II} [get_ports {ddram_a[11]}]
set_property -dict {PACKAGE_PIN N6 IOSTANDARD SSTL18_II} [get_ports {ddram_a[12]}]

# Bank ba[0..2]
set_property -dict {PACKAGE_PIN P2 IOSTANDARD SSTL18_II} [get_ports {ddram_ba[0]}]
set_property -dict {PACKAGE_PIN P3 IOSTANDARD SSTL18_II} [get_ports {ddram_ba[1]}]
set_property -dict {PACKAGE_PIN R1 IOSTANDARD SSTL18_II} [get_ports {ddram_ba[2]}]

# Command / control
set_property -dict {PACKAGE_PIN N4 IOSTANDARD SSTL18_II} [get_ports ddram_ras_n]
set_property -dict {PACKAGE_PIN L1 IOSTANDARD SSTL18_II} [get_ports ddram_cas_n]
set_property -dict {PACKAGE_PIN N2 IOSTANDARD SSTL18_II} [get_ports ddram_we_n]
set_property -dict {PACKAGE_PIN K6 IOSTANDARD SSTL18_II} [get_ports ddram_cs_n]
set_property -dict {PACKAGE_PIN M1 IOSTANDARD SSTL18_II} [get_ports ddram_cke]
set_property -dict {PACKAGE_PIN M3 IOSTANDARD SSTL18_II} [get_ports ddram_odt]

# Data mask dm[0..1]
set_property -dict {PACKAGE_PIN T6 IOSTANDARD SSTL18_II} [get_ports {ddram_dm[0]}]
set_property -dict {PACKAGE_PIN U1 IOSTANDARD SSTL18_II} [get_ports {ddram_dm[1]}]

# Data dq[0..15] (IN_TERM=UNTUNED_SPLIT_50)
set_property -dict {PACKAGE_PIN R7 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[0]}]
set_property -dict {PACKAGE_PIN V6 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[1]}]
set_property -dict {PACKAGE_PIN R8 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[2]}]
set_property -dict {PACKAGE_PIN U7 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[3]}]
set_property -dict {PACKAGE_PIN V7 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[4]}]
set_property -dict {PACKAGE_PIN R6 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[5]}]
set_property -dict {PACKAGE_PIN U6 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[6]}]
set_property -dict {PACKAGE_PIN R5 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[7]}]
set_property -dict {PACKAGE_PIN T5 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[8]}]
set_property -dict {PACKAGE_PIN U3 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[9]}]
set_property -dict {PACKAGE_PIN V5 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[10]}]
set_property -dict {PACKAGE_PIN U4 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[11]}]
set_property -dict {PACKAGE_PIN V4 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[12]}]
set_property -dict {PACKAGE_PIN T4 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[13]}]
set_property -dict {PACKAGE_PIN V1 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[14]}]
set_property -dict {PACKAGE_PIN T3 IOSTANDARD SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dq[15]}]

# Strobes dqs_p/dqs_n[0..1] (DIFF_SSTL18_II, IN_TERM=UNTUNED_SPLIT_50)
set_property -dict {PACKAGE_PIN U9 IOSTANDARD DIFF_SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dqs_p[0]}]
set_property -dict {PACKAGE_PIN V9 IOSTANDARD DIFF_SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dqs_n[0]}]
set_property -dict {PACKAGE_PIN U2 IOSTANDARD DIFF_SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dqs_p[1]}]
set_property -dict {PACKAGE_PIN V2 IOSTANDARD DIFF_SSTL18_II IN_TERM UNTUNED_SPLIT_50} [get_ports {ddram_dqs_n[1]}]

# DRAM clock clk_p/clk_n (DIFF_SSTL18_II)
set_property -dict {PACKAGE_PIN L6 IOSTANDARD DIFF_SSTL18_II} [get_ports ddram_clk_p]
set_property -dict {PACKAGE_PIN L5 IOSTANDARD DIFF_SSTL18_II} [get_ports ddram_clk_n]

# SLEW=FAST on the whole DDR2 group.
set_property SLEW FAST [get_ports {ddram_*}]

## Internal VREF for the SSTL18_II banks (Nexys A7 DDR2 uses internal VREF).
set_property INTERNAL_VREF 0.900 [get_iobanks 34]
set_property INTERNAL_VREF 0.900 [get_iobanks 35]

##==============================================================================
## Floorplan -- data_path collation (read + write), DFI_RATE=4
##==============================================================================
## At rate=4 both collation critical paths came out routing-dominated (~67%
## route) because the placer scattered u_data_path across the die (low overall
## utilization = no packing pressure): rd_cl_aligner's r_fifo->r_stage CE and
## wr_beat_sequencer's beat_pull->r_stage_data.
##
## SINGLE pblock on rd_cl_aligner only. Empirically on this part (grid X0/X1 x
## Y0..Y3), this minimal floorplan is the optimum:
##   WNS by config -> rd-only(X0,2rgn): -0.405 | merged data_path(3rgn): -0.966
##                    both same col: -0.809 | rd X0 + wr X1: -0.526
## Adding ANY wr_beat_sequencer pblock made things worse -- it places better
## FREE (next to the axi_intake wbuf it beat-pulls from), and constraining it
## perturbs rd_cl_aligner's placement too. So: pblock rd_cl_aligner (the module
## whose r_fifo->r_stage CE path benefits most from compaction), leave the rest
## of the datapath to the placer. Placement-only (routing free), like
## stream_char's pblock_compressor.
## REMOVED (2026-07-18): this pblock targeted u_data_path/u_rd_cl_aligner — a cell
## that does NOT exist in the rearchitected core (the read aligner is now
## u_core/u_core/u_dfi/u_rd), so it was a NO-OP that only threw a critical
## warning. Timing is now closed by the FREQ DROP (sys 75->66.67 MHz in
## ddr2_char_top.sv, WNS -0.445 -> +0.131) rather than by floorplanning the
## routing-dominated arbiter row-hit->r_bank cone, so no pblock is needed.

## NOTE: a pblock on u_sched+u_ifc (tried CLOCKREGION_X1Y1:X1Y3) made WNS WORSE
## (-30.5 -> -33.0): forcing u_ifc into one column pushed rd_intake and wr_cam
## apart and LENGTHENED the snarf route (rd_intake AR -> wr_cam snarf_q), which
## is the worst path. Left to the placer FREE (consistent with the rd_cl_aligner
## note above: constraining the pumice cone backfires here). The route wall on
## the snarf/scheduler cone needs a pipeline register, not floorplanning.

## CORE Pblock (BRAM-anchored, wr_cam+rd_cam+arbiter into CLOCKREGION_X0Y1:X0Y3)
## was tried 2026-09-04 after the data->BRAM change regressed the w_rd_head_wins
## cross-CAM compare to WNS -4.237. It moved WNS only +0.19 ns (-4.045), route
## still 78%, and split the r_rfc_cnt carry chain across the region -- i.e. the
## SAME result as the pre-BRAM u_ifc attempt below. Floorplanning this cone does
## not work; the 26-level global-age compare needs a PIPELINE REGISTER. Pblock
## removed. See w_rd_head_wins pipelining work.

## A u_arbiter-only compaction Pblock (CLOCKREGION_X1Y1:X1Y2) was tried
## 2026-09-04 to attack the route-dominated intra-arbiter miss (pipelined build
## WNS -0.175). It BACKFIRED: WNS -1.013 (worse), 133 failing endpoints. Even a
## single-module Pblock hurts here -- confining u_arbiter congested the region
## (its own route grew to 12.5ns) AND pushed the CAMs away (u_rd_cam -> 81
## failing endpoints on the lengthened CAM->arbiter feed). So NO floorplanning
## of the scheduler/CAM cone works, single-module included; the levers are
## frequency or further logic-depth reduction. Pblock removed.

## bank_lsb (address-map config CSR) is set once before init and is CONSTANT
## during DRAM traffic, so its combinational fan-out into the address mapper /
## CAMs never needs to meet a per-cycle deadline. Relax paths that START there.
set_false_path -from [get_cells -quiet -hier -filter {NAME =~ *field_storage_reg*bank_lsb*}]

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
