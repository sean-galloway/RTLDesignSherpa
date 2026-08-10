##==============================================================================
## Genesys 2 Constraints — STREAM Characterization Harness (monitor validation)
##==============================================================================
## Board: Digilent Genesys 2 (Kintex-7 XC7K325T-2FFG900C)
## Top:   stream_char_genesys2_top  (MMCM: 200 MHz LVDS sysclk -> harness clock)
## Host:  single USB-UART link (115200 8N1 via the board's FT232R)
## Pins from the Digilent Genesys-2-Master.xdc (Rev H), matching the proven
## rapids_char_genesys2_top.xdc. Timing exceptions ported from the Nexys A7
## stream_char_top.xdc (documented SW-contract multicycles + functional false
## paths); the A7 pblock floorplanning is deliberately NOT ported — the K325T
## at this clock should not need it (add back per the A7 file if it ever does).
##==============================================================================

##==============================================================================
## Primary Clock — 200 MHz LVDS system clock (AD12/AD11)
##==============================================================================
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports sysclk_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports sysclk_n]
create_clock -period 5.000 -name sysclk_200 -waveform {0.000 2.500} [get_ports sysclk_p]
## The MMCM (u_mmcm) derives the harness clock; Vivado auto-generates it from
## the CLKOUT0 divider (default 12 -> 100 MHz).

##==============================================================================
## CPU reset button (R19, active-low) — asynchronous
##==============================================================================
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]
set_false_path -from [get_ports cpu_resetn]

##==============================================================================
## USB-UART. Async at 115.2 kbaud — relaxed timing.
##==============================================================================
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_tx_in]
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_rx_out]
set_false_path -from [get_ports uart_tx_in]
set_false_path -to   [get_ports uart_rx_out]

##==============================================================================
## User LEDs (8)
##==============================================================================
set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
set_false_path -to [get_ports {led[*]}]

##==============================================================================
## Reset-synchronizer CDC (r_rst_meta/r_rst_sync in the board top). Async
## assert / sync deassert; the whole reset distribution is a false path (the
## design is held in reset for many cycles after configuration, so skew across
## the fan-out is harmless — same rationale as the A7 XDC).
##==============================================================================
set_false_path -from [get_ports cpu_resetn] \
               -to   [get_pins -hier -filter {NAME =~ r_rst_meta_reg/D}]
set_false_path -from [get_pins -hier -filter {NAME =~ r_rst_sync_reg/C}]

##==============================================================================
## LED status driver — slow generated clock + CDC handshake. Same structure as
## the A7/rapids flows. NOTE: -divide_by = 2 * FPGA_CLK_HZ / LED_UPDATE_HZ.
## Keep in lockstep with CLKOUT0_DIVIDE in the top: 100 MHz -> 1000000,
## 80 MHz -> 800000, 60 MHz -> 600000.
##==============================================================================
create_generated_clock -name led_slow_clk \
    -source [get_pins -hier -filter {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
    -divide_by 1000000 \
    [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]

set_clock_groups -asynchronous \
    -group [get_clocks -of_objects [get_pins u_bufg_c0/O]] \
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

##==============================================================================
## Multi-cycle paths — software-programmed AXI transfer-beat config
##==============================================================================
## AXI_XFER_CONFIG.{RD,WR}_XFER_BEATS are sw-written once at setup and held
## static during AXI transfers (SW contract: idle transfers before rewriting).
## Ported from the A7 XDC; see that file for the full derivation.
set cfg_xfer_bits [get_cells -quiet -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*AXI_XFER_CONFIG*XFER_BEATS*}]
set_multicycle_path 2 -setup -from $cfg_xfer_bits
set_multicycle_path 1 -hold  -from $cfg_xfer_bits

##==============================================================================
## Multi-cycle paths — STREAM master GLOBAL_CTRL (sw-static master enable)
##==============================================================================
set cfg_global_bits [get_cells -quiet -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*GLOBAL_CTRL*}]
set_multicycle_path 2 -setup -from $cfg_global_bits
set_multicycle_path 1 -hold  -from $cfg_global_bits

##==============================================================================
## Multi-cycle paths — AXI monitor reporter interrupt FIFO (write side)
##==============================================================================
## Event FIFO: one extra cycle of write latency only delays monbus packet
## emergence by a cycle — invisible to software and the datapath. Constrained
## at the destination so every source cone is covered (A7 rationale).
set intr_fifo_dst [get_cells -quiet -hier -filter \
    {NAME =~ *u_axi_monitor_base/reporter/intr_fifo/*}]
set_multicycle_path 2 -setup -to $intr_fifo_dst
set_multicycle_path 1 -hold  -to $intr_fifo_dst

##==============================================================================
## Multi-cycle paths — DAXMON_ENABLE.MON_EN config bit (sw-static)
##==============================================================================
set cfg_daxmon_bits [get_cells -quiet -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*DAXMON_ENABLE*MON_EN*}]
set_multicycle_path 2 -setup -from $cfg_daxmon_bits
set_multicycle_path 1 -hold  -from $cfg_daxmon_bits

##==============================================================================
## Multi-cycle paths — perf_profiler event FIFO (write side)
##==============================================================================
set perf_fifo_dst [get_cells -quiet -hier -filter \
    {NAME =~ *u_perf_profiler/u_perf_fifo/*}]
set_multicycle_path 2 -setup -to $perf_fifo_dst
set_multicycle_path 1 -hold  -to $perf_fifo_dst

##==============================================================================
## False path — scheduler beats-remaining counter into rd/wr engine arbiters
##==============================================================================
## Functionally a false path: the size decrement and the arbiter's grant
## decision have no same-cycle dependency (done-strobe handshake resolves any
## divergence next cycle). Scope limited to r_pending_client_reg — grant_*_reg
## form a valid/ready handshake and must NOT be false-pathed. Full derivation
## in the A7 stream_char_top.xdc.
set rd_beats_src [get_cells -quiet -hier -filter \
    {NAME =~ *u_scheduler/r_read_beats_remaining_reg*}]
set rd_arb_dst [get_cells -quiet -hier -filter \
    {NAME =~ *u_axi_read_engine/gen_multi_channel.u_arbiter/r_pending_client_reg*}]
set_false_path -from $rd_beats_src -to $rd_arb_dst

set wr_beats_src [get_cells -quiet -hier -filter \
    {NAME =~ *u_scheduler/r_write_beats_remaining_reg*}]
set wr_arb_dst [get_cells -quiet -hier -filter \
    {NAME =~ *u_axi_write_engine/gen_multi_channel.u_arbiter/r_pending_client_reg*}]
set_false_path -from $wr_beats_src -to $wr_arb_dst

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
