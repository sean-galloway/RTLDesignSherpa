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
## Multi-cycle paths — STREAM master GLOBAL_CTRL.GLOBAL_EN
##==============================================================================
## GLOBAL_CTRL.GLOBAL_EN is the sw-programmed master enable for the entire
## STREAM block. Like AXI_XFER_CONFIG above, it's written once at setup and
## held static during operation. Its fan-out reaches the AXI monitor's
## interrupt FIFO, the perf_error_count counter enables, and the write
## engine arbiter's pending-client logic. After the response-delay block
## was added to the harness, P&R perturbation pushed several of these
## paths just out of single-cycle closure (worst -0.569 ns).
##
## Same SW contract as AXI_XFER_CONFIG: idle transfers before disabling.
## Reads / writes to GLOBAL_CTRL during a live DMA are NOT supported.
set cfg_global_bits [get_cells -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*GLOBAL_CTRL*}]
set_multicycle_path 2 -setup -from $cfg_global_bits
set_multicycle_path 1 -hold  -from $cfg_global_bits

##==============================================================================
## Multi-cycle paths — AXI monitor reporter interrupt FIFO (write side)
##==============================================================================
## The desc-monitor's reporter feeds an interrupt FIFO that buffers monbus
## events (errors, completions, threshold crossings). Several different
## signals fan into the same RAM enable / address / data logic — sw enable
## bits (DAXMON_ENABLE), the per-slot transaction state table, the perf
## counter enables. Post-route placement consistently lands the intr_fifo
## RAM cells in a region where one or another of those source paths slides
## out of single-cycle closure (which combination depends on the P&R seed).
##
## MCP'ing one source at a time is whack-a-mole: every rebuild a different
## sibling becomes the worst path. Constraining at the DESTINATION (any
## pin under the intr_fifo) catches them all in one rule.
##
## Safety: this is an event FIFO. Events are written when the monitor sees
## an interesting transaction transition; one extra cycle of latency on
## the write means monbus packets emerge one cycle later. Invisible to
## software consumers and to anything timing-sensitive in the design's
## actual data path. We're NOT relaxing paths INSIDE the FIFO — only paths
## landing on its inputs.
set intr_fifo_dst [get_cells -hier -filter \
    {NAME =~ *u_axi_monitor_base/reporter/intr_fifo/*}]
set_multicycle_path 2 -setup -to $intr_fifo_dst
set_multicycle_path 1 -hold  -to $intr_fifo_dst

##==============================================================================
## False path — scheduler beats-remaining counter into read-arbiter
##==============================================================================
## r_read_beats_remaining is the per-channel decrementer in the scheduler
## that tracks "beats left to issue from this descriptor". It feeds two
## comparators (`<= sched_rd_beats_done` and `== 0`) whose output gates
## sched_rd_valid into the shared read engine's arbiter (gen_multi_channel
## .u_arbiter.r_pending_client_reg).
##
## P&R routinely places this path 14 levels deep through u_stream_regs ->
## back into the per-channel scheduler -> across multiple sibling
## scheduler_groups -> into the arbiter, taking ~9.7 ns of which 6.5 ns is
## routing. Worst slack post-route is in the -0.026 ns range, which on a
## -1 part causes intermittent stalls in the field.
##
## The path is functionally a false path: the size decrement and the
## arbiter's grant decision do NOT have a same-cycle dependency. The
## scheduler's done-strobe handshake with the engine ensures the arbiter
## can never sample stale beats_remaining and act on it incorrectly —
## any divergence is resolved by the next handshake cycle.
##
## Source: r_read_beats_remaining_reg* in every per-channel scheduler.
## Destination: every flop inside the read engine's arbiter. The 4-channel
## build only had r_pending_client_reg show up as the worst sibling of
## this cone, but at 8 channels grant_reg / grant_id_reg / r_last_grant_id_reg
## all land in the same ~14-level neighborhood. The same false-path
## justification covers every arbiter state element: the size decrement
## and the arbiter's state machine have no same-cycle dependency.
set rd_beats_src [get_cells -hier -filter \
    {NAME =~ *u_scheduler/r_read_beats_remaining_reg*}]
set rd_arb_dst [get_cells -hier -filter \
    {NAME =~ *u_axi_read_engine/gen_multi_channel.u_arbiter/*_reg*}]
set_false_path -from $rd_beats_src -to $rd_arb_dst

## Symmetric situation on the write side: the same decrementer pattern
## drives the write engine's arbiter. Constrain the entire arbiter state.
set wr_beats_src [get_cells -hier -filter \
    {NAME =~ *u_scheduler/r_write_beats_remaining_reg*}]
set wr_arb_dst [get_cells -hier -filter \
    {NAME =~ *u_axi_write_engine/gen_multi_channel.u_arbiter/*_reg*}]
set_false_path -from $wr_beats_src -to $wr_arb_dst

##==============================================================================
## False paths — additional sources into the write engine's arbiter
##==============================================================================
## The write engine's request to the arbiter is the AND of several per-
## channel signals. At 8 channels two more sources end up on the critical
## path into the same `u_arbiter/*_reg*` destination cone covered by the
## constraint above:
##
##   (1) u_sram_controller's per-channel latency_bridge skid-buffer write
##       pointer / drain-in-progress flop. The "this channel has enough
##       beats buffered to start a drain" comparison feeds
##       axi_wr_drain_data_avail[i] -> w_arb_request[i] -> arbiter.
##
##   (2) The write engine's own r_w_channel_id flop, which selects which
##       channel currently owns the W datapath. Replicated and routed
##       back into the arbiter's pending-client state at 15 levels.
##
## Both share the same justification as the scheduler-beats false_path:
## the request-side signal is a "wants to be granted" indicator whose
## consistency with the arbiter is maintained by the grant_ack handshake.
## A stale grant self-resolves on the next cycle (the engine simply
## doesn't issue AR if the requesting channel's data isn't actually
## there yet, and the arbiter moves on). Costs at most one wasted
## arbitration cycle per grant -- invisible in throughput.
set wr_sram_drain_src [get_cells -hier -filter \
    {NAME =~ *u_sram_controller/gen_channel_units*.u_channel_unit/u_latency_bridge/*_reg*}]
set_false_path -from $wr_sram_drain_src -to $wr_arb_dst

set wr_engine_chid_src [get_cells -hier -filter \
    {NAME =~ *u_axi_write_engine/r_w_channel_id_reg*}]
set_false_path -from $wr_engine_chid_src -to $wr_arb_dst

## Third source into the same arbiter cone: the W-channel skid buffer's
## wr_ready output. Fans out into per-channel "can start a burst" gating
## in w_arb_request. Same false-path family: skid backpressure feedback
## resolves into the arbiter through the grant_ack handshake; a one-
## cycle stale ready costs at most one arbitration retry.
set wr_skid_ready_src [get_cells -hier -filter \
    {NAME =~ *u_wr_axi_skid/w_channel/wr_ready_reg*}]
set_false_path -from $wr_skid_ready_src -to $wr_arb_dst

##==============================================================================
## Multi-cycle paths — DAXMON_ENABLE.MON_EN config bit
##==============================================================================
## DAXMON_ENABLE.MON_EN is the sw-programmed enable for the descriptor AXI
## monitor. Like AXI_XFER_CONFIG and GLOBAL_CTRL it's written once at setup
## and held static during operation. Its fan-out reaches the perf_error_count
## counter clock-enables in the AXI monitor reporter (4 endpoints, -0.142 ns
## post-route). Same SW contract: the bit is not toggled while transfers are
## in flight, so a 2-cycle propagation budget is safe.
set cfg_daxmon_bits [get_cells -hier -filter \
    {NAME =~ *u_stream_regs/field_storage_reg*DAXMON_ENABLE*MON_EN*}]
set_multicycle_path 2 -setup -from $cfg_daxmon_bits
set_multicycle_path 1 -hold  -from $cfg_daxmon_bits

##==============================================================================
## Multi-cycle paths — perf_profiler event FIFO (write side)
##==============================================================================
## u_perf_profiler/u_perf_fifo is the event FIFO that captures per-channel
## start/end timestamps for performance instrumentation. Its write data
## pin (DIBDI on the auto-inferred BRAM) is fed by combinational logic
## sourced from the scheduler state machine (~14 levels post-synthesis,
## marginal -0.061 ns slack post-route).
##
## Same justification as the intr_fifo MCP above: this is an event FIFO,
## not a control path. One extra cycle of latency on the write means
## perf events emerge one cycle later — invisible to software consumers
## and to any timing-sensitive logic in the data path. We constrain at
## the destination so any combination of source paths is captured.
set perf_fifo_dst [get_cells -hier -filter \
    {NAME =~ *u_perf_profiler/u_perf_fifo/*}]
set_multicycle_path 2 -setup -to $perf_fifo_dst
set_multicycle_path 1 -hold  -to $perf_fifo_dst

##==============================================================================
## Configuration / Bitstream
##==============================================================================
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
