# Filelist for the rapids_byte_harness sources that do not depend on the DUT's
# channel count: pattern blocks, memories, host path and the harness itself.
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness_common.f
# Pulled by rapids_byte_harness.f (8-channel DUTs) and rapids_byte_harness_16ch.f
# (16-channel DUTs) after their DUT filelists, which supply the packages.

# ---- CRC + LFSR leaves (not pulled by the DUT filelist) ----
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc_xor_shift_cascade.f
-f $REPO_ROOT/rtl/common/filelists/dataint_crc.f
-f $REPO_ROOT/rtl/common/filelists/shifter_lfsr_fibonacci.f

# ---- AXI4 skid leaves + SDPRAM/addr-gen core (deps of the memory/pattern blocks) ----
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f

# ---- On-chip pattern generators / checkers + memories ----
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_injector.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_crc_check.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axis_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_injector.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave_pattern_check.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# ---- Harness top ----
# ---- Host path (relocated from rapids_byte_top: the harness owns UART->AXIL->APB)
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_master.f
# Memory-latency model on the R and B channels (STREAM knob 5), RESP_DELAY CSR.
$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/stream/rtl/axi_response_delay.sv
# Shared interface observers (USE_OBSERVERS, rapids TASK-001). Generate-gated
# in the harness, but their closure must compile in every build.
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/axi4_intf_master_observer.f
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/axis4_intf_observer.f
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/char_run_timer.f

$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/rtl/rapids_byte_harness.sv
