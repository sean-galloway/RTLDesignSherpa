# Filelist: rtl/filelists/instrumentation_common.f
#
# Every instrumentation source that is NOT the bridge -- harness_csr and its
# GENERATED register block, the response-delay shim, the SRAM channel tracker,
# the LED/7-seg drivers.
#
# WHY THIS FILE EXISTS: instrumentation.f and instrumentation_mon.f were
# identical except for ONE line, the bridge. Fourteen duplicated entries,
# including the harness registers. Adding the generated harness_csr regblock
# meant editing both, and editing only one would have left two builds compiling
# different register sets -- silently, because each list is internally valid.
#
# The registers belong to ONE RTL shared by all three build flavours
# (perf/obs/mon), so they are listed here exactly once and the two variants add
# nothing but their bridge. A source that belongs to every flavour must never be
# typed twice.
#
# Do NOT put a bridge in here: the two bridges' adapter modules collide by name,
# so a build takes exactly one.
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/axi_response_delay.sv

# harness_csr's registers are generated from regs/harness_csr_regs.rdl. The
# package and block must precede the module that instantiates them.
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/regs/generated/rtl/harness_csr_regs_top_pkg.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/regs/generated/rtl/harness_csr_regs_top.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/harness_csr.sv

-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_core.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axil_axil.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/sram_chan_tracker.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/sram_chan_tracker_bind.sv
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/seven_seg_4digit.sv
