# Filelist: rtl/filelists/instrumentation_mon.f
#
# The monitor/observer bridge plus the shared instrumentation. This is the list
# the Genesys 2 harness pulls, so it is what ALL THREE build flavours and the
# cocotb sim compile -- perf, obs and mon differ by generics, never by sources.
#
# Everything except the bridge lives in instrumentation_common.f. The two lists
# were once identical but for the bridge line, which meant the harness registers
# were written down twice.
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/filelists/instrumentation_common.f
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_stream_mon_axil.f
