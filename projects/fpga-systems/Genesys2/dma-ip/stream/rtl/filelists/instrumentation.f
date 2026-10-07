# Filelist: rtl/filelists/instrumentation.f
#
# The char/perf bridge plus the shared instrumentation. Nothing in THIS tree
# pulls this list -- the Genesys 2 harness takes instrumentation_mon.f, and
# bridge_stream_char_axil is instantiated only by the older NexysA7
# stream_char harness, which has been migrated out. It is kept because that
# flow still references it from its own checkout.
#
# Everything except the bridge lives in instrumentation_common.f, so this
# cannot drift from the monitor list the way it did when both spelled out the
# same fourteen sources.
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/filelists/instrumentation_common.f
-f $STREAM_CHAR_FRAMEWORK_ROOT/rtl/bridges/filelists/bridge_stream_char_axil.f
