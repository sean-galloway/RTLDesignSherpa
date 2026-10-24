# Filelist for scheduler_g (STREAM, stream TASK-020): the gatling-sequenced
# scheduler around scheduler_core.
# Location: projects/components/dma-ip/stream/rtl/filelists/fub_g/scheduler_g.f
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
-f $STREAM_ROOT/rtl/filelists/fub/scheduler_core.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub_g/scheduler_g_base_fifo.f
$STREAM_ROOT/rtl/fub_g/scheduler_g.sv
