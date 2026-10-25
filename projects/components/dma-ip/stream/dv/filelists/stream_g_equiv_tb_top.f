# The stream-g equivalence bench (stream TASK-020): NUM_CHANNELS FSM schedulers
# beside NUM_CHANNELS scheduler_g on one rapids_seq_g.
# Location: projects/components/dma-ip/stream/dv/filelists/stream_g_equiv_tb_top.f
# STREAM's own firmware image FIRST on the include path: rapids_seq_g's
# `include "sched_g_fw.svh" must take stream-g's image (rtl/fw_g, built by
# bin/gen_stream_g_fw.py); rapids_seq_g_core.f brings the block without rapids' image.
+incdir+$STREAM_ROOT/rtl/macro_g/generated/fw
-f $REPO_ROOT/projects/components/dma-ip/stream/rtl/filelists/fub/scheduler.f
-f $REPO_ROOT/projects/components/dma-ip/stream/rtl/filelists/fub_g/scheduler_g.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_seq_g_core.f
$REPO_ROOT/projects/components/dma-ip/stream/dv/tb/stream_g_equiv_tb_top.sv
