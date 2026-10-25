# Filelist for scheduler_group_array_g (stream-g, stream TASK-020): the product
# array with scheduler_g per channel and one rapids_seq_g (the rapids-g sequencer
# block, reused) serving them; the shared-engine structure only.
# Location: projects/components/dma-ip/stream/rtl/filelists/macro_g/scheduler_group_array_g.f
# STREAM's own firmware image FIRST on the include path: rapids_seq_g's
# `include "sched_g_fw.svh" must take stream-g's image (rtl/fw_g, built by
# bin/gen_stream_g_fw.py); rapids_seq_g_core.f brings the block without rapids' image.
+incdir+$STREAM_ROOT/rtl/macro_g/generated/fw
+incdir+$STREAM_ROOT/rtl/includes
+incdir+$STREAM_ROOT/rtl/macro_g
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_single_client.f
$STREAM_ROOT/rtl/includes/stream_pkg.sv
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_monlite.f
# the per-channel branch still names scheduler_group (it fatals at elaboration)
-f $STREAM_ROOT/rtl/filelists/macro/scheduler_group.f
-f $STREAM_ROOT/rtl/filelists/fub_g/scheduler_g.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_seq_g_core.f
$STREAM_ROOT/rtl/fub/descriptor_engine_shared.sv
$STREAM_ROOT/rtl/macro_g/generated/scheduler_group_array_g.sv
