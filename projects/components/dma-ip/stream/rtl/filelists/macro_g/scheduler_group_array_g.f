# Filelist for scheduler_group_array_g (stream-g, stream TASK-020): the product
# array with scheduler_g per channel and one rapids_seq_g (the rapids-g sequencer
# block, reused) serving them; the shared-engine structure only.
# Location: projects/components/dma-ip/stream/rtl/filelists/macro_g/scheduler_group_array_g.f
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
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_seq_g.f
$STREAM_ROOT/rtl/fub/descriptor_engine_shared.sv
$STREAM_ROOT/rtl/macro_g/generated/scheduler_group_array_g.sv
