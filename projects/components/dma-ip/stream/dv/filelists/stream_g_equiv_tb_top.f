# The stream-g equivalence bench (stream TASK-020): NUM_CHANNELS FSM schedulers
# beside NUM_CHANNELS scheduler_g on one rapids_seq_g.
# Location: projects/components/dma-ip/stream/dv/filelists/stream_g_equiv_tb_top.f
-f $REPO_ROOT/projects/components/dma-ip/stream/rtl/filelists/fub/scheduler.f
-f $REPO_ROOT/projects/components/dma-ip/stream/rtl/filelists/fub_g/scheduler_g.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_seq_g.f
$REPO_ROOT/projects/components/dma-ip/stream/dv/tb/stream_g_equiv_tb_top.sv
