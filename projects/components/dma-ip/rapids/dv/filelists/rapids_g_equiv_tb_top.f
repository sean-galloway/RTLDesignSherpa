# rapids-g equivalence bench (rapids TASK-034): FSM schedulers beside
# gatling-sequenced ones. Both scheduler filelists carry scheduler_core.sv;
# the filelist tools de-duplicate it.
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/scheduler.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub_g/scheduler_g.f
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_seq_g.f
$REPO_ROOT/projects/components/dma-ip/rapids/dv/tb/rapids_g_equiv_tb_top.sv
