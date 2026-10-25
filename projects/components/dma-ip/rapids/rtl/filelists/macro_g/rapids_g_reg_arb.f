# rapids-g (rapids TASK-034): the register command-queue arbiter -- who may
# push into the register block's command queue (host APB, SRC gatling, SNK
# gatling share the one cmd/rsp path into peakrdl_to_cmdrsp).
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro_g/rapids_g_reg_arb.f
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin_simple_ack.f
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_g/rapids_g_reg_arb.sv
