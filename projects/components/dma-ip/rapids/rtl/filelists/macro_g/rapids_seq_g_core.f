# rapids_seq_g_core.f -- the sequencer block WITHOUT a firmware image: the
# gatling core, its arbiter and rapids_seq_g.sv, whose `include "sched_g_fw.svh"
# is left to the consumer's include path. rapids_seq_g.f adds rapids-g's image;
# a design with its own image (stream-g, rtl/fw_g) pulls this file and puts its
# own generated/fw directory on the path instead (owner 2026-10-24: the two
# designs' firmware is not common, and the Vivado flattener sorts include
# directories, so only ONE sched_g_fw.svh may be reachable in a build).
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin_simple_ack.f
-f $GATLING_ROOT/rtl/filelists/top/gatling_core.f
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro_g/rapids_seq_g.sv
