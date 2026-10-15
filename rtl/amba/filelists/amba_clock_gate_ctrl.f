# Filelist for amba_clock_gate_ctrl
# Location: rtl/amba/filelists/amba_clock_gate_ctrl.f
#
# Generated from the inline verilog_sources lists in val/amba.
# Compile order is significant and preserved from the original tests.

+incdir+$REPO_ROOT/rtl/amba/includes

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
