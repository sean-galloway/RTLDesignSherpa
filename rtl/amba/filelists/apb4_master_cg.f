# Filelist for apb4_master_cg
# Location: rtl/amba/filelists/apb4_master_cg.f
#
# Added 2026-09-02. This module had NO filelist, which is why it had no test:
# nothing could build it. It was the only clock-gated wrapper in the repo with
# no gating coverage at all, and the missing filelist is the reason -- not an
# oversight in the test.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/apb4_master.f
-f $REPO_ROOT/rtl/common/filelists/icg.f
-f $REPO_ROOT/rtl/common/filelists/clock_gate_ctrl.f
$REPO_ROOT/rtl/amba/shared/amba_clock_gate_ctrl.sv
$REPO_ROOT/rtl/amba/apb4/apb4_master_cg.sv
