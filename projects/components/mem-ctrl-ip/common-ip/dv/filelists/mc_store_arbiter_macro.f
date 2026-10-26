# Filelist for the store<->arbiter macro contract test
# (common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py).
#
# Closure: pkg -> fifo primitives -> the store + both pick cores (SCHED_CORE
# selects one at elaboration; STORE_BACKEND selects the entry store or the
# bank FIFO store) -> tb top.

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/common

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes/mc_common_pkg.sv

-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_age_fifo_sync.f

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_xddr2_entry_store.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_bank_fifo_store.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arbiter.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_bank_head_records.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_bank_pick.sv

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_store_arbiter_macro_tb_top.sv
