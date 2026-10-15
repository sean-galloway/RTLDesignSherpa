# Filelist for the store<->arbiter macro contract test
# (common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py).
#
# Closure: pkg -> fifo primitives -> the two blocks under test -> tb top.

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/common

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes/mc_common_pkg.sv

$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_xddr2_entry_store.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arbiter.sv

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_store_arbiter_macro_tb_top.sv
