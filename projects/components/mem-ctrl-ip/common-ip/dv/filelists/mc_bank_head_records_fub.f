# Filelist for the mc_bank_head_records fub test
# (common-ip/dv/tests/fub/test_mc_bank_head_records.py).
#
# Closure: pkg -> the record block under test -> tb top.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_head_records.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_bank_head_records_tb_top.sv
