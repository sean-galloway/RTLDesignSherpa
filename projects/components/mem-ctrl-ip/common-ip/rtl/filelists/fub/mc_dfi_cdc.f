# Filelist for mc_dfi_cdc (common-ip DFI 2.1 CDC)
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
# async FIFO deps
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
# this module
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_dfi_cdc.sv
