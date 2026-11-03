# Filelist for the mc_axi4_narrow_pack fub test
# (common-ip/dv/tests/fub/test_mc_axi4_narrow_pack.py).
#
# Closure: the block (its own filelist carries the gaxi FIFO it builds on);
# its ports are flat AXI4, so it is the toplevel itself.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_axi4_narrow_pack.f
