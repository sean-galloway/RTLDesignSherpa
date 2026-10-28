# Filelist for the mc_rd_return_ring fub test
# (common-ip/dv/tests/fub/test_mc_rd_return_ring.py).
#
# Closure: the ring (its own filelist carries the gaxi FIFO it builds on);
# the ring's ports are packed, so it is the toplevel itself.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_return_ring.f
