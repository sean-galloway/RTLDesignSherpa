# Filelist for the full jet-mesi-l1 RTL closure.
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_all.f
#
# Starts with the package; each later task appends its own filelist here.

-f $JET_ROOT/rtl/filelists/jet_pkg.f
-f $JET_ROOT/rtl/filelists/jet_mshr.f
-f $JET_ROOT/rtl/filelists/jet_wb_buffer.f
-f $JET_ROOT/rtl/filelists/jet_rsp_seq.f
-f $JET_ROOT/rtl/filelists/jet_control.f

# Task 4: the jet planes + the recomposed pair-rig top (the plane
# filelists come in through jet_top.f / jet_ace_top.f)
-f $JET_ROOT/rtl/filelists/plane/jet_cpu_plane.f
-f $JET_ROOT/rtl/filelists/plane/jet_coh_core.f
-f $JET_ROOT/rtl/filelists/jet_top.f

# Task 9: the onyx-rig ACE top (with the shared common-ip issue block) + the pair fabric
-f $CACHE_COMMON_ROOT/rtl/filelists/fub/l1_ace_issue.f
-f $JET_ROOT/rtl/filelists/jet_ace_top.f
-f $JET_ROOT/rtl/filelists/jet_pair_fabric.f
