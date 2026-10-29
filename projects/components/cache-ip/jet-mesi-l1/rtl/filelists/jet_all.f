# Filelist for the full jet-mesi-l1 RTL closure.
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_all.f
#
# Starts with the package; each later task appends its own filelist here.

-f $JET_ROOT/rtl/filelists/jet_pkg.f
-f $JET_ROOT/rtl/filelists/jet_mshr.f
-f $JET_ROOT/rtl/filelists/jet_wb_buffer.f
-f $JET_ROOT/rtl/filelists/jet_rsp_seq.f
-f $JET_ROOT/rtl/filelists/jet_control.f
-f $JET_ROOT/rtl/filelists/jet_top.f

# Task 9: the onyx-rig ACE top (with its issue block) + the pair fabric
-f $JET_ROOT/rtl/filelists/jet_ace_issue.f
-f $JET_ROOT/rtl/filelists/jet_ace_top.f
-f $JET_ROOT/rtl/filelists/jet_pair_fabric.f
