# Filelist for cxs_master
# Location: rtl/amba/filelists/cxs_master.f
#
# CXS (Arm IHI 0079, Issues A-D). See docs/markdown/rtl-amba/cxs/README.md

# Package first: the module imports it in its header
-f $REPO_ROOT/rtl/amba/filelists/cxs_pkg.f
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_odd_byte_parity.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_cntl_track.f
-f $REPO_ROOT/rtl/amba/filelists/cxs_stream_key.f
$REPO_ROOT/rtl/amba/cxs/cxs_master.sv
