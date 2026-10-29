# Filelist for jet_rsp_seq
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_rsp_seq.f
#
# Response sequencer: CAM-free ring of per-tag completion records that keeps
# GAXI responses in request-accept order while fills/merges complete out of
# order internally (J4).  Needs the reset macro header and jet_pkg.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $JET_ROOT/rtl/filelists/jet_pkg.f

$JET_ROOT/rtl/fub/jet_rsp_seq.sv
