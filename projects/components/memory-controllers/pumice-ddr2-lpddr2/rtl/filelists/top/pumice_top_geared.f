# Filelist for pumice_top_geared (pumice_top + formal AXI dwidth converters).
# Host AXI width decoupled from DW via axi4_dwidth_converter_wr/rd.
#
# COMPOSES pumice_top.f rather than re-listing its closure. It used to be a
# parallel hand-maintained copy: 46 of its 47 entries were identical to
# pumice_top.f, and the one that was not is how it broke -- pumice_top.f gained
# the gated pumice_cmd_history_checker and this list did not, so building the
# scoreboard through the GEARED top died with MODMISSING while the plain top
# worked. Two lists that must agree will not stay agreed; one that includes the
# other cannot drift. Anything the core top needs now arrives here for free.
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top.f

# ---- AXI data-width converters (host <-> DW), the only thing geared adds ----
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_rd.f

# ---- geared wrapper ----
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/top/pumice_top_geared.sv
