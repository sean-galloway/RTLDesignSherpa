# pumice_rbl_table -- RBLA row-locality miss-counter table (modes 6/7).
# Pipelined update (PUMICE-017): stage-0 read / stage-1 write+verdict.
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_rbl_table.sv
