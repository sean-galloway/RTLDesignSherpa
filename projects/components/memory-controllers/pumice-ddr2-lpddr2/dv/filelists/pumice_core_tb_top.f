# Filelist for pumice_core_tb_top.
# The DUT closure comes from the component's OWN filelist — never hand-list
# rtl/common or rtl/amba sources here (they rot when a component's internal
# deps change; see the STREAM fub filelists for the pattern).
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_core.f
# dv checkers (standalone scoreboards, instantiated in the tb top)
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/dv/checkers/pumice_dfi_rd_return_checker.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/dv/tb/pumice_core_tb_top.sv
