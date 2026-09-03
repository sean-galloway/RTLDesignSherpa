# Filelist for pumice_cmd_arbiter
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv
# Two-stage bank-partitioned scheduler -- the arbiter's sole implementation
# (the legacy flat arbiter was retired). Both modules are instantiated
# unconditionally by pumice_cmd_arbiter and must precede it.
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_bank_cmd_picker.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_bank_sched_core.sv
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/fub/pumice_cmd_arbiter.sv
