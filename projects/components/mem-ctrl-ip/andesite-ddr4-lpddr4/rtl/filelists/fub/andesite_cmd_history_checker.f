# Filelist for andesite_cmd_history_checker — per-(rank,bank) issued-command
# history scoreboard (audit-only; generate-gated into the scheduler via
# CMD_HISTORY_EN, assertions simulation-only).
# reset_defs.svh -- this module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/includes

# pumice_pkg -- the module does `import pumice_pkg::*`, so the package is part
# of its closure. It was missing: this filelist declared only an incdir and the
# module, so elaborating it alone has never worked (dram_op_e referenced before
# declaration). Matches how the sibling fub filelists list it.
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/includes/andesite_pkg.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_cmd_history_checker.sv
