# ==============================================================================
# HIVE (hive-serv) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: compile closure for the HIVE control-plane RTL (hive_top and
#          sub-blocks), so `make lint-hive` has sources to lint.
# Usage:   verilator --lint-only -f filelists/hive_all.f
#
# Blocks: hive_c_controller (Block 1), serv_monitor (Block 2, 16x),
#         control_network (Block 3), config_manager (Block 4).
# Vendored cores (vendor/vexriscv, vendor/serv) are upstream code and are
# NOT linted as part of this area.
#
# Named hive_all.f to match the module prefix and the registry area name in
# bin/filelists.toml; the DIRECTORY is hive-serv.
# ==============================================================================

+incdir+$REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/includes

# --- Block RTL (appended as modules land; Phase 1 bring-up) ------------------
# -f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/core/hive_c_controller.f
# -f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/core/serv_monitor.f
