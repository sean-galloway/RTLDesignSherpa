# ==============================================================================
# HIVE - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: compile closure for the HIVE control-plane RTL (hive_top and
#          sub-blocks), so `make lint-hive` has sources to lint.
# Usage:   verilator --lint-only -f filelists/hive_all.f
#
# Blocks: hive_c_controller (Block 1), engine_monitor (Block 2: one gatling,
#         four per-engine peripheral sets),
#         control_network (Block 3), config_manager (Block 4).
# The VexRiscv core (vendor/vexriscv) is upstream code: hive_c_loader.f pulls
# it in for the compile closure, but its warnings are upstream's, not this
# area's; gatling is linted in its own area (riscv-ip/gatling-rv32i).
#
# Named hive_all.f to match the module prefix and the registry area name in
# bin/filelists.toml and the directory (renamed from hive-serv 2026-11-25).
# ==============================================================================

# --- Block RTL (appended as modules land; Phase 1 bring-up) ------------------
# Block 1, hive_c_controller
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_c_loader.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_axis_cda_master.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_descriptor_gen.f

# Block 2, engine_monitor per-engine leaves (the monitor top not written yet;
# local_mem is the v0.2 SERV memory, kept until the top lands)
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/traffic_counter.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/trigger_logic.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/axis_injector.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/local_mem.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/ctrl_net_slave.f

# Block 3, control network
-f $REPO_ROOT/projects/components/compute-eng-ip/hive/rtl/filelists/hive_ctrl_network.f
