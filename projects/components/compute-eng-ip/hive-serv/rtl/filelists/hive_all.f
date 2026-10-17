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

# --- Block RTL (appended as modules land; Phase 1 bring-up) ------------------
# Block 1, hive_c_controller (hive_c_loader not written yet)
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/hive_axis_cda_master.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/hive_descriptor_gen.f

# Block 2, serv_monitor leaves (the serv_monitor top not written yet)
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/traffic_counter.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/trigger_logic.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/axis_injector.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/local_mem.f
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/ctrl_net_slave.f

# Block 3, control network
-f $REPO_ROOT/projects/components/compute-eng-ip/hive-serv/rtl/filelists/hive_ctrl_network.f
