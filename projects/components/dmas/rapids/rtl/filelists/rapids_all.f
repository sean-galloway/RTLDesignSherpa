# ==============================================================================
# RAPIDS - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.
#          rtl/Makefile has referenced this exact path as MASTER_FILELIST all
#          along; the file was never created, so `make lint-rapids` died with
#          "Cannot open -f command file" and the gate measured nothing.
# Usage:   verilator --lint-only -f filelists/rapids_all.f
#
# `-f` includes each block's own filelist; never hand-list sources here.
# Verified when written: every module-declaring .sv under rtl/ is reachable
# from the lists below, with no orphans and no duplicate module names.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/alloc_ctrl_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/axi_read_engine_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/axi_write_engine_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/latency_bridge_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub_beats/scheduler_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub/ctrlrd_engine.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/fub/ctrlwr_engine.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_core_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_snk_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/rapids_src_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/scheduler_group_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_data_path_axis_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_data_path_axis_test_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_data_path_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_data_path_axis_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_data_path_axis_test_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_data_path_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro_beats/src_sram_controller_beats.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/macro/monbus_axil_group.f
-f $REPO_ROOT/projects/components/dmas/rapids/rtl/filelists/top_beats/rapids_beats_top.f
