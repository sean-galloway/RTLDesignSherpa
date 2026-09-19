# ==============================================================================
# STREAM - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.
#          rtl/Makefile has referenced this exact path as MASTER_FILELIST all
#          along; the file was never created, so `make lint-stream` died with
#          "Cannot open -f command file" and the gate measured nothing.
# Usage:   verilator --lint-only -f filelists/stream_all.f
#
# `-f` includes each block's own filelist; never hand-list sources here.
# Verified when written: every module-declaring .sv under rtl/ is reachable
# from the lists below, with no orphans and no duplicate module names.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/axi_read_engine.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/axi_write_engine.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/descriptor_engine.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/perf_profiler.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/scheduler.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/sram_controller.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/fub/stream_latency_bridge.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/datapath_rd_test.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/datapath_wr_test.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/monbus_axil_group.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/scheduler_group_array.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/scheduler_group.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/macro/stream_core.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/stream_pkg.f
-f $REPO_ROOT/projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f
