# ==============================================================================
# Converters - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns, so that
#          `make lint-converters` has sources to lint.
# Usage:   verilator --lint-only -f filelists/converters_all.f
#
# `-f` includes each module's own filelist; never hand-list sources here.
# Verified when written: all 34 module-declaring .sv files under rtl/ are
# reachable from the lists below, with no orphans and no duplicate modules.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb4_to_axi4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb4_to_peakrdl.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb5_to_axi4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb_cmdrsp_to_axi4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_to_apb4_chain.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_dwidth_to_axil4_wr_chain.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_apb4_shim.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_apb5_shim.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil4_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil5.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil5_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_axil5_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi4_to_wb4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_axi4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_axi4_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_axi4_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_wb4_core.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil4_to_wb4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_rd.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/axil_to_axi4_wide_align_wr.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/uart_axil_bridge.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/wb4_to_axi4.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/wb4_to_axil4_core.f
-f $REPO_ROOT/projects/components/converters/rtl/filelists/wb4_to_axil4.f
