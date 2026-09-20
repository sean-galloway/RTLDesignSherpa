# ==============================================================================
# misc - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for the small shared oddments this area owns,
#          so that `make lint-misc` has sources to lint.
# Usage:   verilator --lint-only -f filelists/misc_all.f
#
# `-f` includes each module s own filelist; never hand-list sources here.
# Verified when written: all 11 module-declaring .sv files under rtl/ are
# reachable from the lists below, with no orphans.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/misc/rtl/filelists/axi4_intf_master_observer.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/axi4_intf_slave_observer.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/axi4_slave_rom.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/dma_address_gen.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/monbus_legal_cam.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/monbus_pkt_tally.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/monbus_tally_axil.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/simple_rom.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/stream_run_addr_gen.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/verilator_xilinx_stubs.f
