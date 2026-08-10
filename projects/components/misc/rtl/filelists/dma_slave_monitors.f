# Filelist for dma_slave_monitors
# Location: projects/components/misc/rtl/filelists/dma_slave_monitors.f
#
# Monitored DMA-slave wrapper: axi4_dma_slaves plus a slave-side rd/wr monitor
# pair, with its OWN APB config regblock (slvmon_regs) rather than 16 cfg_*
# ports for the harness to tie off.
#
# In misc/ because it is NOT stream-specific -- rapids-beats uses the same
# instrumentation pair (this and axi4_intf_observer), and its HAS already names
# the observer as "the shared, DMA-agnostic" instrument. It was briefly placed
# in the stream component on the assumption only stream used it; that was the
# same wrong assumption made about the observer an hour earlier.

+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/axi4_dma_slaves.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd_mon.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_wr_mon.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f
-f $REPO_ROOT/rtl/amba/filelists/monbus_axil_axil_group.f
# The block's OWN config regblock and the APB->cmdrsp->passthrough chain behind
# it (same chain stream_top_ch8 uses). These are part of dma_slave_monitors'
# compile closure now, not the harness's.
$REPO_ROOT/projects/components/misc/rtl/regs/slvmon_regs.vlt
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/slvmon_regs_top_pkg.sv
$REPO_ROOT/projects/components/misc/rtl/regs/generated/rtl/slvmon_regs_top.sv
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv

$REPO_ROOT/projects/components/misc/rtl/dma_slave_monitors.sv
