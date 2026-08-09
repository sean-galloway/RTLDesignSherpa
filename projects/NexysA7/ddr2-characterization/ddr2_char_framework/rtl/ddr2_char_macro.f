# Filelist for ddr2_char_macro
# Wraps the two AXI4 master-side characterization engines + the pumice
# memory controller behind a single module so the bench can drive cfg, APB,
# and DFI without touching the internal AXI plumbing.

# Engines bring their own deps (common, gaxi, axi4_master_wr/rd, addr-gen).
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_crc_check.f

# Perf: bus meters + latency histograms tapped on the internal AXI wires.
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f

# pumice controller top (geared) — pulls in axi4_ifc / scheduler / dfi_layer
# / core / PeakRDL csr + the host<->core AXI dwidth converters.
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top_geared.f

# APB CSR window -> controller cpuif shim (apb4_slave_cdc + peakrdl_to_cmdrsp).
# counter_bin + fifo_control already come in via pumice_top_geared.f.
#
# apb4_slave_cdc's CDC is a gray-pointer async FIFO (gaxi_fifo_async), not a
# toggle handshake: the APB side (presetn) and core side (aresetn) are separate
# reset domains here — CTRL.soft_reset pulses only the core side — and a
# toggle-parity handshake desynchronizes under that, permanently offsetting the
# response stream by one transaction.
-f $REPO_ROOT/rtl/cdc/filelists/counter_johnson.f
-f $REPO_ROOT/rtl/common/filelists/find_first_set.f
-f $REPO_ROOT/rtl/common/filelists/find_last_set.f
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f
-f $REPO_ROOT/rtl/cdc/filelists/johnson2bin.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_open_loop.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv
$REPO_ROOT/projects/components/converters/rtl/apb_to_peakrdl.sv

# The macro itself
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.sv
