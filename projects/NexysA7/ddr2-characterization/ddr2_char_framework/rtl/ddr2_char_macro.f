# Filelist for ddr2_char_macro
# Wraps the two AXI4 master-side characterization engines + the pumice
# memory controller behind a single module so the bench can drive cfg, APB,
# and DFI without touching the internal AXI plumbing.

# Engines bring their own deps (common, gaxi, axi4_master_wr/rd, addr-gen).
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_crc_check.f

# Perf: bus meters + latency histograms tapped on the internal AXI wires.
$REPO_ROOT/rtl/amba/shared/axi_bus_meter.sv
$REPO_ROOT/rtl/amba/shared/axi_perf_latency_hist.sv

# pumice controller top (geared) — pulls in axi4_ifc / scheduler / dfi_layer
# / core / PeakRDL csr + the host<->core AXI dwidth converters.
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top_geared.f

# APB CSR window -> controller cpuif shim (apb_slave_cdc + peakrdl_to_cmdrsp).
# counter_bin + fifo_control already come in via pumice_top_geared.f.
$REPO_ROOT/rtl/amba/shared/cdc_synchronizer.sv
$REPO_ROOT/rtl/amba/shared/cdc_2_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_4_phase_handshake.sv
$REPO_ROOT/rtl/amba/shared/cdc_open_loop.sv
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_slave_cdc.sv
$REPO_ROOT/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv
$REPO_ROOT/projects/components/converters/rtl/apb_to_peakrdl.sv

# The macro itself
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.sv
