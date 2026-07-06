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

# pumice controller top — pulls in axi_frontend / scheduler / data_path
# / dfi_v21_interface / core / csr_slave.
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/top/pumice_top.f

# The macro itself
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.sv
