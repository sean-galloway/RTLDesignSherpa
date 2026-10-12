# Filelist for granite_char_macro
# Wraps the two AXI4 master-side characterization engines + the Granite
# memory controller behind a single module so the bench can drive cfg, APB,
# and DFI without touching the internal AXI plumbing. Mirrors
# ddr2_char_framework/rtl/filelists/ddr2_char_macro.f with the controller
# swapped for granite_top_geared.

# Engines bring their own deps (common, gaxi, axi4_master_wr/rd, addr-gen).
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_injector.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_crc_check.f

# Perf: bus meters + latency histograms tapped on the internal AXI wires.
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f

# Granite controller top (geared) -- pulls in granite.f / granite_csr / core
# plus the host<->core AXI dwidth converters.
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite_top_geared.f

# APB CSR window -> controller cpuif shim (apb4_slave_cdc + peakrdl_to_cmdrsp).
# counter_bin + fifo_control already come in via granite_top_geared.f.
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb4_to_peakrdl.f

# The generator config block.
-f $REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/filelists/chargen_regs.f

# The generator unit: two write and two read generator blocks and the N:1 merge
# that puts them on the Granite controller's single s_axi port.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_axi_mux.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_wr_order_q.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_unit.sv

# The macro itself
# DUT-agnostic engine spine (generator unit + chargen_regs + perf).
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_engine_block.sv
$REPO_ROOT/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite/rtl/granite_char_macro.sv
