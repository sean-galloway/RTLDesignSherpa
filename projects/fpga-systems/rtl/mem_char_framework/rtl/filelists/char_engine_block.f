# The DUT-agnostic memory-characterization engine.
#
# This is the whole point of the shared framework: one engine, one CSR map, one
# host program, behind whichever memory controller a board build puts under it.
# pumice/DDR2 on Nexys A7 and scoria/DDR3 on Genesys 2 both pull THIS file, so a
# bandwidth number from one is comparable with a bandwidth number from the other
# -- which is exactly what an A/B against LiteDRAM is for.
#
# It carries NO controller dependency. mem_char_pkg supplies the one enum the
# framework needs (mem_variant_e); a controller's package must never appear in
# this closure. It did once: char_engine_block imported pumice_pkg, which put
# the DDR2 controller's package in the LiteDRAM build's synthesis closure and
# made the framework unusable from a DDR3 harness.
#
# What is NOT here, deliberately:
#   harness_csr.sv        board-level control/status -- the build lists it, so
#                         a build can carry its own without forking the engine
#   led_status_driver.sv  board display, ditto
#   the bridges           each board's address map is its own

+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/mem_char_pkg.sv

# AXI/APB plumbing the engine and its CSR window need.
-f $REPO_ROOT/rtl/cdc/filelists/cdc_open_loop.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/apb4_slave_cdc.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/apb4_to_peakrdl.f

# The pattern generators and the perf instruments the engine instantiates.
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_pattern_gen.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_crc_check.f
-f $REPO_ROOT/rtl/amba/filelists/axi_bus_meter.f
-f $REPO_ROOT/rtl/amba/filelists/axi_perf_latency_hist.f

# Generator config block (PeakRDL).
-f $REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/filelists/chargen_regs.f

# Generator unit: write/read generator blocks + the N:1 merge onto the
# controller's single AXI port.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_axi_mux.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_wr_order_q.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_gen_unit.sv

# The engine spine.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/char_engine_block.sv
