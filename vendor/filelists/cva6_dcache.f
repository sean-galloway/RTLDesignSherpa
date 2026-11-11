# Filelist for the vendored OpenHW CVA6 write-back data cache (std_nbdcache)
# Location: vendor/filelists/cva6_dcache.f
#
# Upstream RTL, see vendor/cva6-dcache/PROVENANCE.md. Packages first in
# dependency order; the technology SRAM cell (tc_sram) is NOT here -- the
# consumer supplies it together with tc_sram_wrapper (projects/fpga-systems/
# Genesys2/cache-ip/ref/rtl/tc_sram.sv, tc_sram_wrapper.sv). lfsr_8bit and cf_math_pkg come from vendor/pulp-common_cells.
# Consumer: projects/fpga-systems/Genesys2/cache-ip/ref (ref_cva6_dcache_top).

+incdir+$REPO_ROOT/vendor/pulp-common_cells/include
$REPO_ROOT/vendor/pulp-common_cells/src/cf_math_pkg.sv
# axi_adapter imports the PULP axi_pkg (vendor/pulp-axi)
$REPO_ROOT/vendor/pulp-axi/src/axi_pkg.sv
$REPO_ROOT/vendor/cva6-dcache/core/include/config_pkg.sv
# riscv_pkg / ariane_pkg read the per-core package by its generic name cva6_config_pkg
$REPO_ROOT/vendor/cva6-dcache/core/include/cv64a6_imafdc_sv39_wb_config_pkg.sv
$REPO_ROOT/vendor/cva6-dcache/core/include/riscv_pkg.sv
$REPO_ROOT/vendor/cva6-dcache/core/include/ariane_pkg.sv
$REPO_ROOT/vendor/cva6-dcache/core/include/std_cache_pkg.sv
$REPO_ROOT/vendor/cva6-dcache/core/include/build_config_pkg.sv
$REPO_ROOT/vendor/pulp-common_cells/src/lfsr_8bit.sv
# tc_sram_wrapper is supplied by the consumer with tc_sram (Vivado empties the typed-port upstream wrapper)
$REPO_ROOT/vendor/cva6-dcache/common/local/util/sram.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/amo_alu.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/tag_cmp.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/axi_adapter.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/miss_handler.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/cache_ctrl.sv
$REPO_ROOT/vendor/cva6-dcache/core/cache_subsystem/std_nbdcache.sv
