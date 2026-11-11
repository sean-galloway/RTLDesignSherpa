# Filelist for the vendored CEA / OpenHW HPDcache (cache-ip common-ip TASK-003)
# Location: vendor/filelists/cv_hpdcache.f
#
# Upstream RTL, see vendor/cv-hpdcache/PROVENANCE.md. Order follows upstream
# rtl/hpdcache.Flist (package first), then the behavioural SRAM macros and
# the memory-to-AXI adapters the reference wrapper uses. Consumer:
# projects/fpga-systems/Genesys2/cache-ip/ref (ref_hpdcache_top).

+incdir+$REPO_ROOT/vendor/cv-hpdcache/rtl/include
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_pkg.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/utils/hpdcache_mem_req_read_arbiter.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/utils/hpdcache_mem_req_write_arbiter.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_demux.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_lfsr.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_sync_buffer.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_fifo_reg.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_fifo_reg_initialized.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_fxarb.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_rrarb.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_mux.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_decoder.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_1hot_to_binary.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_prio_1hot_encoder.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_prio_bin_encoder.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_sram.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_sram_wbyteenable.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_sram_wmask.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_regbank_wbyteenable_1rw.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_regbank_wmask_1rw.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_data_downsize.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_data_upsize.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/hpdcache_data_resize.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hwpf_stride/hwpf_stride_pkg.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hwpf_stride/hwpf_stride.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hwpf_stride/hwpf_stride_arb.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hwpf_stride/hwpf_stride_wrapper.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_amo.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_cmo.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_core_arbiter.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_ctrl.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_ctrl_pe.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_memctrl.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_cbuf.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_miss_handler.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_mshr.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_rtab.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_uncached.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_victim_plru.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_victim_random.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_victim_sel.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_wbuf.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/hpdcache_flush.sv
# the 1rw and wbyteenable SRAM macros are supplied by the consumer (Vivado maps
# upstream's behavioural models to registers: see ref/rtl/hpdcache_sram_1rw.sv);
# the wmask model stays for the generate branches this configuration does not take
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/common/macros/behav/hpdcache_sram_wmask_1rw.sv
# the two memory-to-AXI adapters import the PULP axi_pkg (vendor/pulp-axi)
$REPO_ROOT/vendor/pulp-axi/src/axi_pkg.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/utils/hpdcache_mem_to_axi_read.sv
$REPO_ROOT/vendor/cv-hpdcache/rtl/src/utils/hpdcache_mem_to_axi_write.sv
