# Filelist for l1_cpu_frontend
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_frontend.f
#
# CPU-facing GAXI slave (MAS ch02_blocks/09 + ch03_interfaces/01): latches
# the packed {addr, we, be, wdata} request, presents a single-cycle req_valid
# to l1_control, stages the response in a gaxi_fifo_sync DEPTH=2
# (DECISION D-6) so cpu_rsp_rd_data holds under cpu_rsp_rd_ready low.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

# Response staging queue (DECISION D-6)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$CACHE_COMMON_ROOT/rtl/fub/l1_cpu_frontend.sv
