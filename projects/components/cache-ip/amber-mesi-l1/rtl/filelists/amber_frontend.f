# Filelist for amber_cpu_frontend
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_frontend.f
#
# CPU-facing GAXI slave (MAS ch02_blocks/09 + ch03_interfaces/01): latches
# the packed {addr, we, be, wdata} request, presents a single-cycle req_valid
# to amber_control, stages the response in a gaxi_fifo_sync DEPTH=2
# (DECISION D-6) so cpu_rsp_rd_data holds under cpu_rsp_rd_ready low.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# Response staging queue (DECISION D-6)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$AMBER_ROOT/rtl/fub/amber_cpu_frontend.sv
