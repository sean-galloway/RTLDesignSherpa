# Filelist for kestrel_mem_loader
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/fub/kestrel_mem_loader.f
#
# Board glue: AXIL slave SRAM loader (load-then-run; mutual exclusion by
# protocol, not a contention arbiter). Composes the repo's skid-buffered
# AXIL leaf slaves -- they come in through their OWN filelists; this file
# never hand-lists rtl/amba sources.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Package (halt causes)
-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f

# AXIL leaf slaves (complete closures per the amba filelists)
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f

# Loader module
$KESTREL_ROOT/rtl/fub/kestrel_mem_loader.sv
