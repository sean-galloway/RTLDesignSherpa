# Filelist for amber_drain
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_drain.f
#
# Drain path: AXI4 write master that evicts dirty lines to downstream memory.
# Stub -- own RTL added by its task.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# AXI4 write-master transport (complete closure; no rtl/amba sources hand-listed)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr.f
