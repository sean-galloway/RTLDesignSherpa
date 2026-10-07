# Filelist for amber_fill
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_fill.f
#
# Fill path: AXI4 read master that fetches cache lines from downstream memory.
# Stub -- own RTL added by its task.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# AXI4 read-master transport (complete closure; no rtl/amba sources hand-listed)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd.f
