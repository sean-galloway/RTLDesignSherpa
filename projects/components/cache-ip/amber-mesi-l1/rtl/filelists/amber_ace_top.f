# Filelist for amber_ace_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_ace_top.f
#
# ACE top: full coherency master issue ports (read + write). Stub -- own RTL
# added by its task; foreign sources only via their own filelists.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# ACE read/write master transports (complete closures)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_master_wr.f
