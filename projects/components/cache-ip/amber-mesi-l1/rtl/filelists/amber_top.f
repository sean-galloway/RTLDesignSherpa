# Filelist for amber_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_top.f
#
# Top-level L1 cache with AXI4 downstream and ACE snoop ports. Composes the
# core slice plus the AMBA transport closures it sits on. Own RTL: the top
# itself; foreign sources only via their own filelists.

# Shared amber package
-f $AMBER_ROOT/rtl/filelists/amber_pkg.f

# The core closure (nine landed FUBs + their house deps)
-f $AMBER_ROOT/rtl/filelists/amber_core.f

# AXI4 read/write master monitors (complete closures)
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_rd_monlite.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_master_wr_monlite.f

# ACE snoop slave transport (complete closure)
-f $REPO_ROOT/rtl/amba/filelists/axi4ace_snoop_slave.f

# Pair-rig bench memory slave (AXI4 SDP RAM, complete closure)
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# Monbus arbiter closure
-f $REPO_ROOT/rtl/amba/filelists/monbus_arbiter.f

# The pair-rig top itself
$AMBER_ROOT/rtl/top/amber_top.sv
