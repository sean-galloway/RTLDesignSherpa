# Filelist for amber_top
# Location: projects/components/cache-ip/amber-mesi-l1/rtl/filelists/amber_top.f
#
# Top-level L1 cache with AXI4 downstream and ACE snoop ports. Composes the
# three cache-ip planes (CPU plane, coherence-core plane, AXI4 fabric plane)
# plus the D-7 monbus_arbiter and boundary reset_sync. Own RTL: the top
# itself; foreign sources only via their own filelists.

# CPU plane (l1_cpu_frontend)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_cpu_plane.f

# Coherence-core plane (l1_control, arrays, repl, fill/drain, monlite)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_coh_core.f

# AXI4 fabric plane (l1_snoop_resp, axi4_master_rd/wr_monlite, D-8 sideband)
-f $CACHE_COMMON_ROOT/rtl/filelists/plane/l1_axi4_plane.f

# Boundary reset synchronizer (amber_top input aresetn is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Pair-rig bench memory slave (AXI4 SDP RAM, complete closure); carried here
# because amber_pair_rig_tb merges amber_top.f + amber_pair_fabric.f.
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

# The pair-rig top itself
$AMBER_ROOT/rtl/top/amber_top.sv
