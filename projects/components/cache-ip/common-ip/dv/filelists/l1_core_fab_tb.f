# Filelist for l1_core_fab_tb
# Location: projects/components/cache-ip/common-ip/dv/filelists/l1_core_fab_tb.f
#
# Testbench wrapper that composes the restructured l1_core aggregate with
# the ACE snoop responder, presenting the same external port list as the
# pre-restructure l1_core so test_l1_core's stimulus survives unchanged.

# The aggregate core (CPU plane + coherence core plane)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_core.f

# ACE snoop responder (the fabric-plane FUB; closed here for the TB)
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_snoop_resp.f

# The TB wrapper itself
$CACHE_COMMON_ROOT/dv/tb/l1_core_fab_tb.sv
