# Filelist for l1_snoop_kmap_test
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_snoop_kmap_test.f
#
# Combinational {state, snoop} -> {CRRESP, next_state} decode (HAS Table 3.0).
# Validation harness only (not instantiated in the design); the kmap
# workbook and the gem5 FSM oracle diff against this module boundary.

-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

$CACHE_COMMON_ROOT/rtl/fub/l1_snoop_kmap_test.sv
