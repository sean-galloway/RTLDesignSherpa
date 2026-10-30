# Filelist for l1_snoop_kmap
# Location: projects/components/cache-ip/common-ip/rtl/filelists/l1_snoop_kmap.f
#
# Combinational {state, snoop} -> {CRRESP, next_state} decode (HAS Table 3.0).
# l1_snoop_resp will instantiate this leaf; the kmap workbook diffs against it.

-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f

$CACHE_COMMON_ROOT/rtl/fub/l1_snoop_kmap.sv
