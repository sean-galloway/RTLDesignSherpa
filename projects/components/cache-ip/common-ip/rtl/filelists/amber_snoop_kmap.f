# Filelist for amber_snoop_kmap
# Location: projects/components/cache-ip/common-ip/rtl/filelists/amber_snoop_kmap.f
#
# Combinational {state, snoop} -> {CRRESP, next_state} decode (HAS Table 3.0).
# amber_snoop_resp will instantiate this leaf; the kmap workbook diffs against it.

-f $CACHE_COMMON_ROOT/rtl/filelists/amber_pkg.f

$CACHE_COMMON_ROOT/rtl/fub/amber_snoop_kmap.sv
