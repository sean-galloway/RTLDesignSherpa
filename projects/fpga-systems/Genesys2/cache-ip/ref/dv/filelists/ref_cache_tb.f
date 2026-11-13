# ref_cache_tb.f -- one reference cache + the rig memory behind a GAXI CPU port
# (cache-ip common-ip TASK-003 read-after-write check). Env: REPO_ROOT,
# REF_FRAMEWORK_ROOT, CACHE_COMMON_ROOT, JET_PRIME_ROOT (REF_CACHE_SEL 2 = jet-prime direct).
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_hpdcache_top.f
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_cva6_dcache_top.f
+incdir+$REPO_ROOT/projects/components/cache-ip/common-ip/rtl/includes
-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_pkg.f
-f $JET_PRIME_ROOT/rtl/filelists/jet_prime_top.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
$REF_FRAMEWORK_ROOT/dv/ref_cache_tb.sv
