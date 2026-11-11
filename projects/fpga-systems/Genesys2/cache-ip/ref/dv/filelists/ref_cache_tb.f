# ref_cache_tb.f -- one reference cache + the rig memory behind a GAXI CPU port
# (cache-ip common-ip TASK-003 read-after-write check). Env: REPO_ROOT,
# REF_FRAMEWORK_ROOT.
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_hpdcache_top.f
-f $REF_FRAMEWORK_ROOT/rtl/filelists/ref_cva6_dcache_top.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
$REF_FRAMEWORK_ROOT/dv/ref_cache_tb.sv
