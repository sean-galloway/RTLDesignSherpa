# ref_cva6_dcache_top: the vendored CVA6 write-back dcache behind the pair rig's
# CPU / memory ports (cache-ip common-ip TASK-003). Consumer: ref_genesys2_top.f
# (REF_CACHE=cva6).
+incdir+$REPO_ROOT/vendor/pulp-axi/include
-f $REPO_ROOT/vendor/filelists/cva6_dcache.f
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/tc_sram.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/tc_sram_wrapper.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/ref_cva6_cfg_pkg.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/ref_cva6_dcache_top.sv
