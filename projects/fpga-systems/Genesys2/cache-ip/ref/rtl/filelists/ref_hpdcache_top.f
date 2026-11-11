# ref_hpdcache_top: the vendored HPDcache behind the pair rig's CPU / memory ports
# (cache-ip common-ip TASK-003). Consumer: ref_genesys2_top.f.
-f $REPO_ROOT/vendor/filelists/cv_hpdcache.f
# block-RAM implementations of the HPDcache SRAM macros
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/hpdcache_sram_1rw.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/hpdcache_sram_wbyteenable_1rw.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/cache-ip/ref/rtl/ref_hpdcache_top.sv
