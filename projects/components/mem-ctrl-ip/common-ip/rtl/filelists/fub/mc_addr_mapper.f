# Filelist for mc_addr_mapper (common-ip; extracted in Phase 2 Task 2)
# Address decode: one runtime knob (bank_lsb) + optional XOR hash; andesite's
# bank group rides HAS_BG. Leaf FUB: pkg + the module only.
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_addr_mapper.sv
