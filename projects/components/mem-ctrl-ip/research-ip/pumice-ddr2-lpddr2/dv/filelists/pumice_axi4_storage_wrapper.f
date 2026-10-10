# Test wrapper that re-assembles mc_axi4_layer + mc_storage_layer for the
# legacy standalone pumice axi4 layer test.
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_storage_layer.f
$REPO_ROOT/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tb/pumice_axi4_storage_wrapper.sv
