# granite.f - the product's layer selection (common-ip only)
#
# Per common_has ch5.2 a product is a configuration of the common stack,
# not a new RTL tree: this filelist IS the SKU's layer selection.
#
# Layer selection per config/product_config.md:
#   mc_axi4_layer        - AXI4 front end
#   mc_xddr2_entry_store - storage-lite N=1 in-order seam (replaces mc_storage_layer)
#   mc_scheduler_layer   - pick machinery + common v2 children
#   mc_training_layer    - shell composing the LPDDR2 clients
#   mc_dfi_2p1_layer     - command / write / read pipelines + CDC
#   (mc_storage_layer    - ABSENT)
#   (mc_ras_layer        - ABSENT)

-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/includes/granite_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_entry_store.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_scheduler_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_dfi_2p1_layer.f
# product top
$REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv
