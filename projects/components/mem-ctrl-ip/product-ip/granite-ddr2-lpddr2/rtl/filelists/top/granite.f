# granite.f - the product's plane selection (common-ip only)
#
# Per common_has ch5.2 a product is a configuration of the common stack,
# not a new RTL tree: this filelist IS the SKU's plane selection.
#
# Plane selection per config/product_config.md:
#   mc_axi4_plane        - AXI4 front end
#   mc_xddr2_entry_store - storage-lite N=1 in-order seam (replaces mc_storage_plane)
#   mc_init_plane        - JEDEC init + MR shadow + PHY init handshake
#   mc_scheduler_plane   - pick machinery + common v2 children (external-init mode)
#   mc_training_plane    - shell composing the LPDDR2 clients
#   mc_dfi_2p1_plane     - command / write / read pipelines + CDC
#   (mc_storage_plane    - ABSENT)
#   (mc_ras_plane        - ABSENT)

-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/includes/granite_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_entry_store.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_head_records.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_init_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_scheduler_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_dfi_2p1_plane.f
# product top
$REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv
