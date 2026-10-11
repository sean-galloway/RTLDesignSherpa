# granite.f - the product's layer selection (common-ip only)
#
# Per common_has ch5.2 a product is a configuration of the common stack,
# not a new RTL tree: this filelist IS the SKU's layer selection. There is
# deliberately no granite_core.sv yet - the first build composes the top
# after the layer wrappers dissolve into common-ip (TASK-001 in this
# product's vault area). No research-ip filelist may appear here.
#
# Layer selection per config/product_config.md:
#   mc_axi4_layer      - AXI4 front end (lite SKU widths at instantiation)
#   mc_storage_layer   - lite configuration (N=1 in-order seam)
#   mc_scheduler_layer - pick machinery + common v2 children
#   mc_training_layer  - shell; composes the LPDDR2 clients
#   mc_dfi_2p1_layer   - command / write / read pipelines + CDC
#   (mc_ras_layer      - deliberately absent: true bypass)
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/includes/granite_pkg.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_storage_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_scheduler_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_layer.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_dfi_2p1_layer.f
