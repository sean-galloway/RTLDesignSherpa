# Filelist for the rapids tile harness's endpoint models (rapids TASK-032):
# the cells and cores RAPIDS talks to on its CXS links.
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids-tile/filelists/tile_injectors.f

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv
-f $REPO_ROOT/rtl/amba/filelists/axis4_master_injector.f

$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids-tile/rtl/tile_cell_tx.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids-tile/rtl/tile_credit_rx.sv
