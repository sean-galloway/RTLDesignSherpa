# RAPIDS Source Data Path Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path.f
# Purpose: Source Data Path (Memory -> AXI Read -> SRAM -> Drain)

# Include SRAM controller dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/src_sram_controller.f

# Include AXI read engine dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/axi_read_engine.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/src_data_path.sv
