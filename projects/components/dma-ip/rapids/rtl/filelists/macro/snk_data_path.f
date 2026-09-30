# RAPIDS Sink Data Path Macro File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path.f
# Purpose: Sink Data Path (Fill -> SRAM -> AXI Write -> Memory)

# Include SRAM controller dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_sram_controller.f

# Include AXI write engine dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/fub/axi_write_engine.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/snk_data_path.sv
