# RAPIDS Sink Data Path with AXIS Interface File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis.f
# Purpose: Sink Data Path with AXIS Slave Interface (AXIS -> Fill -> SRAM -> AXI Write -> Memory)

# Include base sink_data_path dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module (AXIS wrapper)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/snk_data_path_axis.sv
