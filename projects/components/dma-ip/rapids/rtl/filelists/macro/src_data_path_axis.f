# RAPIDS Source Data Path with AXIS Interface File List
# Location: projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis.f
# Purpose: Source Data Path with AXIS Master Interface (Memory -> AXI Read -> SRAM -> Drain -> AXIS)

# Include base source_data_path dependencies
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path.f

# Includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module (AXIS wrapper)
$REPO_ROOT/projects/components/dma-ip/rapids/rtl/macro/src_data_path_axis.sv
