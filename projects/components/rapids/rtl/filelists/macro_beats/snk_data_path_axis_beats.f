# RAPIDS Sink Data Path with AXIS Interface File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_axis_beats.f
# Purpose: Sink Data Path with AXIS Slave Interface (AXIS -> Fill -> SRAM -> AXI Write -> Memory)

# Include base sink_data_path dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module (AXIS wrapper)
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_data_path_axis_beats.sv
