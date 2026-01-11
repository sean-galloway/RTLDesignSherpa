# RAPIDS Source Data Path with AXIS Interface File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/src_data_path_axis_beats.f
# Purpose: Source Data Path with AXIS Master Interface (Memory -> AXI Read -> SRAM -> Drain -> AXIS)

# Include base source_data_path dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/src_data_path_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module (AXIS wrapper)
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/src_data_path_axis_beats.sv
