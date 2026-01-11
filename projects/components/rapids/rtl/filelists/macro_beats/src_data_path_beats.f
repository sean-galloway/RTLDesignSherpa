# RAPIDS Source Data Path Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/src_data_path_beats.f
# Purpose: Source Data Path (Memory -> AXI Read -> SRAM -> Drain)

# Include SRAM controller dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/src_sram_controller_beats.f

# Include AXI read engine dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/axi_read_engine_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/src_data_path_beats.sv
