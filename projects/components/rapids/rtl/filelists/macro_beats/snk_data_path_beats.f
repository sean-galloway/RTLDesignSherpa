# RAPIDS Sink Data Path Macro File List
# Location: projects/components/rapids/rtl/filelists/macro_beats/snk_data_path_beats.f
# Purpose: Sink Data Path (Fill -> SRAM -> AXI Write -> Memory)

# Include SRAM controller dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f

# Include AXI write engine dependencies
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub_beats/axi_write_engine_beats.f

# Includes
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# DUT module
$REPO_ROOT/projects/components/rapids/rtl/macro_beats/snk_data_path_beats.sv
