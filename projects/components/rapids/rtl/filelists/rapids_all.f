# RAPIDS Master Filelist
# Location: projects/components/rapids/rtl/filelists/rapids_all.f
# Purpose: Complete RAPIDS component for linting (all FUB and macro modules)

# Include directories
+incdir+$REPO_ROOT/projects/components/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Package files
$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv
$REPO_ROOT/projects/components/rapids/rtl/includes/rapids_pkg.sv

# Include FUB modules with filelists
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/descriptor_engine.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/scheduler.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/ctrlrd_engine.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f

# FUB modules without individual filelists (add directly)
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/simple_sram.sv
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/sink_sram_control.sv
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/sink_axi_write_engine.sv
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/source_sram_control.sv
$REPO_ROOT/projects/components/rapids/rtl/rapids_fub/source_axi_read_engine.sv

# Include all macro module filelists
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro/scheduler_group.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro/scheduler_group_array.f
-f $REPO_ROOT/projects/components/rapids/rtl/filelists/macro/monbus_axil_group.f
