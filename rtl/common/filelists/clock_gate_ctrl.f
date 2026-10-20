# Filelist for clock_gate_ctrl module
# Location: rtl/common/filelists/clock_gate_ctrl.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies
-f $REPO_ROOT/rtl/common/filelists/icg.f

# clock_gate_ctrl module
$REPO_ROOT/rtl/common/clock_gate_ctrl.sv
