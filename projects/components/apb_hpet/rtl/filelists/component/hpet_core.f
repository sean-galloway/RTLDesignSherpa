# HPET Core Logic File List
# Location: rtl/amba/components/hpet/filelists/component/hpet_core.f
# Purpose: HPET timer functionality and core logic

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies - Common modules
$REPO_ROOT/rtl/common/counter_bin.sv

# Core module
$REPO_ROOT/rtl/amba/components/hpet/hpet_core.sv
