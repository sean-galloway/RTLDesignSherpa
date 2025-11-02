# Filelist for grayj2bin module
# Location: rtl/common/filelists/grayj2bin.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh


# Dependencies
# grayj2bin module
$REPO_ROOT/rtl/common/find_first_set.sv
$REPO_ROOT/rtl/common/find_last_set.sv
$REPO_ROOT/rtl/common/leading_one_trailing_one.sv
$REPO_ROOT/rtl/common/grayj2bin.sv
