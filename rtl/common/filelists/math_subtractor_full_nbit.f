# Filelist for math_subtractor_full_nbit module
# Location: rtl/common/filelists/math_subtractor_full_nbit.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh


# Dependencies
$REPO_ROOT/rtl/common/math_adder_full.sv
$REPO_ROOT/rtl/common/math_subtractor_full.sv

# math_subtractor_full_nbit module
$REPO_ROOT/rtl/common/math_subtractor_full_nbit.sv
