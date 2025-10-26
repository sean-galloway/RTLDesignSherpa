# Filelist for dataint_crc module
# Location: rtl/common/filelists/dataint_crc.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh


# Dependencies
# dataint_crc module
$REPO_ROOT/rtl/common/dataint_crc_xor_shift.sv
$REPO_ROOT/rtl/common/dataint_crc_xor_shift_cascade.sv
$REPO_ROOT/rtl/common/dataint_crc.sv
