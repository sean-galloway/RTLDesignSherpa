# Filelist for johnson2bin module
# Location: rtl/cdc/filelists/johnson2bin.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies -- owned by rtl/common, so -f include rather than hand-list.
# leading_one_trailing_one.f carries find_first_set and find_last_set itself.
-f $REPO_ROOT/rtl/common/filelists/leading_one_trailing_one.f

# johnson2bin module
$REPO_ROOT/rtl/cdc/johnson2bin.sv
