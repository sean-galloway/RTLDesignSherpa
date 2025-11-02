# Filelist for arbiter_round_robin_weighted module
# Location: rtl/common/filelists/arbiter_round_robin_weighted.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh


# Dependencies
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
# arbiter_round_robin_weighted module
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin_weighted.sv
