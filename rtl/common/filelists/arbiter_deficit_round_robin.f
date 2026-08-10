# Filelist for arbiter_deficit_round_robin module
# Location: rtl/common/filelists/arbiter_deficit_round_robin.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies (the shared base RR core and its priority encoder)
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv

# arbiter_deficit_round_robin module
$REPO_ROOT/rtl/common/arbiter_deficit_round_robin.sv
