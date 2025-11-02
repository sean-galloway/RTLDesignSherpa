# Filelist for simple_sram module
# Location: projects/components/stream/rtl/filelists/fub/simple_sram.f

# Include directories
+incdir+$REPO_ROOT/projects/components/stream/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Simple SRAM module (no packages needed)
$REPO_ROOT/projects/components/stream/rtl/stream_fub/simple_sram.sv
