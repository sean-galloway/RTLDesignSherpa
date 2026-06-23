# Filelist for ddr2_lpddr2_top — integration of all three macros.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/regs/generated/rtl
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Pull in the sub-macros + CSR slave via their own filelists.
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/axi_frontend_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/command_scheduler_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/data_path_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/dfi_v21_interface_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/ddr2_lpddr2_core_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/filelists/macro/ddr2_lpddr2_csr_slave.f

# This top module
$REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/rtl/top/ddr2_lpddr2_top.sv
