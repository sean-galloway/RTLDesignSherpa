# Filelist for pumice_top — integration of all three macros.

# Include directories
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/includes
+incdir+$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/regs/generated/rtl
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Pull in the sub-macros + CSR slave via their own filelists.
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/axi_frontend_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/command_scheduler_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/data_path_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/dfi_v21_interface_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/pumice_core_macro.f
-f $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/filelists/macro/pumice_csr_slave.f

# This top module
$REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/top/OLD/pumice_top.sv
