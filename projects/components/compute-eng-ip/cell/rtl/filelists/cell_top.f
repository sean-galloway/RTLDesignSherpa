# Filelist for cell_top (slice 1 and beyond).
# Location: projects/components/compute-eng-ip/cell/rtl/filelists/cell_top.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# House reset macros
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Delta node dependency (the cell instantiates one delta_mesh_cell)
-f $REPO_ROOT/projects/components/fabric-gen-ip/delta/rtl/filelists/delta_mesh.f

# ALU-INFER dependencies (slice 3+ will instantiate alu_infer_top)
-f $REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/filelists/alu_infer_top.f

# Cell shared package and slice-1 modules
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_pkg.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_cfg_regs.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_mem_in.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_mem_out.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_rx.sv
$REPO_ROOT/projects/components/compute-eng-ip/cell/rtl/cell_top.sv
