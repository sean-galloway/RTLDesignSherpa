# Filelist for key_equation_solver_euclid
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/key_equation_solver_euclid.f
#
# Level 2: the inversionless Euclidean solver, 8t+8 gf_mul in generate loops
# (no separate PE module). Uses `ALWAYS_FF_RST.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/key_equation_solver_euclid.sv
