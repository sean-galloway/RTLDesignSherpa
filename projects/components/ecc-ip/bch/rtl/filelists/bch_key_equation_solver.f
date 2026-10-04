# Filelist for bch_key_equation_solver
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_key_equation_solver.f
#
# BCH key-equation solver: bch_pkg plus the imported Reed-Solomon riBM array.
# The riBM filelist pulls in ribm_pe and reset_defs; bch_pkg pulls in gf_pkg.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/key_equation_solver_ribm.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/fub/bch_key_equation_solver.sv
