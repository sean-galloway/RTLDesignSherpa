# Filelist for the aged-fifo + matrix-arbiter macro test
# (common-ip/dv/tests/macro/test_mc_age_arb.py).
#
# Closure: the two blocks under test -> tb top.  No pkg dependency: both
# modules stand alone (reset_defs.svh comes from the includes below).

+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
+incdir+$REPO_ROOT/rtl/common

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_age_fifo.sv
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_matrix_arbiter.sv

$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_age_arb_macro_tb_top.sv
