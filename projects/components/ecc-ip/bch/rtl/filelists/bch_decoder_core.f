# Filelist for bch_decoder_core
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_core.f
#
# Binary BCH decoder core: bch_pkg, the three gate-green fubs it integrates,
# and the macro wrapper. Uses `ALWAYS_FF_RST, so reset_defs must be on the
# include path.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_syndrome_unit.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_key_equation_solver.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_chien_search.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/macro/bch_decoder_core.sv
