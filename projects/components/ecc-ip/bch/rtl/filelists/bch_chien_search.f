# Filelist for bch_chien_search
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_chien_search.f
#
# BCH Chien search: bch_pkg plus t+1 Horner cells (two gf_mul_const each).
# Uses `ALWAYS_FF_RST, so reset_defs must be on the include path.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/fub/bch_chien_search.sv
