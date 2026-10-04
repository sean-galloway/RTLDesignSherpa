# Filelist for bch_error_injector
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_error_injector.f
#
# BCH bit-granular error injector: bch_pkg plus reset_defs. Self-contained;
# no GF arithmetic instances are required because the injector only inverts bits.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/fub/bch_error_injector.sv
