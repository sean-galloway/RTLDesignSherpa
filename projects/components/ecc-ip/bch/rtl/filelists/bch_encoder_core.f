# Filelist for bch_encoder_core
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_core.f
#
# Systematic binary BCH encoder core: bch_pkg, the bit-LFSR, and an output
# skid buffer. Uses `ALWAYS_FF_RST, so reset_defs must be on the include path.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/macro/bch_encoder_core.sv
