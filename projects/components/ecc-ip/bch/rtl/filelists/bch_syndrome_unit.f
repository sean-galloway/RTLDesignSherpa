# Filelist for bch_syndrome_unit
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_syndrome_unit.f
#
# BCH odd-syndrome unit: bch_pkg plus the imported gf_syndrome_cell. Uses
# `ALWAYS_FF_RST, so reset_defs must be on the include path.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_syndrome_cell.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/fub/bch_syndrome_unit.sv
