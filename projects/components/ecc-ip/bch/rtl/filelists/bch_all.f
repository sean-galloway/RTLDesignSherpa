# Master filelist for the bch component
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_all.f
#
# The lint closure for rtl/Makefile (AREA := bch). Every module in the
# component appears here through its own list. The GF(2^m) primitives are
# imported from the reed-solomon component per PRD D7.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f

# Imported GF layer from reed-solomon (via its own filelists: cross-area
# sources must be -f'd, never hand-listed — bin/filelist_registry.py --audit)
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_mul_const.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_syndrome_cell.f

# House infrastructure used by the encoder and wrappers
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

# BCH blocks (each through its own list; verilator dedupes the repeated
# bch_pkg.f / reset_defs.f pulls)
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_core.f

# Imported Reed-Solomon riBM array for the key-equation solver
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/key_equation_solver_ribm.f

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_core.f

# Board-facing wrappers and bring-up utilities (TASK-006)
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_beat_packer.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_error_injector.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_axis4.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_axis4.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_axi4.f
