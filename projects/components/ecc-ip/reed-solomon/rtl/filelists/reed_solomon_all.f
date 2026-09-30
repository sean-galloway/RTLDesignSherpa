# Master filelist for the reed-solomon component
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/reed_solomon_all.f
#
# The lint closure for rtl/Makefile (AREA := reed_solomon). Every module in
# the component appears here through its own list. Level 0 GF layer today;
# the encoder and decoder blocks join as they land.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_pkg.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_mul_const.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_mul.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_inv.sv

# Level 1 and Level 3 (encoder side)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_lfsr_encoder.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/rs_encoder_core.sv

# Decoder side
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/gf_syndrome_cell.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/syndrome_unit.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/gf/ribm_pe.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/key_equation_solver_ribm.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/key_equation_solver_euclid.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/chien_search.sv
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/forney_evaluator.sv
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/rs_decoder_core.sv

# Test stimulus
$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/rs_error_injector.sv
