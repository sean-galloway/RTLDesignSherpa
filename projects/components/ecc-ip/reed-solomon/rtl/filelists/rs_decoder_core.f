# Filelist for rs_decoder_core
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_decoder_core.f
#
# Level 3 deliverable: syndrome unit (twice: receive and re-check), riBM
# solver, Chien search, Forney evaluator, the block and output FIFOs from
# rtl/amba/gaxi and two descriptor skids. The consumer -f includes this list.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/syndrome_unit.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/key_equation_solver_ribm.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/key_equation_solver_euclid.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/chien_search.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/forney_evaluator.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_erasure_unit.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/macro/rs_decoder_core.sv
