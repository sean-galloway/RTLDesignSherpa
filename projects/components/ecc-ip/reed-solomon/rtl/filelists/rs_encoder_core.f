# Filelist for rs_encoder_core
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_core.f
#
# Level 3 deliverable: the LFSR encoder plus an output skid buffer from
# rtl/amba/gaxi. The consumer -f includes this list and nothing else.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/gf_lfsr_encoder.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/rs_encoder_core.sv
