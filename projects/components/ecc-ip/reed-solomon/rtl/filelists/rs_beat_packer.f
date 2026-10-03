# Filelist for rs_beat_packer
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_beat_packer.f
#
# Repacks a symbol stream so only a block's last beat is partial, which is what
# rs_decoder_core's in_keep contract requires and what rs_encoder_core does not
# produce when k does not fill a beat (PRD D9b). Self-contained.

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/fub/rs_beat_packer.sv
