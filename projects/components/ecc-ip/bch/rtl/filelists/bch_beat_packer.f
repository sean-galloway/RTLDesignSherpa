# Filelist for bch_beat_packer
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_beat_packer.f
#
# Repacks a bit stream so only a block's last beat is partial, which is what
# bch_decoder_core's in_keep contract requires and what bch_encoder_core does
# not produce when k does not fill a beat. Self-contained.

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/fub/bch_beat_packer.sv
