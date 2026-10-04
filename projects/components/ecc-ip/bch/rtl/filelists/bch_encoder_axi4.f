# Filelist for bch_encoder_axi4
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_axi4.f
#
# The AXI4 memory-to-memory encoder: a read engine feeds bch_encoder_core and a
# write engine drains it, both on one AXI4 master port. A consumer that wants a
# stream instead includes bch_encoder_axis4.f; one that wants the bare handshake
# includes bch_encoder_core.f.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_pkg.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_core.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_engines.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_beat_packer.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/top/bch_encoder_axi4.sv
