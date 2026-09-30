# Filelist for rs_encoder_axi4
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_axi4.f
#
# The AXI4 memory-to-memory encoder: a read engine feeds rs_encoder_core and a
# write engine drains it, both on one AXI4 master port. A consumer that wants a
# stream instead includes rs_encoder_axis4.f; one that wants the bare handshake
# includes rs_encoder_core.f.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_core.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_engines.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/axi4/rs_encoder_axi4.sv
