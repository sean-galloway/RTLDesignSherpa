# Filelist for rs_encoder_axis4
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_axis4.f
#
# The component's AXI4-Stream integration top: rs_encoder_core wrapped in the
# house axis4_slave / axis4_master skid wrappers. A consumer that wants a
# stream interface includes THIS list; one that wants the bare handshake
# includes rs_encoder_core.f instead.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_core.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_beat_packer.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/axis4/rs_encoder_axis4.sv
