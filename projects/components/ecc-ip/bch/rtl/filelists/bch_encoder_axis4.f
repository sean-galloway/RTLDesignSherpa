# Filelist for bch_encoder_axis4
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_axis4.f
#
# The component's AXI4-Stream integration top: bch_encoder_core wrapped in the
# house axis4_slave / axis4_master skid wrappers. A consumer that wants a
# stream interface includes THIS list; one that wants the bare handshake
# includes bch_encoder_core.f instead.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_core.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/top/bch_encoder_axis4.sv
