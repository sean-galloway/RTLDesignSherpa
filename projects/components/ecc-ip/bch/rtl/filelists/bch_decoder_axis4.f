# Filelist for bch_decoder_axis4
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_axis4.f
#
# The component's AXI4-Stream integration top: bch_decoder_core wrapped in the
# house axis4_slave / axis4_master skid wrappers. A consumer that wants a
# stream interface includes THIS list; one that wants the bare handshake plus
# the raw per-block verdict includes bch_decoder_core.f instead.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_core.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_slave.f
-f $REPO_ROOT/rtl/amba/filelists/axis4_master.f

$REPO_ROOT/projects/components/ecc-ip/bch/rtl/top/bch_decoder_axis4.sv
