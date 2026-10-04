# Filelist for the BCH AXI4 codec loop fixture
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_axi4_loop_tb.f
#
# Both AXI4 codec tops plus three sdpram memories, wired messages -> encode ->
# decode -> messages. Used only by dv/tests/fub/test_bch_axi4_loop.py.

-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_axi4.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

$REPO_ROOT/projects/components/ecc-ip/bch/dv/tb/bch_axi4_loop_tb_top.sv
