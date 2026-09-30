# Filelist for the AXI4 codec loop fixture
# Location: projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_loop_tb.f
#
# Both AXI4 codec tops plus three sdpram memories, wired messages -> encode ->
# decode -> messages. Used only by dv/tests/fub/test_rs_axi4_loop.py.

-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_encoder_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_decoder_axi4.f
-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f

$REPO_ROOT/projects/components/ecc-ip/reed-solomon/dv/tb/rs_axi4_loop_tb_top.sv
