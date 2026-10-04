# Filelist for the bch_axi4 engines loopback fixture
# Location: projects/components/ecc-ip/bch/rtl/filelists/bch_axi4_engines_tb.f
#
# The two job engines (reused from reed-solomon) plus a real sdpram memory,
# wired write-engine-to-write-channels and read-engine-to-read-channels.
# Used only by dv/tests/fub/test_bch_axi4_engines.py.

-f $REPO_ROOT/rtl/amba/filelists/sdpram_slave_axi4_axi4.f
-f $REPO_ROOT/projects/components/ecc-ip/reed-solomon/rtl/filelists/rs_axi4_engines.f

$REPO_ROOT/projects/components/ecc-ip/bch/dv/tb/bch_axi4_engines_tb_top.sv
