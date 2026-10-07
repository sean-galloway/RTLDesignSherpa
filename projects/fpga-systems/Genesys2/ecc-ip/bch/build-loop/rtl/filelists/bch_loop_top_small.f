# Filelist for bch_loop_top -- small BCH(248,224) t=3 profile for the Nexys A7.
# Location: projects/fpga-systems/Genesys2/ecc-ip/bch/build-loop/rtl/filelists/bch_loop_top_small.f
#
# This is the board top closure with +define+BCH_LOOP_SMALL selecting the small
# geometry in bch_loop_cfg_pkg.sv. `make lint`, Vivado, and the cocotb sim all
# consume this closure through the same underlying bch_loop_top.f.

+define+BCH_LOOP_SMALL
-f $REPO_ROOT/projects/fpga-systems/Genesys2/ecc-ip/bch/build-loop/rtl/filelists/bch_loop_top.f
