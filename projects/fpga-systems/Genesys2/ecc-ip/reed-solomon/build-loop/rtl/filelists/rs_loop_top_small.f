# Filelist for rs_loop_top -- small RS(64,56) t=4 profile for the Nexys A7.
# Location: projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/build-loop/rtl/filelists/rs_loop_top_small.f
#
# This is the board top closure with +define+RS_LOOP_SMALL selecting the small
# geometry in rs_loop_cfg_pkg.sv. `make lint`, Vivado, and the cocotb sim all
# consume this closure through the same underlying rs_loop_top.f.

+define+RS_LOOP_SMALL
-f $REPO_ROOT/projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/build-loop/rtl/filelists/rs_loop_top.f
