# Filelist for rs_loop_genesys2_top -- Genesys 2 (Kintex-7 XC7K325T-2) build.
# Location: projects/fpga-systems/Genesys2/reed-solomon/build-loop/rtl/filelists/rs_loop_genesys2_top.f
#
# Reuses the entire Nexys top filelist (harness + DUT + host front-end + board
# helpers + rs_loop_top itself) and adds only the Genesys 2 board wrapper,
# which turns the 200 MHz LVDS sysclk into 100 MHz via an MMCM and instantiates
# rs_loop_harness unchanged. IBUFDS / MMCME2_BASE / BUFG are Xilinx unisim
# primitives supplied by Vivado (this is a Vivado-only target).

# ---- Everything the Nexys top needs (includes rs_loop_top.sv) ----
-f $REPO_ROOT/projects/fpga-systems/Genesys2/reed-solomon/build-loop/rtl/filelists/rs_loop_top.f

# ---- Genesys 2 board wrapper (MMCM + pin mapping) ----
$REPO_ROOT/projects/fpga-systems/Genesys2/reed-solomon/build-loop/rtl/rs_loop_genesys2_top.sv
