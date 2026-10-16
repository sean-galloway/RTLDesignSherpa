# Genesys 2 board top, leg B2 (Xilinx SmartConnect). The SmartConnect block
# design (fb_sc_wrapper) is created in the Vivado project (fpga/tcl/fb_sc_bd.tcl)
# and create_project.tcl adds fb_litedram; SmartConnect's HDL is encrypted, so
# this leg has no Verilator lint or sim (PRD section 5).
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_sc.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_genesys2_top.sv
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/generated/fb_litedram_bb/fb_litedram_bb.sv
