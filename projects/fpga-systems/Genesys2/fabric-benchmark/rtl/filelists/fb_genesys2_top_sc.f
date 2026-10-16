# Genesys 2 board top, leg B2 (Xilinx SmartConnect). The SmartConnect block
# design (fb_sc_wrapper) and fb_mig are created in the Vivado project
# (fpga/tcl/fb_sc_bd.tcl, fb_mig_ip.tcl); SmartConnect's HDL is encrypted, so
# this leg has no Verilator lint or sim (PRD section 5).
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_sc.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_genesys2_top.sv
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_mig_lint_stub.sv
