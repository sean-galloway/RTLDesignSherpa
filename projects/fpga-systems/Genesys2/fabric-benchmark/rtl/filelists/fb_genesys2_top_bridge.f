# Genesys 2 board top, leg A (bridge generator).
# fb_mig is a Vivado IP the build creates in the project (fpga/tcl/fb_mig_ip.tcl);
# it is not a source here; Verilator gets rtl/fb_mig_lint_stub.sv in its place.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_bridge.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_genesys2_top.sv
# Verilator stand-ins (each file is `ifdef VERILATOR; Vivado sees nothing)
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_mig_lint_stub.sv
