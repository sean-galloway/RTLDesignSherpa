# Genesys 2 board top, leg A (bridge generator).
# fb_litedram (S0) is generated toolchain output (bin/gen_litedram.sh, gitignored)
# that only Vivado reads: create_project.tcl adds it. Verilator gets its
# generated port blackbox in its place.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/filelists/fb_harness_bridge.f
$STREAM_CHAR_FRAMEWORK_ROOT/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_genesys2_top.sv
# Verilator stand-ins (each file is `ifdef VERILATOR; Vivado sees nothing)
-f $MISC_ROOT/rtl/filelists/verilator_xilinx_stubs.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/generated/fb_litedram_bb/fb_litedram_bb.sv
