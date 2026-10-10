# Filelist for scoria_char_harness -- the board harness behind the pins.
#
# ORDER MATTERS, for the reason scoria_char_macro.f records: scoria_pkg must
# precede anything referencing memtype_e, and mem_char_pkg must precede
# anything referencing mem_variant_e. The macro closure carries scoria_pkg, so
# it comes first; the shared framework blocks carry mem_char_pkg.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# The char macro, which carries scoria_pkg, the controller closure and the
# shared char engine.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/filelists/scoria_char_macro.f

# Shared harness instruments, listed DIRECTLY because the framework ships no
# filelists for them -- the same way pumice's board filelist pulls them. Only
# char_engine_block and chargen_regs have lists of their own.
#
# mem_char_pkg FIRST: harness_csr takes a mem_variant_e port, and the package
# must precede it or the failure reads as a missing type rather than a
# misordered list.
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/mem_char_pkg.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/harness_csr.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_cmd_delay.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/dfi_rddata_delay.sv
$REPO_ROOT/projects/fpga-systems/rtl/mem_char_framework/rtl/led_status_driver.sv

# Host transport: UART -> AXI4-Lite, the shared converter.
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f

# The generated 1x3 config bridge.
-f $REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/bridges/filelists/bridge_scoria_char_axil.f

# The DFI adapter is NOT here: it is instantiated by the board TOP, not the
# harness, because it belongs with the PHY it feeds.

$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/rtl/scoria_char_harness.sv
