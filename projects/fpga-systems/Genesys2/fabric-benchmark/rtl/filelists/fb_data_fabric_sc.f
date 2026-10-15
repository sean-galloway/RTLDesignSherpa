# Leg B2 data fabric under test: Xilinx SmartConnect, through its IP-integrator
# block design. The design itself (fb_sc.bd and its generated fb_sc_wrapper) is
# made by fpga/tcl/vendor_ip.tcl under fpga/ip/build and read from there by the
# Vivado flows; SmartConnect's HDL is encrypted, so this leg has no Verilator
# sim (PRD section 5). This list carries the leg wrapper only.
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/generated/fb_data_fabric_sc/fb_data_fabric.sv
