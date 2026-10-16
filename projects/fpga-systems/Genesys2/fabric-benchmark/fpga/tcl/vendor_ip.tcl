#==============================================================================
# vendor_ip.tcl -- generate the Vivado-built fabric legs of the K7 benchmark
#==============================================================================
# Everything comes from rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl,
# which bin/gen_fabric_legs.py writes from the same TOML + connectivity CSV as
# the bridge leg. Nothing here is a hand-picked parameter.
#
#   fb_xbar   leg B1 from the IP catalog (axi_crossbar). The sim and the OOC
#             build use the HDL wrapper; this copy exists so
#             bin/check_xbar_params.py can prove the wrapper passes exactly
#             the parameters Vivado's own customization produces.
#   fb_sc     leg B2: an IP-integrator block design around smartconnect, one
#             interface port per TOML port (so the wrapper's pins are
#             <port>_<signal>), windows assigned per master, every pair not in
#             the connectivity CSV excluded (DECERR). No AxUSER: SmartConnect's
#             MI ID width is 0 and read-only, so the endpoints select channels
#             by address and B2 carries nothing the other legs do not.
#   fb_mig    MIG 7-series DDR3 for S0 (K3), from
#             rtl/generated/fb_mig_prj/fb_mig.prj (bin/gen_mig_prj.py: the
#             board-proven Genesys 2 pinout, DDR3-800, 4:1 so ui_clk = 100 MHz
#             = the fabric clock, AXI4 128-bit, ID = the fabric's slave ID).
#
# Output: $FB_IP_DIR (default fpga/ip/build), a Vivado project holding both,
# with output products generated. Regenerable, so not committed.
#
#   vivado -mode batch -source fpga/tcl/vendor_ip.tcl
#==============================================================================
set script_dir [file dirname [file normalize [info script]]]
set area       [file normalize "$script_dir/../.."]
set ip_dir     [expr {[info exists ::env(FB_IP_DIR)] ? [file normalize $::env(FB_IP_DIR)] : "$area/fpga/ip/build"}]
source "$area/rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl"

file delete -force $ip_dir
file mkdir $ip_dir
create_project fb_vendor_ip $ip_dir -part $FB_PART -force
set_property target_language Verilog [current_project]

# ---- leg B1: IP-catalog crossbar ----------------------------------------------
puts "\n--- fb_xbar (axi_crossbar) ---"
create_ip -name axi_crossbar -vendor xilinx.com -library ip -module_name fb_xbar
set_property -dict $FB_XBAR_CONFIG [get_ips fb_xbar]
# Vivado may silently clamp or ignore a value: read every key back.
set bad 0
foreach {k v} $FB_XBAR_CONFIG {
    set got [get_property $k [get_ips fb_xbar]]
    if {[string tolower $got] ne [string tolower $v]} {
        puts stderr "ERROR: fb_xbar $k = $got, asked for $v"
        incr bad
    }
}
if {$bad} { exit 1 }
generate_target {instantiation_template synthesis simulation} [get_ips fb_xbar]

# ---- leg B2: SmartConnect block design ------------------------------------------
source "$script_dir/fb_sc_bd.tcl"
fb_create_sc_bd

# ---- S0 memory controller: MIG 7-series DDR3 --------------------------------------
source "$script_dir/fb_mig_ip.tcl"
fb_create_mig $area $FB_DW $FB_SID

puts "\nvendor_ip: fb_xbar + fb_sc + fb_mig generated under $ip_dir"
