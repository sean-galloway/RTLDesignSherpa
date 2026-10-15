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
#             the connectivity CSV excluded (DECERR), AxUSER = {slot, id} wide
#             enough to rebuild the slave-side ID (SmartConnect's MI ID width
#             is 0 and read-only).
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
puts "\n--- fb_sc (smartconnect block design) ---"
create_bd_design fb_sc
set sc [create_bd_cell -type ip -vlnv xilinx.com:ip:smartconnect:1.0 sc]
set_property -dict [list CONFIG.NUM_SI [llength $FB_MASTERS] CONFIG.NUM_MI [llength $FB_SLAVES] \
                         CONFIG.NUM_CLKS 1] $sc
set clk [create_bd_port -dir I -type clk -freq_hz $FB_FREQ_HZ aclk]
set rst [create_bd_port -dir I -type rst aresetn]
set_property CONFIG.POLARITY ACTIVE_LOW $rst
connect_bd_net $clk [get_bd_pins sc/aclk]
connect_bd_net $rst [get_bd_pins sc/aresetn]

set busifs {}
set i 0
foreach m $FB_MASTERS {
    lassign $m name mode
    set p [create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 $name]
    set_property -dict [list CONFIG.PROTOCOL AXI4 CONFIG.DATA_WIDTH $FB_DW CONFIG.ADDR_WIDTH $FB_AW \
        CONFIG.ID_WIDTH $FB_MID CONFIG.ARUSER_WIDTH $FB_SID CONFIG.AWUSER_WIDTH $FB_SID \
        CONFIG.READ_WRITE_MODE $mode CONFIG.HAS_REGION 0 CONFIG.FREQ_HZ $FB_FREQ_HZ \
        CONFIG.NUM_READ_OUTSTANDING $FB_ACCEPT CONFIG.NUM_WRITE_OUTSTANDING $FB_ACCEPT] $p
    connect_bd_intf_net $p [get_bd_intf_pins [format "sc/S%02d_AXI" $i]]
    lappend busifs $name
    incr i
}
set i 0
foreach s $FB_SLAVES {
    lassign $s name mode base range
    set p [create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 $name]
    set_property -dict [list CONFIG.PROTOCOL AXI4 CONFIG.DATA_WIDTH $FB_DW CONFIG.ADDR_WIDTH $FB_AW \
        CONFIG.READ_WRITE_MODE $mode CONFIG.HAS_REGION 0 CONFIG.FREQ_HZ $FB_FREQ_HZ] $p
    connect_bd_intf_net [get_bd_intf_pins [format "sc/M%02d_AXI" $i]] $p
    lappend busifs $name
    incr i
}
set_property CONFIG.ASSOCIATED_BUSIF [join $busifs ":"] $clk
set_property CONFIG.ASSOCIATED_RESET aresetn $clk

# Windows: map every slave into every master's space, then exclude the pairs
# the connectivity CSV does not connect. An excluded pair answers DECERR, as an
# unconnected pair does in the other two legs.
foreach m $FB_MASTERS {
    set mname [lindex $m 0]
    set reach [dict get $FB_CONN $mname]
    foreach s $FB_SLAVES {
        lassign $s sname mode base range
        set seg [get_bd_addr_segs /$sname/Reg]
        assign_bd_address -offset $base -range $range -target_address_space [get_bd_addr_spaces /$mname] $seg -force
        if {[lsearch -exact $reach $sname] < 0} {
            exclude_bd_addr_seg -target_address_space [get_bd_addr_spaces /$mname] $seg
        }
    }
}

validate_bd_design
# The slave-side ID is rebuilt from AxUSER, so it must reach every MI full width.
foreach s $FB_SLAVES {
    lassign $s sname mode
    foreach {key on} [list ARUSER_WIDTH [expr {$mode ne "WRITE_ONLY"}] AWUSER_WIDTH [expr {$mode ne "READ_ONLY"}]] {
        set w [get_property CONFIG.$key [get_bd_intf_ports /$sname]]
        if {$on && $w != $FB_SID} {
            puts stderr "ERROR: fb_sc $sname $key = $w, need $FB_SID (the {slot, id} the wrapper rebuilds)"
            exit 1
        }
    }
    if {[get_property CONFIG.ID_WIDTH [get_bd_intf_ports /$sname]] != 0} {
        puts "NOTE: fb_sc $sname has an MI ID now; the wrapper's AxUSER-as-ID scheme should be revisited"
    }
}
save_bd_design
set bd_file [get_files fb_sc.bd]
set_property synth_checkpoint_mode None $bd_file
generate_target all $bd_file
make_wrapper -files $bd_file -top -import

# ---- S0 memory controller: MIG 7-series DDR3 --------------------------------------
puts "\n--- fb_mig (mig_7series) ---"
create_ip -name mig_7series -vendor xilinx.com -library ip -version 4.2 -module_name fb_mig
set mig_dir [get_property IP_DIR [get_ips fb_mig]]
file copy -force "$area/rtl/generated/fb_mig_prj/fb_mig.prj" [file join $mig_dir mig_a.prj]
set_property -dict [list CONFIG.XML_INPUT_FILE {mig_a.prj} CONFIG.RESET_BOARD_INTERFACE {Custom} \
                         CONFIG.MIG_DONT_TOUCH_PARAM {Custom} CONFIG.BOARD_MIG_PARAM {Custom}] [get_ips fb_mig]
generate_target {instantiation_template synthesis simulation} [get_ips fb_mig]
# MIG ignores a .prj it cannot parse and falls back to its defaults without an
# error, so read the generated core back: the design point must have landed.
set mig_v [glob "$ip_dir/fb_vendor_ip.gen/sources_1/ip/fb_mig/fb_mig/user_design/rtl/fb_mig_mig.v"]
set text [read [set fh [open $mig_v]]]; close $fh
foreach {param want} [list tCK 2500 nCK_PER_CLK 4 DQ_WIDTH 32 C_S_AXI_DATA_WIDTH $FB_DW C_S_AXI_ID_WIDTH $FB_SID] {
    if {![regexp "parameter\\s+$param\\s+=\\s+(\\d+)" $text -> got] || $got != $want} {
        puts stderr "ERROR: fb_mig $param = [expr {[info exists got] ? $got : {missing}}], expected $want"
        exit 1
    }
}

puts "\nvendor_ip: fb_xbar + fb_sc + fb_mig generated under $ip_dir"
