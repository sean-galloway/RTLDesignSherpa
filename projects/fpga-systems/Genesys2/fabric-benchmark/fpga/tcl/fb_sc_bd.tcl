#==============================================================================
# fb_sc_bd.tcl -- create leg B2's SmartConnect block design in the CURRENT project
#==============================================================================
# One recipe for the vendor-IP project (vendor_ip.tcl) and the B2 board build
# (create_project.tcl, FB_LEG=sc). Everything comes from
# rtl/generated/fb_vendor_ip_cfg/fb_vendor_ip_cfg.tcl (bin/gen_fabric_legs.py),
# the same TOML + connectivity CSV as the other legs: one interface port per
# TOML port (so the wrapper's pins are <port>_<signal>), windows assigned per
# master, every pair not in the connectivity CSV excluded (DECERR).
#
#   fb_create_sc_bd     (expects the fb_vendor_ip_cfg.tcl globals sourced)
#==============================================================================
proc fb_create_sc_bd {} {
    global FB_MASTERS FB_SLAVES FB_DW FB_AW FB_MID FB_FREQ_HZ FB_ACCEPT FB_CONN
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
            CONFIG.ID_WIDTH $FB_MID \
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
    # The leg wrapper ties every slave-side ID to 0 because SmartConnect drives
    # none. If a Vivado release starts driving one, that assumption is stale.
    foreach s $FB_SLAVES {
        set sname [lindex $s 0]
        foreach key {ID_WIDTH ARUSER_WIDTH AWUSER_WIDTH} {
            set w [get_property CONFIG.$key [get_bd_intf_ports /$sname]]
            if {$w != 0} {
                puts stderr "ERROR: fb_sc $sname $key = $w; the leg wrapper assumes 0 (regenerate it to match)"
                exit 1
            }
        }
    }
    save_bd_design
    set bd_file [get_files fb_sc.bd]
    set_property synth_checkpoint_mode None $bd_file
    generate_target all $bd_file
    make_wrapper -files $bd_file -top -import
}
