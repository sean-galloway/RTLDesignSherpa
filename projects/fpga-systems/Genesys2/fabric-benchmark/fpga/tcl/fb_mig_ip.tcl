#==============================================================================
# fb_mig_ip.tcl -- create the S0 MIG DDR3 core (fb_mig) in the CURRENT project
#==============================================================================
# One recipe for every project that needs the controller: the vendor-IP
# project (fpga/tcl/vendor_ip.tcl) and each board build (create_project.tcl).
# Each project creates its own copy from rtl/generated/fb_mig_prj/fb_mig.prj
# (bin/gen_mig_prj.py: the board-proven Genesys 2 pinout, DDR3-800 at 4:1 so
# ui_clk = 100 MHz = the fabric clock, AXI4 128-bit, ID = the fabric's slave
# ID), so two builds never generate into one shared IP directory.
#
#   fb_create_mig <area> <fb_dw> <fb_sid>
#
# MIG ignores a .prj it cannot parse and falls back to its defaults without
# an error, so the generated core is read back and the design point checked.
#==============================================================================
proc fb_create_mig {area fb_dw fb_sid} {
    puts "\n--- fb_mig (mig_7series) ---"
    create_ip -name mig_7series -vendor xilinx.com -library ip -version 4.2 -module_name fb_mig
    set mig_dir [get_property IP_DIR [get_ips fb_mig]]
    file copy -force "$area/rtl/generated/fb_mig_prj/fb_mig.prj" [file join $mig_dir mig_a.prj]
    set_property -dict [list CONFIG.XML_INPUT_FILE {mig_a.prj} CONFIG.RESET_BOARD_INTERFACE {Custom} \
                             CONFIG.MIG_DONT_TOUCH_PARAM {Custom} CONFIG.BOARD_MIG_PARAM {Custom}] [get_ips fb_mig]
    generate_target {instantiation_template synthesis simulation} [get_ips fb_mig]
    set gen [get_property DIRECTORY [current_project]]
    set mig_v [glob -nocomplain "$gen/*.gen/sources_1/ip/fb_mig/fb_mig/user_design/rtl/fb_mig_mig.v"]
    if {$mig_v eq ""} { puts stderr "ERROR: fb_mig_mig.v not generated"; exit 1 }
    set text [read [set fh [open [lindex $mig_v 0]]]]; close $fh
    foreach {param want} [list tCK 2500 nCK_PER_CLK 4 DQ_WIDTH 32 C_S_AXI_DATA_WIDTH $fb_dw C_S_AXI_ID_WIDTH $fb_sid] {
        if {![regexp "parameter\\s+$param\\s+=\\s+(\\d+)" $text -> got] || $got != $want} {
            puts stderr "ERROR: fb_mig $param = [expr {[info exists got] ? $got : {missing}}], expected $want"
            exit 1
        }
    }
    puts "fb_mig: design point verified (tCK 2500, 4:1, DQ 32, AXI $fb_dw b, ID $fb_sid)"
}
