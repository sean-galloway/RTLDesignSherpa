open_checkpoint [file join [pwd] reports_retry3a granite_char_top_retry3a_routed.dcp]
set fp [open [file join [pwd] reports_fp1 cell_types.txt] w]
foreach hier {u_harness/u_dut/u_ctrl/u_core/u_entry_store u_harness/u_dut/u_ctrl/u_core/u_sched_plane u_harness/u_dut/u_ctrl/u_core/u_axi_plane} {
    puts $fp "\nHIER: $hier"
    set cells [get_cells -hier -filter "NAME =~ ${hier}* && PRIMITIVE_LEVEL == LEAF"]
    set types [lsort -unique [get_property REF_NAME $cells]]
    puts $fp "  leaf cells: [llength $cells]"
    puts $fp "  REF_NAMEs: $types"
    set sites [lsort -unique [get_property SITE_TYPE [get_sites -of_objects $cells]]]
    puts $fp "  SITE_TYPEs: $sites"
}
close $fp
close_design
