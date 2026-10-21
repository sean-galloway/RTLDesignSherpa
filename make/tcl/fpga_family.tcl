#==============================================================================
# fpga_family.tcl -- the DSP/primitive family of a Vivado part, for RTL that
# selects a family-specific primitive (e.g. kestrel_alu_dsp's DSP48E1).
#
#   source "$rds_root/make/tcl/fpga_family.tcl"
#   set fam [fpga_family $part_name]     ;# 7SERIES | ULTRASCALE |
#                                        ;# ULTRASCALEPLUS | VERSAL
#
# Derived from the part's ARCHITECTURE property, so a build never has to
# state its family by hand.  Unknown architectures are an error.
#==============================================================================

proc fpga_family {part} {
    set arch [get_property ARCHITECTURE [get_parts $part]]
    switch -glob -- $arch {
        artix7 - kintex7 - virtex7 - spartan7 - zynq - qartix7 - qkintex7 -
        qvirtex7 - qzynq - aartix7 - azynq            { return "7SERIES" }
        kintexu - virtexu                             { return "ULTRASCALE" }
        kintexuplus - virtexuplus - virtexuplusHBM -
        virtexuplus58g - zynquplus - zynquplusRFSOC -
        artixuplus                                    { return "ULTRASCALEPLUS" }
        versal*                                       { return "VERSAL" }
        default {
            error "fpga_family: unknown ARCHITECTURE '$arch' for part $part"
        }
    }
}
