# Timing for the andesite skeleton build on the Genesys 2.
#
# The input clock is constrained in board_pins.xdc (create_clock on
# clk200_p at 5 ns), shared with the scoria build -- identical pins,
# identical board. Everything below is this build's own.
#
# THE MMCM OUTPUT IS NOT DECLARED HERE, DELIBERATELY. Vivado derives the
# generated 100 MHz clock from MMCME2_BASE automatically, and hand-declaring
# it alongside the automatic one is how this family produced a PHANTOM
# -23.5 ns WNS (project_ddr2_char_wsysi_invalid_genclock) -- see
# build-scoria/fpga/constraints/timing.xdc for the full account. If the
# generated clock needs a name, take it from `report_clocks` after
# synthesis and reference it -- do not create it.

# cpu_reset_n is a button. It reaches a synchroniser chain in the top.
set_false_path -from [get_ports cpu_reset_n]

# The LEDs are observed by a human at ~1.5 Hz.
set_false_path -to [get_ports {led[*]}]

# The keep-alive XOR tree (led[3]) samples DFI pins that toggle at sys
# speed; the LED false path above already covers it -- this note exists so
# nobody "fixes" the unconstrained LED path by constraining the DFI nets.
