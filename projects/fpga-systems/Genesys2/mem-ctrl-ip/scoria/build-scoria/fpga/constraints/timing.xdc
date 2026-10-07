# Clocking and timing for the scoria DDR3 build on the Genesys 2.
#
# The input clock is constrained in board_pins.xdc (create_clock on clk200_p at
# 5 ns), which is shared verbatim with the LiteDRAM build -- identical pins,
# identical board, one thing different. Everything below is this build's own.
#
# THE MMCM OUTPUTS ARE NOT DECLARED HERE, DELIBERATELY. Vivado derives
# generated clocks from MMCME2_BASE automatically, and hand-declaring them
# alongside the automatic ones is how this family produced a PHANTOM -23.5 ns
# WNS: an invalid auto-inferred generated clock on an MMCM output that also had
# a manual create_generated_clock, which cost a day of hunting before anyone
# doubted the constraint rather than the design
# (project_ddr2_char_wsysi_invalid_genclock). If an MMCM output needs a name,
# take it from `report_clocks` after synthesis and reference it -- do not
# create it.
#
# sys is 80 MHz (12.5 ns) and sys4x is 320 MHz (3.125 ns), from VCO 800 with
# CLKOUT1 /10 and CLKOUT0 /2.5. See scoria_char_top.sv for why sys4x is on the
# fractional output.

# The UART is asynchronous to everything and its bridge synchronises it.
set_false_path -from [get_ports uart_rx]
set_false_path -to   [get_ports uart_tx]

# cpu_reset_n is a button. It reaches a synchroniser chain in the top.
set_false_path -from [get_ports cpu_reset_n]

# The LEDs are observed by a human at 200 Hz.
set_false_path -to [get_ports {led[*]}]
