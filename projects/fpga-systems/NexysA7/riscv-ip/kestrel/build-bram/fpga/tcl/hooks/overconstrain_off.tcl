# IMPL=explore: drop the placement-time over-constraint (overconstrain_on.tcl)
# back to the XDC's 0.2 ns spread budget, so routing and the reports see the
# real clock less the budget (constraints/kestrel_nexysa7.xdc).
set_clock_uncertainty -setup 0.200 [get_clocks -of_objects [get_pins -hier -filter {NAME =~ *u_mmcm/CLKOUT0}]]
