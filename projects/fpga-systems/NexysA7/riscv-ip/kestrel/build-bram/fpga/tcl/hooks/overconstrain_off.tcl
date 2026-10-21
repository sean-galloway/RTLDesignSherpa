# IMPL=explore: drop the placement-time over-constraint (overconstrain_on.tcl)
# so routing and the reports see the real clock.
set_clock_uncertainty -setup 0.000 [get_clocks -of_objects [get_pins -hier -filter {NAME =~ *u_mmcm/CLKOUT0}]]
