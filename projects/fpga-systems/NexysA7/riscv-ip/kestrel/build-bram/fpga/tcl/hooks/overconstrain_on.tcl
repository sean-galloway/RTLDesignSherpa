# IMPL=explore: tighten the clock before placement so the placer and the
# post-place phys_opt aim past the real period (the over-constraint idea is
# from the BRISKI barrel core's flow).  overconstrain_off.tcl removes it
# before routing, so sign-off timing is against the true constraint.
set_clock_uncertainty -setup 0.300 [get_clocks -of_objects [get_pins -hier -filter {NAME =~ *u_mmcm/CLKOUT0}]]
