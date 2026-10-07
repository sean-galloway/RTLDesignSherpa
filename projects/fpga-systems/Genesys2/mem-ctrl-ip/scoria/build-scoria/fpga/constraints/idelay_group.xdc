# IODELAY grouping for the scoria DDR3 build.
#
# WHY THIS FILE EXISTS. Vivado's DRC requires every IDELAYE2/ODELAYE2 to share
# an IODELAY_GROUP with the IDELAYCTRL that calibrates it. LiteX normally sets
# that with a platform command on the generated PHY -- but we generate the PHY
# standalone through migen's Verilog converter, and the conversion DROPS the
# attribute. Nothing in the emitted k7ddrphy.v carries IODELAY_GROUP (checked:
# zero occurrences), so without this the build fails DRC late, with a message
# about delay groups rather than about a missing attribute.
#
# One group for the whole design: there is exactly one IDELAYCTRL and one PHY.
set_property IODELAY_GROUP scoria_iodelay [get_cells -hier -filter {REF_NAME == IDELAYCTRL}]
set_property IODELAY_GROUP scoria_iodelay [get_cells -hier -filter {REF_NAME == IDELAYE2}]
set_property IODELAY_GROUP scoria_iodelay [get_cells -hier -filter {REF_NAME == ODELAYE2}]
