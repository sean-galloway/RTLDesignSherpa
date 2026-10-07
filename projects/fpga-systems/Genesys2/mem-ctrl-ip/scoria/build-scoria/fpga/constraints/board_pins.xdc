# Genesys 2 non-DDR3 pins for the LiteDRAM board proof.
#
# Pin values from litex_boards/platforms/digilent_genesys2.py, the same file
# bin/gen_genesys2_ddr3_xdc.py reads for the 71 DDR3 pins. Kept as a separate
# file because the DDR3 half is GENERATED and must stay regenerable -- mixing
# hand-written pins into it would make the next regen clobber them.

# ---- 200 MHz LVDS board clock (AD12/AD11) ----
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports clk200_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports clk200_n]
create_clock -period 5.000 -name clk200 [get_ports clk200_p]

# ---- reset button, active LOW ----
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_reset_n]

# ---- BIOS console. The Genesys 2 UART is a SEPARATE FT232R (serial AU05X8RM),
#      not an interface of the JTAG FT2232 -- both cables must be enumerated or
#      there is no UART however good the bitstream is. ----
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports uart_tx]
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports uart_rx]

# ---- LEDs ----
set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]

# ---- bank-wide requirement for the 1.5 V SSTL DDR3 banks on this part ----
set_property INTERNAL_VREF 0.750 [get_iobanks 32]
set_property INTERNAL_VREF 0.750 [get_iobanks 33]
set_property INTERNAL_VREF 0.750 [get_iobanks 34]

# ---- cross-domain reset into the core's reset synchroniser ------------------
# INTEGRATION-LEVEL constraint, filling a gap in the standalone core's own XDC.
#
# The core instantiates its reset synchroniser as bare FDCE primitives
# (u_litedram/FDCE -> FDCE_1) clocked by the raw 200 MHz input, fed through a
# LUT from main_litedramcore_reset_storage_reg -- a SOFTWARE-WRITABLE CSR in the
# 100 MHz sys domain. That is a reset crossing clock domains into a two-flop
# synchroniser: timing it is meaningless, which is what the synchroniser is for.
#
# The core's litedram_genesys2_ddr3.xdc does NOT cover it, and this is worth
# knowing rather than assuming. That file false-paths the PRE pins of cells
# tagged ars_ff1/ars_ff2 and set_max_delay 2 across that chain -- but these
# FDCEs carry no such attribute (they are direct primitive instantiations, not
# migen's AsyncResetSynchronizer), and a PRE-pin false path does not cover a
# setup path into D in any case. Adding that file alone left WNS unchanged at
# -0.329, which is how the real mechanism was found.
#
# Deliberately NARROW. `set_clock_groups -asynchronous` between sys and clk200
# would also clear it and would be wrong: sys is derived from clk200 by the same
# PLL, so a blanket declaration would stop timing real paths between the
# controller and the DDR3 PHY domains -- hiding exactly the class of failure
# this board proof exists to expose.
#
# Constrained by DESTINATION, not by source. The first attempt at this named
# the source register (main_litedramcore_reset_storage_reg) and moved WNS from
# -0.329 to -0.286 -- it fixed that path and exposed the next one, because
# main_crg_reset is a LUT combination of several sys-domain signals and the
# write STROBE for the same CSR is one of them. Chasing sources here is
# whack-a-mole; the asynchronicity is a property of the destination.
#
# It is exactly one pin. The core's reset chain is FDCE -> FDCE_1 -> ... ->
# FDCE_7, all clocked by main_crg_clkin_signal, and only the first takes its D
# from outside that domain (verified by reading every FDCE instance in the
# generated core). So this declares the single crossing point asynchronous and
# leaves all seven downstream stages fully timed within clk200, which is right:
# a synchroniser's internal chain must still meet timing.
#
# No -quiet: if the name changes, this matches nothing, WNS goes negative again
# and the build reports TIMING NOT MET. The check is self-verifying.
set_false_path -to [get_pins u_litedram/FDCE/D]
