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
