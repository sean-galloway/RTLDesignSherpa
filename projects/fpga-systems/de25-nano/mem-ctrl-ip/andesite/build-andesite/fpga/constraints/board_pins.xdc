# Genesys 2 board pins for the andesite skeleton build.
#
# Pin values are the Genesys 2's, identical to build-scoria's board_pins.xdc
# (same board, same oscillator/button/LED bank) minus everything this
# skeleton does not carry: no UART (no host scaffolding in build 1), no
# DDR3 pins (no PHY, onboard DDR3 left dark), no INTERNAL_VREF (nothing
# drives the SSTL banks).

# ---- 200 MHz LVDS board clock (AD12/AD11) ----
set_property -dict {PACKAGE_PIN AD12 IOSTANDARD LVDS} [get_ports clk200_p]
set_property -dict {PACKAGE_PIN AD11 IOSTANDARD LVDS} [get_ports clk200_n]
create_clock -period 5.000 -name clk200 [get_ports clk200_p]

# ---- reset button, active LOW ----
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_reset_n]

# ---- LEDs ----
set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
