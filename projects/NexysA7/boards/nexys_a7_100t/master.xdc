##==============================================================================
## Nexys A7-100T Master Constraints File
##==============================================================================
## Board: Digilent Nexys A7-100T (XC7A100T-1CSG324C)
## Purpose: Complete pin assignment template
## Usage: Copy relevant sections to your project's constraints file
##==============================================================================

##==============================================================================
## Clock Signals
##==============================================================================

## Primary Clock (100 MHz)
#set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
#create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports CLK100MHZ]

##==============================================================================
## Push Buttons (Active-High)
##==============================================================================

#set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports btnC]  # Center
#set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports btnU]  # Up
#set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports btnL]  # Left
#set_property -dict {PACKAGE_PIN R10 IOSTANDARD LVCMOS33} [get_ports btnR]  # Right
#set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports btnD]  # Down

## CPU Reset Button (Active-Low)
#set_property -dict {PACKAGE_PIN N17 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]

##==============================================================================
## Slide Switches (16)
##==============================================================================

#set_property -dict {PACKAGE_PIN J15 IOSTANDARD LVCMOS33} [get_ports {sw[0]}]
#set_property -dict {PACKAGE_PIN L16 IOSTANDARD LVCMOS33} [get_ports {sw[1]}]
#set_property -dict {PACKAGE_PIN M13 IOSTANDARD LVCMOS33} [get_ports {sw[2]}]
#set_property -dict {PACKAGE_PIN R15 IOSTANDARD LVCMOS33} [get_ports {sw[3]}]
#set_property -dict {PACKAGE_PIN R17 IOSTANDARD LVCMOS33} [get_ports {sw[4]}]
#set_property -dict {PACKAGE_PIN T18 IOSTANDARD LVCMOS33} [get_ports {sw[5]}]
#set_property -dict {PACKAGE_PIN U18 IOSTANDARD LVCMOS33} [get_ports {sw[6]}]
#set_property -dict {PACKAGE_PIN R13 IOSTANDARD LVCMOS33} [get_ports {sw[7]}]
#set_property -dict {PACKAGE_PIN T8  IOSTANDARD LVCMOS18} [get_ports {sw[8]}]
#set_property -dict {PACKAGE_PIN U8  IOSTANDARD LVCMOS18} [get_ports {sw[9]}]
#set_property -dict {PACKAGE_PIN R16 IOSTANDARD LVCMOS33} [get_ports {sw[10]}]
#set_property -dict {PACKAGE_PIN T13 IOSTANDARD LVCMOS33} [get_ports {sw[11]}]
#set_property -dict {PACKAGE_PIN H6  IOSTANDARD LVCMOS33} [get_ports {sw[12]}]
#set_property -dict {PACKAGE_PIN U12 IOSTANDARD LVCMOS33} [get_ports {sw[13]}]
#set_property -dict {PACKAGE_PIN U11 IOSTANDARD LVCMOS33} [get_ports {sw[14]}]
#set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports {sw[15]}]

##==============================================================================
## LEDs (16)
##==============================================================================

#set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
#set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
#set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
#set_property -dict {PACKAGE_PIN N14 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
#set_property -dict {PACKAGE_PIN R18 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
#set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
#set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
#set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
#set_property -dict {PACKAGE_PIN V16 IOSTANDARD LVCMOS33} [get_ports {led[8]}]
#set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS33} [get_ports {led[9]}]
#set_property -dict {PACKAGE_PIN U14 IOSTANDARD LVCMOS33} [get_ports {led[10]}]
#set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports {led[11]}]
#set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS33} [get_ports {led[12]}]
#set_property -dict {PACKAGE_PIN V14 IOSTANDARD LVCMOS33} [get_ports {led[13]}]
#set_property -dict {PACKAGE_PIN V12 IOSTANDARD LVCMOS33} [get_ports {led[14]}]
#set_property -dict {PACKAGE_PIN V11 IOSTANDARD LVCMOS33} [get_ports {led[15]}]

##==============================================================================
## RGB LEDs (2)
##==============================================================================

## RGB LED 16
#set_property -dict {PACKAGE_PIN R12 IOSTANDARD LVCMOS33} [get_ports led16_r]
#set_property -dict {PACKAGE_PIN M16 IOSTANDARD LVCMOS33} [get_ports led16_g]
#set_property -dict {PACKAGE_PIN N15 IOSTANDARD LVCMOS33} [get_ports led16_b]

## RGB LED 17
#set_property -dict {PACKAGE_PIN G14 IOSTANDARD LVCMOS33} [get_ports led17_r]
#set_property -dict {PACKAGE_PIN R11 IOSTANDARD LVCMOS33} [get_ports led17_g]
#set_property -dict {PACKAGE_PIN N16 IOSTANDARD LVCMOS33} [get_ports led17_b]

##==============================================================================
## 7-Segment Display (8 Digits, Common Anode)
##==============================================================================

## Segment Cathodes (Active-Low)
#set_property -dict {PACKAGE_PIN L3 IOSTANDARD LVCMOS33} [get_ports {seg[0]}]  # CA
#set_property -dict {PACKAGE_PIN N1 IOSTANDARD LVCMOS33} [get_ports {seg[1]}]  # CB
#set_property -dict {PACKAGE_PIN L5 IOSTANDARD LVCMOS33} [get_ports {seg[2]}]  # CC
#set_property -dict {PACKAGE_PIN L4 IOSTANDARD LVCMOS33} [get_ports {seg[3]}]  # CD
#set_property -dict {PACKAGE_PIN K3 IOSTANDARD LVCMOS33} [get_ports {seg[4]}]  # CE
#set_property -dict {PACKAGE_PIN M2 IOSTANDARD LVCMOS33} [get_ports {seg[5]}]  # CF
#set_property -dict {PACKAGE_PIN L6 IOSTANDARD LVCMOS33} [get_ports {seg[6]}]  # CG
#set_property -dict {PACKAGE_PIN M4 IOSTANDARD LVCMOS33} [get_ports dp]        # DP

## Digit Anodes (Active-Low)
#set_property -dict {PACKAGE_PIN N6 IOSTANDARD LVCMOS33} [get_ports {an[7]}]  # AN7 (leftmost)
#set_property -dict {PACKAGE_PIN M6 IOSTANDARD LVCMOS33} [get_ports {an[6]}]  # AN6
#set_property -dict {PACKAGE_PIN M3 IOSTANDARD LVCMOS33} [get_ports {an[5]}]  # AN5
#set_property -dict {PACKAGE_PIN N5 IOSTANDARD LVCMOS33} [get_ports {an[4]}]  # AN4
#set_property -dict {PACKAGE_PIN N2 IOSTANDARD LVCMOS33} [get_ports {an[3]}]  # AN3
#set_property -dict {PACKAGE_PIN N4 IOSTANDARD LVCMOS33} [get_ports {an[2]}]  # AN2
#set_property -dict {PACKAGE_PIN L1 IOSTANDARD LVCMOS33} [get_ports {an[1]}]  # AN1
#set_property -dict {PACKAGE_PIN M4 IOSTANDARD LVCMOS33} [get_ports {an[0]}]  # AN0 (rightmost)

##==============================================================================
## VGA Connector (12-bit Color)
##==============================================================================

## Red (4-bit)
#set_property -dict {PACKAGE_PIN A3 IOSTANDARD LVCMOS33} [get_ports {vga_r[0]}]
#set_property -dict {PACKAGE_PIN B4 IOSTANDARD LVCMOS33} [get_ports {vga_r[1]}]
#set_property -dict {PACKAGE_PIN C5 IOSTANDARD LVCMOS33} [get_ports {vga_r[2]}]
#set_property -dict {PACKAGE_PIN A4 IOSTANDARD LVCMOS33} [get_ports {vga_r[3]}]

## Green (4-bit)
#set_property -dict {PACKAGE_PIN C6 IOSTANDARD LVCMOS33} [get_ports {vga_g[0]}]
#set_property -dict {PACKAGE_PIN A5 IOSTANDARD LVCMOS33} [get_ports {vga_g[1]}]
#set_property -dict {PACKAGE_PIN B6 IOSTANDARD LVCMOS33} [get_ports {vga_g[2]}]
#set_property -dict {PACKAGE_PIN A6 IOSTANDARD LVCMOS33} [get_ports {vga_g[3]}]

## Blue (4-bit)
#set_property -dict {PACKAGE_PIN B7 IOSTANDARD LVCMOS33} [get_ports {vga_b[0]}]
#set_property -dict {PACKAGE_PIN C7 IOSTANDARD LVCMOS33} [get_ports {vga_b[1]}]
#set_property -dict {PACKAGE_PIN D7 IOSTANDARD LVCMOS33} [get_ports {vga_b[2]}]
#set_property -dict {PACKAGE_PIN D8 IOSTANDARD LVCMOS33} [get_ports {vga_b[3]}]

## Sync
#set_property -dict {PACKAGE_PIN B11 IOSTANDARD LVCMOS33} [get_ports vga_hs]  # Horizontal Sync
#set_property -dict {PACKAGE_PIN B12 IOSTANDARD LVCMOS33} [get_ports vga_vs]  # Vertical Sync

##==============================================================================
## USB-UART (FTDI FT2232HQ)
##==============================================================================

#set_property -dict {PACKAGE_PIN C4 IOSTANDARD LVCMOS33} [get_ports uart_txd_in]   # RXD (from PC)
#set_property -dict {PACKAGE_PIN D4 IOSTANDARD LVCMOS33} [get_ports uart_rxd_out]  # TXD (to PC)

##==============================================================================
## USB HID (PS/2 Mouse/Keyboard)
##==============================================================================

#set_property -dict {PACKAGE_PIN F4 IOSTANDARD LVCMOS33} [get_ports ps2_clk]
#set_property -dict {PACKAGE_PIN B2 IOSTANDARD LVCMOS33} [get_ports ps2_data]

##==============================================================================
## Ethernet (10/100 RMII)
##==============================================================================

#set_property -dict {PACKAGE_PIN D17 IOSTANDARD LVCMOS33} [get_ports eth_ref_clk]  # 50 MHz
#set_property -dict {PACKAGE_PIN C16 IOSTANDARD LVCMOS33} [get_ports eth_rstn]
#set_property -dict {PACKAGE_PIN F16 IOSTANDARD LVCMOS33} [get_ports eth_crsdv]
#set_property -dict {PACKAGE_PIN G16 IOSTANDARD LVCMOS33} [get_ports {eth_rxd[0]}]
#set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS33} [get_ports {eth_rxd[1]}]
#set_property -dict {PACKAGE_PIN G14 IOSTANDARD LVCMOS33} [get_ports eth_rxerr]
#set_property -dict {PACKAGE_PIN H16 IOSTANDARD LVCMOS33} [get_ports {eth_txd[0]}]
#set_property -dict {PACKAGE_PIN H15 IOSTANDARD LVCMOS33} [get_ports {eth_txd[1]}]
#set_property -dict {PACKAGE_PIN H14 IOSTANDARD LVCMOS33} [get_ports eth_txen]
#set_property -dict {PACKAGE_PIN C15 IOSTANDARD LVCMOS33} [get_ports eth_mdc]
#set_property -dict {PACKAGE_PIN K13 IOSTANDARD LVCMOS33} [get_ports eth_mdio]
#set_property -dict {PACKAGE_PIN G18 IOSTANDARD LVCMOS33} [get_ports eth_intn]

## Ethernet Clock Constraint
#create_clock -period 20.000 -name eth_ref_clk [get_ports eth_ref_clk]

##==============================================================================
## Quad SPI Flash (128 Mb)
##==============================================================================

#set_property -dict {PACKAGE_PIN L13 IOSTANDARD LVCMOS33} [get_ports qspi_cs]
#set_property -dict {PACKAGE_PIN K17 IOSTANDARD LVCMOS33} [get_ports {qspi_dq[0]}]  # MOSI
#set_property -dict {PACKAGE_PIN K18 IOSTANDARD LVCMOS33} [get_ports {qspi_dq[1]}]  # MISO
#set_property -dict {PACKAGE_PIN L14 IOSTANDARD LVCMOS33} [get_ports {qspi_dq[2]}]  # WP
#set_property -dict {PACKAGE_PIN M14 IOSTANDARD LVCMOS33} [get_ports {qspi_dq[3]}]  # HOLD

##==============================================================================
## Audio Out (PWM, 3.5mm Jack)
##==============================================================================

#set_property -dict {PACKAGE_PIN A11 IOSTANDARD LVCMOS33} [get_ports aud_pwm]
#set_property -dict {PACKAGE_PIN D12 IOSTANDARD LVCMOS33} [get_ports aud_sd]  # Shutdown (active-low)

##==============================================================================
## PMOD Headers (4x 12-pin)
##==============================================================================

## PMOD Header JA (Top Row: 1-6, Bottom Row: 7-12)
#set_property -dict {PACKAGE_PIN C17 IOSTANDARD LVCMOS33} [get_ports {ja[0]}]   # JA1
#set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS33} [get_ports {ja[1]}]   # JA2
#set_property -dict {PACKAGE_PIN E18 IOSTANDARD LVCMOS33} [get_ports {ja[2]}]   # JA3
#set_property -dict {PACKAGE_PIN G17 IOSTANDARD LVCMOS33} [get_ports {ja[3]}]   # JA4
#set_property -dict {PACKAGE_PIN D17 IOSTANDARD LVCMOS33} [get_ports {ja[4]}]   # JA7
#set_property -dict {PACKAGE_PIN E17 IOSTANDARD LVCMOS33} [get_ports {ja[5]}]   # JA8
#set_property -dict {PACKAGE_PIN F18 IOSTANDARD LVCMOS33} [get_ports {ja[6]}]   # JA9
#set_property -dict {PACKAGE_PIN G18 IOSTANDARD LVCMOS33} [get_ports {ja[7]}]   # JA10

## PMOD Header JB
#set_property -dict {PACKAGE_PIN D14 IOSTANDARD LVCMOS33} [get_ports {jb[0]}]   # JB1
#set_property -dict {PACKAGE_PIN F16 IOSTANDARD LVCMOS33} [get_ports {jb[1]}]   # JB2
#set_property -dict {PACKAGE_PIN G16 IOSTANDARD LVCMOS33} [get_ports {jb[2]}]   # JB3
#set_property -dict {PACKAGE_PIN H14 IOSTANDARD LVCMOS33} [get_ports {jb[3]}]   # JB4
#set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports {jb[4]}]   # JB7
#set_property -dict {PACKAGE_PIN F13 IOSTANDARD LVCMOS33} [get_ports {jb[5]}]   # JB8
#set_property -dict {PACKAGE_PIN G13 IOSTANDARD LVCMOS33} [get_ports {jb[6]}]   # JB9
#set_property -dict {PACKAGE_PIN H16 IOSTANDARD LVCMOS33} [get_ports {jb[7]}]   # JB10

## PMOD Header JC
#set_property -dict {PACKAGE_PIN K1 IOSTANDARD LVCMOS33} [get_ports {jc[0]}]    # JC1
#set_property -dict {PACKAGE_PIN F6 IOSTANDARD LVCMOS33} [get_ports {jc[1]}]    # JC2
#set_property -dict {PACKAGE_PIN J2 IOSTANDARD LVCMOS33} [get_ports {jc[2]}]    # JC3
#set_property -dict {PACKAGE_PIN G6 IOSTANDARD LVCMOS33} [get_ports {jc[3]}]    # JC4
#set_property -dict {PACKAGE_PIN E7 IOSTANDARD LVCMOS33} [get_ports {jc[4]}]    # JC7
#set_property -dict {PACKAGE_PIN J3 IOSTANDARD LVCMOS33} [get_ports {jc[5]}]    # JC8
#set_property -dict {PACKAGE_PIN J4 IOSTANDARD LVCMOS33} [get_ports {jc[6]}]    # JC9
#set_property -dict {PACKAGE_PIN E6 IOSTANDARD LVCMOS33} [get_ports {jc[7]}]    # JC10

## PMOD Header JD
#set_property -dict {PACKAGE_PIN H4 IOSTANDARD LVCMOS33} [get_ports {jd[0]}]    # JD1
#set_property -dict {PACKAGE_PIN H1 IOSTANDARD LVCMOS33} [get_ports {jd[1]}]    # JD2
#set_property -dict {PACKAGE_PIN G1 IOSTANDARD LVCMOS33} [get_ports {jd[2]}]    # JD3
#set_property -dict {PACKAGE_PIN G3 IOSTANDARD LVCMOS33} [get_ports {jd[3]}]    # JD4
#set_property -dict {PACKAGE_PIN H2 IOSTANDARD LVCMOS33} [get_ports {jd[4]}]    # JD7
#set_property -dict {PACKAGE_PIN G4 IOSTANDARD LVCMOS33} [get_ports {jd[5]}]    # JD8
#set_property -dict {PACKAGE_PIN G2 IOSTANDARD LVCMOS33} [get_ports {jd[6]}]    # JD9
#set_property -dict {PACKAGE_PIN F3 IOSTANDARD LVCMOS33} [get_ports {jd[7]}]    # JD10

##==============================================================================
## DDR2 SDRAM (128 MB)
##==============================================================================
## NOTE: DDR2 requires complex constraints - use MIG IP core

##==============================================================================
## Configuration and Bitstream Settings
##==============================================================================

#set_property CONFIG_VOLTAGE 3.3 [current_design]
#set_property CFGBVS VCCO [current_design]
#set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
#set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
#set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]

##==============================================================================
## End of Master Constraints File
##==============================================================================
