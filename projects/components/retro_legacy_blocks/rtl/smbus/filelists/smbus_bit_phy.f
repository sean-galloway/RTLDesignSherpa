# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_bit_phy.f
# Purpose: Bit-level SMBus/I2C physical layer (SCL generation, open-drain
#          drivers, clock stretching, START/STOP/repeated-START, one-bit
#          transmit and receive, SCL-low timeout).
#
# Standalone: it instantiates nothing.

+incdir+$REPO_ROOT/rtl/amba/includes

$RETRO_ROOT/rtl/smbus/smbus_bit_phy.sv
