# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_trans_decode.f
# Purpose: SMBus 2.0 transaction table as combinational logic (which bytes,
#          which direction, repeated START or not, how many data bytes).

+incdir+$REPO_ROOT/rtl/amba/includes

$RETRO_ROOT/rtl/smbus/smbus_trans_decode.sv
