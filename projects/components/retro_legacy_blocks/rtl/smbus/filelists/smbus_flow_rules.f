# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_flow_rules.f
# Purpose: The master sequencer's combinational flow rules - byte states, ACK
#          policy, TX FIFO load/pop discipline, FIFO underrun/overrun.

+incdir+$REPO_ROOT/rtl/amba/includes

$RETRO_ROOT/rtl/smbus/smbus_flow_rules.sv
