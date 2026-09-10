# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_core.f
# Purpose: SMBus master transaction sequencer and everything it instantiates.
#          The sequencer owns the transaction (byte order, R/W bits, the
#          repeated START, ACK/NAK policy, PEC scope); the bit PHY below owns
#          every SCL and SDA movement.

+incdir+$REPO_ROOT/rtl/amba/includes

# Bit-level physical layer: every SCL and SDA movement
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_bit_phy.f

# The transaction table, as logic
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_trans_decode.f

# What happens next: the combinational flow rules
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_flow_rules.f

# Abort bookkeeping: when the abort's own STOP has finished
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_abort_track.f

# Byte buffers and their reset policy
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_byte_fifos.f

# Sticky interrupt status
-f $RETRO_ROOT/rtl/smbus/filelists/smbus_int_status.f

$RETRO_ROOT/rtl/smbus/smbus_pec.sv
$RETRO_ROOT/rtl/smbus/smbus_core.sv
