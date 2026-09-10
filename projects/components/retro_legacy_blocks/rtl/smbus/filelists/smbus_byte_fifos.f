# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_byte_fifos.f
# Purpose: TX and RX byte buffers and their three reset sources.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/common/filelists/fifo_sync.f
$RETRO_ROOT/rtl/smbus/simple_fifo.sv
$RETRO_ROOT/rtl/smbus/smbus_byte_fifos.sv
