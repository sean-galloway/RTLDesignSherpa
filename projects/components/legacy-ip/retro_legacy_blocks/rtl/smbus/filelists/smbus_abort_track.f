# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: smbus_abort_track.f
# Purpose: Tracks the abort's own STOP so the sequencer cannot mistake the
#          aborted primitive's completion, or a stale timeout level, for it.

+incdir+$REPO_ROOT/rtl/amba/includes

$RETRO_ROOT/rtl/smbus/smbus_abort_track.sv
