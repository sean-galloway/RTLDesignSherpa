# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: ioapic_deliv_merge.f
# Purpose: Multi-IOAPIC routing -- merge N delivery channels onto one (RLB-008).
#
# Usage: Source this file in simulation/synthesis tools
#
# This is a COMPANION to apb4_ioapic, not part of its closure: an integrator
# instantiates it next to two or more IOAPICs, on the far side of their
# delivery channels. apb4_ioapic.f therefore does not reference it, and nothing
# here is duplicated from that filelist.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Lint waiver for the arbiter's pre-existing UNUSEDSIGNAL (see the .vlt for
# why it is waived here rather than fixed in shared rtl/common).
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.vlt

# Round-robin arbiter, in ACK mode so a grant is held across the delivery
# handshake. Pulled by its own sub-block filelist rather than hand-listed.
-f $REPO_ROOT/rtl/common/filelists/arbiter_round_robin.f

# The merge itself.
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.sv
