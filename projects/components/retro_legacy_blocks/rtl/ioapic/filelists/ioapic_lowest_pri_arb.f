# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: ioapic_lowest_pri_arb.f
# Purpose: The consumer half of LowestPriority delivery (RLB-008).
#
# Usage: Source this file in simulation/synthesis tools
#
# This is a COMPANION to apb4_ioapic, not part of its closure: an integrator
# instantiates it next to the block, on the far side of the delivery channel.
# apb4_ioapic.f therefore does not reference it, and nothing here is duplicated
# from that filelist.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# The arbiter itself. No AMBA or CDC dependencies: it is combinational
# decision logic on an already-synchronous delivery channel.
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_lowest_pri_arb.sv
