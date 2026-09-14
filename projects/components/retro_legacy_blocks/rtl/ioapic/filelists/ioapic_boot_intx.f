# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: ioapic_boot_intx.f
# Purpose: Chipset boot-interrupt rerouting -- a masked IOAPIC pin also drives
#          its mapped legacy 8259 input (RLB-008).
#
# Usage: Source this file in simulation/synthesis tools
#
# This is a COMPANION to apb4_ioapic, not part of its closure. An integrator
# instantiates it beside the block, feeding it the same irq_in the IOAPIC sees
# plus the mask vector the IOAPIC exports. apb4_ioapic.f therefore does not
# reference it, and nothing here is duplicated from that filelist.
#
# The module has no submodules and no dependencies: it is the reroute decision
# and the map onto the legacy inputs, both combinational.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# The companion.
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_boot_intx.sv
