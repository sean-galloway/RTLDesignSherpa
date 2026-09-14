# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Filelist: ioapic_msi_emit.f
# Purpose: MSI delivery -- delivery message to posted bus write (RLB-008).
#
# Usage: Source this file in simulation/synthesis tools
#
# This is a COMPANION to apb4_ioapic, not part of its closure: an integrator
# instantiates it on the far side of the delivery channel, alongside an
# apb4_master_stub. apb4_ioapic.f therefore does not reference it, and nothing
# here is duplicated from that filelist.
#
# The emitter itself has no submodules -- it is the format mapping and the
# command packing. The master that carries the write is pulled by its own
# sub-block filelist rather than hand-listed.

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# The APB4 master that turns cmd/rsp into a bus write.
-f $REPO_ROOT/rtl/amba/filelists/apb4_master_stub.f

# The emitter.
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_msi_emit.sv
