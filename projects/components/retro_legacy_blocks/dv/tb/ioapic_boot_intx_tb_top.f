# SPDX-License-Identifier: MIT
# Filelist for ioapic_boot_intx_tb_top -- the DV wrapper that wires
# ioapic_boot_intx onto a real apb4_ioapic's mask export and enable register
# (RLB-008).
#
# Pulls BOTH halves by their own filelists rather than hand-listing sources.
# apb4_ioapic.f deliberately does not reference the companion (it is not part
# of the block's closure), so the wrapper is where the two meet.
-f $RETRO_ROOT/rtl/ioapic/filelists/apb4_ioapic.f
-f $RETRO_ROOT/rtl/ioapic/filelists/ioapic_boot_intx.f

$RETRO_ROOT/dv/tb/ioapic_boot_intx_tb_top.sv
