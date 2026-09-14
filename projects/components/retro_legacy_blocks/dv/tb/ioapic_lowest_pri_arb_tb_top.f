# SPDX-License-Identifier: MIT
# Filelist for ioapic_lowest_pri_arb_tb_top -- the DV wrapper that wires
# ioapic_lowest_pri_arb onto a real apb4_ioapic delivery channel (RLB-008).
#
# Pulls BOTH halves by their own filelists rather than hand-listing sources:
# apb4_ioapic.f deliberately does not reference the companion (it is not part
# of the block's closure), so the wrapper is where the two meet.
-f $RETRO_ROOT/rtl/ioapic/filelists/apb4_ioapic.f
-f $RETRO_ROOT/rtl/ioapic/filelists/ioapic_lowest_pri_arb.f

$RETRO_ROOT/dv/tb/ioapic_lowest_pri_arb_tb_top.sv
