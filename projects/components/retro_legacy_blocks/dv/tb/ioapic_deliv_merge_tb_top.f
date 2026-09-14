# SPDX-License-Identifier: MIT
# Filelist for ioapic_deliv_merge_tb_top -- the DV wrapper that puts
# ioapic_deliv_merge between two real apb4_ioapic delivery channels (RLB-008).
#
# Pulls both halves by their own filelists rather than hand-listing sources:
# apb4_ioapic.f deliberately does not reference the companion (it is not part
# of the block's closure), so the wrapper is where the two meet. The merge's
# own .f carries the arbiter closure and its lint waiver.
-f $RETRO_ROOT/rtl/ioapic/filelists/apb4_ioapic.f
-f $RETRO_ROOT/rtl/ioapic/filelists/ioapic_deliv_merge.f

$RETRO_ROOT/dv/tb/ioapic_deliv_merge_tb_top.sv
