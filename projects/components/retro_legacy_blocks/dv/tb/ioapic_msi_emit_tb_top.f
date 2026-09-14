# SPDX-License-Identifier: MIT
# Filelist for ioapic_msi_emit_tb_top -- the DV wrapper that wires
# ioapic_msi_emit onto a real apb4_ioapic delivery channel and a real
# apb4_master_stub (RLB-008).
#
# Pulls each half by its OWN filelist rather than hand-listing sources.
# apb4_ioapic.f deliberately does not reference the companion (it is not part
# of the block's closure), so the wrapper is where the two meet.
#
# apb4_master_stub is NOT listed here: ioapic_msi_emit.f already pulls it,
# because the emitter is meaningless without a master to carry the write. The
# two filelists therefore overlap on the shared amba/common closure, which is
# why the runner passes -Wno-MODDUP -- the same arrangement the arbiter and
# merge wrappers use.
-f $RETRO_ROOT/rtl/ioapic/filelists/apb4_ioapic.f
-f $RETRO_ROOT/rtl/ioapic/filelists/ioapic_msi_emit.f

$RETRO_ROOT/dv/tb/ioapic_msi_emit_tb_top.sv
