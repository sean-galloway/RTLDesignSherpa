# SPDX-License-Identifier: MIT
# Filelist for pic_8259_cascade_tb_top -- the DV wrapper that puts two
# apb4_pic_8259 in the PC/AT cascade arrangement (RLB/pic_8259 TASK-001).
#
# Pulls the block by its OWN filelist rather than hand-listing sources; both
# PICs are the same module, so one -f covers the whole closure.
-f $RETRO_ROOT/rtl/pic_8259/filelists/apb4_pic_8259.f

$RETRO_ROOT/dv/tb/pic_8259_cascade_tb_top.sv
