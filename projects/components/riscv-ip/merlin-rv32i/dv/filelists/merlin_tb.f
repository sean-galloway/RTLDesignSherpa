# SPDX-License-Identifier: MIT
# DV filelist for merlin-rv32i: the TB tops on top of the RTL closure.
# RTL sources come in through the RTL master filelist (merlin_all.f);
# only TBs live here.

-f $MERLIN_ROOT/rtl/filelists/merlin_all.f
$MERLIN_ROOT/dv/tb/merlin_pipe_regs_tb_top.sv
