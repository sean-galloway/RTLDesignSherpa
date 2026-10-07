# SPDX-License-Identifier: MIT
# DV filelist for kestrel-rv32i: the TB tops on top of the RTL closure.
# RTL sources come in through the RTL master filelist (kestrel_all.f);
# only TBs live here.
# Own-area paths use $KESTREL_ROOT (registered in env_python,
# bin/TBClasses/shared/filelist_utils.py, and bin/filelist_registry.py).
-f $KESTREL_ROOT/rtl/filelists/kestrel_all.f
$KESTREL_ROOT/dv/tb/kestrel_tb_top.sv
$KESTREL_ROOT/dv/tb/kestrel_loader_tb_top.sv
