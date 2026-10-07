# SPDX-License-Identifier: MIT
# DV filelist for kestrel-rv32i: the TB top on top of the RTL closure.
# RTL sources come in through the RTL filelist; only the TB lives here.
# Paths are $REPO_ROOT-anchored (repo filelist contract).
-f $REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/kestrel.f
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/dv/tb/kestrel_tb_top.sv
