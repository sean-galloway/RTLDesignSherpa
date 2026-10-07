# SPDX-License-Identifier: MIT
# kestrel RTL filelist. Files are appended per-task as RTL lands (Tasks 3-8).
+incdir+$REPO_ROOT/rtl/amba/includes
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_pkg.sv
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_regfile.sv
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_alu.sv
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_imm_gen.sv
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_decode.sv
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_core.sv
# Task 11 board glue: the AXIL loader composes the amba axil4 leaf slaves
# (skid-buffered AW/W/B, AR/R) exactly as rtl/amba/shared/
# sdpram_slave_axil_axil.sv does -- each leaf's own filelist carries its
# gaxi_skid_buffer dependency.
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f
$REPO_ROOT/projects/components/riscv-ip/kestrel-rv32i/rtl/kestrel_mem_loader.sv
