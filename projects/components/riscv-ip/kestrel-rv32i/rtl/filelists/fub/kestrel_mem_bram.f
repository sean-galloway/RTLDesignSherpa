# Filelist for kestrel_mem_bram -- the registered-read (block RAM) memory system.
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/fub/kestrel_mem_bram.f

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f

$KESTREL_ROOT/rtl/fub/kestrel_mem_bram.sv
