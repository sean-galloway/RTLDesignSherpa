# Filelist for gatling_mem_bram -- per-context block-RAM banks, AXIL loader,
# run/status registers.
# Location: projects/components/riscv-ip/gatling-rv32itetrad/rtl/filelists/fub/gatling_mem_bram.f

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axil4_slave_rd.f

$GATLING_ROOT/rtl/fub/gatling_mem_bram.sv
