# Filelist for gatling_xcell -- the Xcell unit (custom-0 POP/PUSH/CFG/ECTX/
# FLUSH/KICK/WAIT) behind gatling_core's xc_* port.
# Location: projects/components/riscv-ip/gatling-rv32i/rtl/filelists/fub/gatling_xcell.f

# reset_defs.svh -- the unit uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$GATLING_ROOT/rtl/fub/gatling_xcell.sv
