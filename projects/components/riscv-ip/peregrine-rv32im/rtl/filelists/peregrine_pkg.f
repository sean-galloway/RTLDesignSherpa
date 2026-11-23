# Filelist for peregrine_pkg
# Location: projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/peregrine_pkg.f
#
# Package only.  Pulls in rv32i_pkg because peregrine_pkg imports the shared
# ALU-op enum and halt-cause constants.

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f
$PEREGRINE_ROOT/rtl/includes/peregrine_pkg.sv
