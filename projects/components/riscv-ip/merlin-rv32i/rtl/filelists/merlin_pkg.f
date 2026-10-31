# Filelist for merlin_pkg
# Location: projects/components/riscv-ip/merlin-rv32i/rtl/filelists/merlin_pkg.f
#
# Package only -- no modules, no closure.  Pulls in rv32i_pkg because
# merlin_pkg imports the shared ALU-op enum and halt-cause constants.

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f
$MERLIN_ROOT/rtl/includes/merlin_pkg.sv
