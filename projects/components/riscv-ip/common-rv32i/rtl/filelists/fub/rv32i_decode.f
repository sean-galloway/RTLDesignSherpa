# Filelist for rv32i_decode
# Location: projects/components/riscv-ip/common-rv32i/rtl/filelists/fub/rv32i_decode.f
#
# Purely combinational control truth table -- no reset_defs dependency.

# Package (opcode/funct localparams, halt causes)
-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f

# Decode module
$RV32I_COMMON_ROOT/rtl/fub/rv32i_decode.sv
