# ==============================================================================
# COMMON-RV32I - Master Filelist
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns: the RV32I
# ISA vocabulary (rv32i_pkg) and the three combinational blocks kestrel and
# gatling both instantiate -- decode, immediate generator, ALU.  Every
# module-declaring .sv under rtl/ is reachable from the lists below.
#
# `-f` includes each block's own filelist; never hand-list sources here.
# ==============================================================================

-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_alu.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_imm_gen.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_decode.f
