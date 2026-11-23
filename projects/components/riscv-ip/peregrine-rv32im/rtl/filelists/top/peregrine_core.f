# Filelist for peregrine_core (top)
# Location: projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/top/peregrine_core.f
#
# Complete closure; never hand-lists rtl/amba, rtl/cdc or common-rv32i
# sources.

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f
-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_alu.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_imm_gen.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_decode.f

# kestrel register file (used verbatim, as in merlin)
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f

-f $PEREGRINE_ROOT/rtl/filelists/fub/peregrine_fubs.f

$PEREGRINE_ROOT/rtl/top/peregrine_core.sv
