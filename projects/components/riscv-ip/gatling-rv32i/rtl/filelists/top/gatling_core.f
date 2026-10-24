# Filelist for gatling_core (top)
# Location: projects/components/riscv-ip/gatling-rv32i/rtl/filelists/top/gatling_core.f
#
# The barrel RV32I core.  Its decode, immediate generator and ALU are the
# common-rv32i blocks it shares with kestrel, pulled in through their own
# filelists (one ISA, one source); this file never hand-lists them.  The
# ISA package (rv32i_pkg) comes in with them.

# reset_defs.svh -- the core uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Boundary reset synchronizer
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Shared ISA FUBs (common-rv32i; each pulls rv32i_pkg)
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_alu.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_imm_gen.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_decode.f

# gatling FUBs
-f $GATLING_ROOT/rtl/filelists/fub/gatling_regfile.f

# Top-level core
$GATLING_ROOT/rtl/top/gatling_core.sv
