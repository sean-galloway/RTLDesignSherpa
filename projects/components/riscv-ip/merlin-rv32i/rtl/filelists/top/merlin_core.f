# Filelist for merlin_core (top)
# Location: projects/components/riscv-ip/merlin-rv32i/rtl/filelists/top/merlin_core.f
#
# The 5-stage pipelined RV32I core.  Each FUB comes in through its own
# filelist (complete-closure discipline); this file never hand-lists
# rtl/amba, rtl/common or common-rv32i sources.  Decode, the immediate
# generator and the ALU are common-rv32i's (shared with kestrel/gatling)
# and come in through $RV32I_COMMON_ROOT.

# reset_defs.svh -- the core uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Boundary reset synchronizer (top input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Package (rv32i_pkg, common-rv32i)
-f $RV32I_COMMON_ROOT/rtl/filelists/rv32i_pkg.f

# Shared ISA FUBs (common-rv32i)
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_alu.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_imm_gen.f
-f $RV32I_COMMON_ROOT/rtl/filelists/fub/rv32i_decode.f

# kestrel register file (used verbatim in merlin v1)
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f

# Merlin package and pipeline FUBs (pipeline registers + hazard unit)
-f $MERLIN_ROOT/rtl/filelists/fub/merlin_fubs.f

# Top-level core
$MERLIN_ROOT/rtl/top/merlin_core.sv
