# Filelist for kestrel_core (top)
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/top/kestrel_core.f
#
# The single-cycle RV32I core. Each FUB below comes in through its own
# filelist (complete-closure discipline); this file never hand-lists
# rtl/amba, rtl/common or common-rv32i sources.  Decode, the immediate
# generator and the ALU are common-rv32i's (shared with gatling,
# 2026-10-22) and come in through $RV32I_COMMON_ROOT.

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

# kestrel FUBs
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f

# Top-level core
$KESTREL_ROOT/rtl/top/kestrel_core.sv
