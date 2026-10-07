# Filelist for kestrel_core (top)
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/top/kestrel_core.f
#
# The single-cycle RV32I core. Each FUB below comes in through its own
# filelist (complete-closure discipline); this file never hand-lists
# rtl/amba or rtl/common sources.

# reset_defs.svh -- the core uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Package
-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f

# FUBs
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_regfile.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_alu.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_imm_gen.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_decode.f

# Top-level core
$KESTREL_ROOT/rtl/top/kestrel_core.sv
