# Filelist for gatling_core (top)
# Location: projects/components/riscv-ip/gatling-rv32itetrad/rtl/filelists/top/gatling_core.f
#
# The four-context barrel RV32I core.  Its decode, immediate generator and
# ALU are kestrel's, used unchanged and pulled in through kestrel's own
# filelists (one ISA, one source); this file never hand-lists them.

# reset_defs.svh -- the core uses `ALWAYS_FF_RST.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Boundary reset synchronizer
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Packages (kestrel_pkg, then gatling_pkg)
-f $GATLING_ROOT/rtl/filelists/gatling_pkg.f

# kestrel FUBs: the ISA datapath
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_alu.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_imm_gen.f
-f $KESTREL_ROOT/rtl/filelists/fub/kestrel_decode.f

# gatling FUBs
-f $GATLING_ROOT/rtl/filelists/fub/gatling_regfile.f

# Top-level core
$GATLING_ROOT/rtl/top/gatling_core.sv
