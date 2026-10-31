# Aggregate FUB filelist for merlin-rv32i
# Location: projects/components/riscv-ip/merlin-rv32i/rtl/filelists/fub/merlin_fubs.f
#
# One aggregate list for every merlin functional unit block; later tasks
# append their FUB filelists here.  Pipeline register FUBs live here first.

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# merlin package (imports rv32i_pkg)
-f $MERLIN_ROOT/rtl/filelists/merlin_pkg.f

# Pipeline register FUBs
$MERLIN_ROOT/rtl/fub/merlin_if_id.sv
$MERLIN_ROOT/rtl/fub/merlin_id_ex.sv
$MERLIN_ROOT/rtl/fub/merlin_ex_mem.sv
$MERLIN_ROOT/rtl/fub/merlin_mem_wb.sv
