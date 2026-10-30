# Filelist for jet_wb_buffer
# Location: projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_wb_buffer.f
#
# Decoupled writeback (victim) buffer: VICTIM_DEPTH-deep FIFO of dirty
# victims, drained oldest-first (J5).  Needs the reset macro header and
# jet_pkg (which closes l1_pkg).

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $JET_ROOT/rtl/filelists/jet_pkg.f

$JET_ROOT/rtl/fub/jet_wb_buffer.sv
