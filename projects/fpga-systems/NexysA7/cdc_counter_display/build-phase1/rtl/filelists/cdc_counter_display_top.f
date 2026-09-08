# Filelist for cdc_counter_display_top -- the phase-1 button-only CDC demo.
# Location: projects/fpga-systems/NexysA7/cdc_counter_display/build-phase1/rtl/filelists/cdc_counter_display_top.f
#
# The ONE compile closure for this build: `make lint` flattens it, the Vivado
# create_project.tcl expands it, and the dv/ sim resolves its sources from it.
#
# Roots: $REPO_ROOT only. No Xilinx primitives in this top -- no stubs needed.

+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

-f $REPO_ROOT/rtl/common/filelists/clock_divider.f
-f $REPO_ROOT/rtl/common/filelists/debounce.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# This build's RTL
$REPO_ROOT/projects/fpga-systems/NexysA7/cdc_counter_display/build-phase1/rtl/cdc_counter_display_top.sv
