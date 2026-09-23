# ==============================================================================
# delta - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for the delta AXIS network, so `make lint-delta`
#          has sources to lint and elaborate.
# Usage:   verilator --lint-only -f filelists/delta_all.f
#
# `-f` includes each module's own filelist; never hand-list sources here.
# Verified when written: rtl/ declares exactly one module
# (delta_axis_flat_4x16) and it is reachable below. rtl_test/ holds other
# generated shapes and is deliberately NOT in this closure.
# ==============================================================================

-f $REPO_ROOT/projects/components/delta/rtl/filelists/delta_axis_flat_4x16.f
