# ==============================================================================
# mc_all - master filelist for the mem-ctrl family common layers
# ==============================================================================
#
# Purpose: the compile closure for everything common-ip owns. Research
#          controllers (research-ip/<rock>/) -f the per-block lists (or this
#          master) as they adopt each layer in the Phase 2 extraction
#          (docs/superpowers/plans/2026-10-10-mem-ctrl-ip-phase2-common-extraction.md).
# Usage:   verilator --lint-only -f filelists/mc_all.f
#
# Written 2026-10-10 with the package (Task 1); per-layer lists join as the
# extraction lands (Tasks 2-6).

# --- Family package (must compile first) ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f
