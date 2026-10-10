# ==============================================================================
# mc_common_pkg - family-shared package for the memory-controller research IPs
# ==============================================================================
#
# Purpose: compile unit for the family types (memtype_e, dram_op_e,
#          bank_state_e, page_policy_e, decoded_addr_t, op helpers).
# Usage:   -f filelists/includes/mc_common_pkg.f
#
# Extracted 2026-10-10 in the mem-ctrl-ip reorg (Phase 2, Task 1). See
# common-ip/docs/mc_common_pkg_knobs.md for the move/stay inventory.

+incdir+$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes
$REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/includes/mc_common_pkg.sv
