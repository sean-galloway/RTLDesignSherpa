# ==============================================================================
# granite (DDR2/LPDDR2 v2 product controller) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.
# Usage:   verilator --lint-only -f filelists/granite_all.f
#
# `-f` includes each block's own filelist; never hand-list sources here.

+incdir+$REPO_ROOT/rtl/amba/includes

# --- SKU package ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/includes/granite_pkg.f

# --- CSR ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite_csr.f

# --- Macros (common-ip stack) ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_axi4_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_init_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_scheduler_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_training_plane.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_dfi_2p1_plane.f

# --- Storage-lite seam ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_xddr2_entry_store.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_head_records.f

# --- Tops ---
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite.f
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite_top_geared.f
