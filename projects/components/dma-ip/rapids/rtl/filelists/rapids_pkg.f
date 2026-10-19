# Filelist for the rapids package header only (rapids_pkg.sv).
# Location: projects/components/dma-ip/rapids/rtl/filelists/rapids_pkg.f
# Purpose: give cross-area flows (e.g. the Genesys2 rapids-tile harness) an
# owning-area filelist to -f for the package, instead of hand-listing the
# source path (filelist_registry cross-area audit, 2026-10-19).

+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes/rapids_pkg.sv
