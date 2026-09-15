# ==============================================================================
# APB Crossbar (apbx-xbar) - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every crossbar variant, so that
#          `make lint-apbx-xbar` has sources to lint.
# Usage:   verilator --lint-only -f filelists/apbx_xbar_all.f
#
# The RTL here is GENERATED (bin/apbx_xbar_generator.py via bin/generate_xbars.py).
# Do not hand-edit the .sv files; regenerate. This list names the per-variant
# filelists, which already carry apbx_xbar_common.f and the AMBA/common closure.
#
# Named apbx_xbar_all.f (underscore) to match the module prefix and the
# registry area name in bin/filelists.toml; the DIRECTORY is apbx-xbar.
# ==============================================================================

+incdir+$REPO_ROOT/rtl/amba/includes

# --- Crossbar cores --------------------------------------------------------
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_1to1.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_1to4.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_2to1.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_2to4.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_2to2_mixed.f

# --- Wrappers --------------------------------------------------------------
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/wrapper/apbx_xbar_1to1_wrap.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/wrapper/apbx_xbar_1to4_wrap.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/wrapper/apbx_xbar_2to1_wrap.f
-f $REPO_ROOT/projects/components/apbx-xbar/rtl/filelists/wrapper/apbx_xbar_2to4_wrap.f
