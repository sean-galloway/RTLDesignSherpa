# ==============================================================================
# ALU-INFER - Master Filelist for Verilator Lint
# ==============================================================================
#
# Purpose: the compile closure for every module this area owns.
#          rtl/Makefile references this exact path as MASTER_FILELIST.
# Usage:   verilator --lint-only -f filelists/alu_infer_all.f
#
# `-f` includes the block's own filelist; never hand-list sources here.
# ==============================================================================

-f $REPO_ROOT/projects/components/compute-eng-ip/alu-infer/rtl/filelists/alu_infer_top.f
