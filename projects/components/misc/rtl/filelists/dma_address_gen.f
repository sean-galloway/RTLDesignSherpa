# Filelist for dma_address_gen
# Location: projects/components/misc/rtl/filelists/dma_address_gen.f
#
# Leaf module, no dependencies.
#
# NOTE ON LAYERING: two rtl/amba/shared modules instantiate this
# (axi4_master_wr_pattern_gen, axi4_master_rd_crc_check), so a shared library
# depends on a project area. That is backwards and worth revisiting -- the
# module arguably belongs in rtl/amba/shared. Until it moves, those consumers
# -f include THIS list rather than hand-listing the path, which is what they
# used to do.

# reset_defs.svh -- this module uses `ALWAYS_FF_RST, so its macro header
# must be on the include path and compiled before it.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/projects/components/misc/rtl/dma_address_gen.sv
