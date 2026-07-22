# Filelist for fifo_defs.svh
# Location: rtl/amba/filelists/fifo_defs.f
#
# Macro header only -- no modules, no closure. Carried as a filelist so that
# consumers under projects/components/ never name an rtl/amba path directly
# and the "no hand-listed rtl sources" rule stays mechanically checkable.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/fifo_defs.svh
