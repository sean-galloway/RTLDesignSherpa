# Filelist for reset_defs.svh
# Location: rtl/amba/filelists/reset_defs.f
#
# Macro header only -- no modules, no closure. Carried as a filelist so that
# consumers under projects/components/ never name an rtl/amba path directly
# and the "no hand-listed rtl sources" rule stays mechanically checkable.

+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/rtl/amba/includes/reset_defs.svh
