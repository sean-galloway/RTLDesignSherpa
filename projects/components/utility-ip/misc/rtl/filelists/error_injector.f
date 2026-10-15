# Filelist for error_injector
# Location: projects/components/utility-ip/misc/rtl/filelists/error_injector.f
#
# Unified bit/symbol error injector. Self-contained; needs only the shared
# reset_defs header from rtl/amba.

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
+incdir+$REPO_ROOT/rtl/amba/includes

$REPO_ROOT/projects/components/utility-ip/misc/rtl/error_injector.sv
