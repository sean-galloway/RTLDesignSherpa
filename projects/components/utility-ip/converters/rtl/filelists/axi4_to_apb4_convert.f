# Filelist for axi4_to_apb4_convert
# Location: projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb4_convert.f

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Boundary reset synchronizer (block input reset is async-assert,
# synchronized internally; complete closure)
-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f

# Dependencies (complete closure; consumers should -f this file, not hand-list
# the converter source).
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f

$CONVERTERS_ROOT/rtl/axi4_to_apb4_convert.sv
