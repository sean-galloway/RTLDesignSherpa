# Filelist for axi3_loopback module
# Location: projects/components/utility-ip/converters/rtl/filelists/axi3_loopback.f
# Purpose: AXI4 -> AXI3 -> AXI4 loopback equivalence chain (integration proof)

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Converter top filelists (read + write submodules are pulled in hierarchically)
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_axi3.f
-f $CONVERTERS_ROOT/rtl/filelists/axi3_to_axi4.f

# Loopback chain top wrapper
$CONVERTERS_ROOT/rtl/axi3_loopback.sv
