# Filelist for kestrel_regfile
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/fub/kestrel_regfile.f

# reset_defs.svh -- ALWAYS_FF_RST/RST_ASSERTED macros.
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Package (XLEN, ALU op and immediate-select enums, halt causes)
-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f

# Register file module
$KESTREL_ROOT/rtl/fub/kestrel_regfile.sv
