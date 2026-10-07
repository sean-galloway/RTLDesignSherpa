# Filelist for kestrel_decode
# Location: projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/fub/kestrel_decode.f
#
# Purely combinational control truth table -- no reset_defs dependency.

# Package (opcode/funct localparams, halt causes)
-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f

# Decode module
$KESTREL_ROOT/rtl/fub/kestrel_decode.sv
