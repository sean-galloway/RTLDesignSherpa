# Filelist for gatling_pkg
# Location: projects/components/riscv-ip/gatling-rv32itetrad/rtl/filelists/gatling_pkg.f
#
# Package only.  gatling reuses kestrel's ISA vocabulary (alu_op_e, the halt
# causes), so kestrel_pkg comes in first.

-f $KESTREL_ROOT/rtl/filelists/kestrel_pkg.f
$GATLING_ROOT/rtl/includes/gatling_pkg.sv
