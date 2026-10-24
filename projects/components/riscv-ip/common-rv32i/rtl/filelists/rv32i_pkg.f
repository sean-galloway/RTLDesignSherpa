# Filelist for rv32i_pkg
# Location: projects/components/riscv-ip/common-rv32i/rtl/filelists/rv32i_pkg.f
#
# Package only -- no modules, no closure.  Every common-rv32i, kestrel and
# gatling filelist that needs the ISA vocabulary pulls this in with -f;
# consumers never name the package path directly.

$RV32I_COMMON_ROOT/rtl/includes/rv32i_pkg.sv
