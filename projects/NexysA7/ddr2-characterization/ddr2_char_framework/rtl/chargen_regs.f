# Filelist for chargen_regs -- the traffic-generator PeakRDL regblock.
#
# The config surface for the sixteen per-bank pattern generators (eight write,
# eight read), sitting on its own APB slave off the harness bridge. Separate
# from harness_csr on purpose: harness_csr describes THE BOARD (build identity,
# DFI tuning, timer, trace ring, PHY window) and is hand-written because of the
# pulses and the indirect window it carries; this block describes THE WORKLOAD
# and is pure array, so it is generated.
#
# Regenerate the RTL below with bin/peakrdl_generate.py (never raw
# `peakrdl regblock` -- the wrapper emits RTL + docs + regmap in lockstep) from
# projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/chargen_regs.rdl.
# The command is in that file's header.
#
# The .vlt comes FIRST and is not optional: PeakRDL's per-field always_comb
# blocks each write a different member of one `field_combo` struct, which
# Verilator reports as MULTIDRIVEN per aggregate. Without the waiver the build
# does not merely warn -- it exceeds the warning limit and fails to compile,
# which is exactly how five stream bridge tests sat broken.

$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/chargen_regs.vlt
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/generated/chargen_regs/rtl/chargen_regs_pkg.sv
$REPO_ROOT/projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/generated/chargen_regs/rtl/chargen_regs.sv

# The cpuif is passthrough, so the APB window in front of it is the consumer's
# choice. This is the shim the char macro already instantiates for the pumice
# CSR slave, and it carries the pclk -> aclk crossing the bridge needs.
-f $REPO_ROOT/projects/components/converters/rtl/filelists/apb4_to_peakrdl.f
