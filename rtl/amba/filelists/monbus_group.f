# Canonical filelist for the monbus_<p1>_<p2>_group family CORE.
# Location: rtl/amba/filelists/monbus_group.f
#
# Every consumer of the monbus group (stream, rapids, bridge-generated *_mon
# bridges, the stream_char framework, the axi4_intf_{master,slave}_observer, and the val/amba
# tests) MUST -f this file rather than listing these sources inline, so a
# shared dependency (e.g. the div-by-3 helper) is added in ONE place.
#
# SELF-CONTAINED: this declares its own complete compile closure. A consumer
# -f includes it and provides nothing on its behalf.
#
# It used to require the including filelist to supply the leaf deps
# (counter_bin, fifo_control, gaxi_fifo_sync, gaxi_skid_buffer) BEFORE the -f.
# That contract was honoured inconsistently -- the four amba wrappers listed
# gaxi_fifo_sync, stream's monbus_axil_group.f listed nothing -- and it is
# unverifiable: linting this file alone reported "Cannot find file containing
# module: 'gaxi_fifo_sync'", which reads as a broken filelist whether or not
# some consumer happens to cover it. A block that only works when someone else
# remembers something is not a closure.
#
# The consumer still adds, AFTER the -f, the specific wrapper(s) it
# instantiates:
#   monbus_axil_axil_group.sv / monbus_axil_axi4_group.sv /
#   monbus_axi4_axil_group.sv / monbus_axi4_axi4_group.sv

# Leaf dependencies the core instantiates directly. gaxi_fifo_sync.f and
# gaxi_skid_buffer.f carry counter_bin and fifo_control themselves, so those
# do not need listing here as well.
#
# Both of those children -f counter_bin.f, so linting THIS file directly with
# raw verilator reports one MODDUP for counter_bin. That is inherent to a
# self-contained closure in a format with no include guards, not a defect
# here: the loader used by the cocotb tests deduplicates, `make -C rtl/amba
# lint` passes, and the FPGA flows already pass -Wno-MODDUP for the same
# reason. Add -Wno-MODDUP if you lint this filelist standalone.
#
# (gaxi_skid_buffer.f pulls counter_bin.f without instantiating counter_bin.
# Left for the AMBA audit -- ~45 filelists -f include it.)
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_skid_buffer.f

# Whole-record rounding helper. math_mod_3_compress.f already -f includes
# math_adder_carry_save_nbit.f, so listing the adder here as well only
# produces a MODDUP.
-f $REPO_ROOT/rtl/math/filelists/math_mod_3_compress.f

# Compressor (optional; selected by USE_COMPRESSION=1 + cfg_compress_en).
$REPO_ROOT/rtl/amba/monitor/monbus_cam.sv
# Pipelined CAM -- the compressor's only CAM path (always pipelined).
$REPO_ROOT/rtl/amba/monitor/monbus_cam_pipe.sv
$REPO_ROOT/rtl/amba/includes/monitor_common_pkg.sv
$REPO_ROOT/rtl/amba/monitor/monbus_compressor.sv
# Half-beat packer (optional; selected by HALF_BEAT_EN=1, two 30-bit slots/beat).
$REPO_ROOT/rtl/amba/monitor/monbus_halfbeat_packer.sv

# Protocol-agnostic core.
$REPO_ROOT/rtl/amba/monitor/monbus_group_core.sv
