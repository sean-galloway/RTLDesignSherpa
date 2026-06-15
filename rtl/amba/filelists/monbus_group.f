# Canonical filelist for the monbus_<p1>_<p2>_group family CORE.
# Location: rtl/amba/filelists/monbus_group.f
#
# Every consumer of the monbus group (stream, rapids, bridge-generated *_mon
# bridges, the stream_char framework, the axi4_dma_observer, and the val/amba
# tests) MUST -f this file rather than listing these sources inline, so a
# shared dependency (e.g. the div-by-3 helper) is added in ONE place.
#
# This lists only the protocol-AGNOSTIC core + its private helpers. The
# including filelist must still provide, BEFORE the -f:
#   +incdir+$REPO_ROOT/rtl/amba/includes      (reset_defs.svh / fifo_defs.svh)
#   the monitor_*_pkg.sv packages
#   the shared leaf deps it also uses elsewhere (counter_bin, fifo_control,
#   gaxi_fifo_sync, gaxi_skid_buffer, the axil4_/axi4_ slave_rd + master_wr
#   leaves)
# and AFTER the -f, the specific wrapper(s) it instantiates:
#   monbus_axil_axil_group.sv / monbus_axil_axi4_group.sv /
#   monbus_axi4_axil_group.sv / monbus_axi4_axi4_group.sv

# Whole-record rounding helper: compressor-style mod-3 + its 3:2 compressor.
$REPO_ROOT/rtl/common/math_adder_carry_save_nbit.sv
$REPO_ROOT/rtl/common/mod_3_compress.sv

# Compressor (optional; selected by USE_COMPRESSION=1 + cfg_compress_en).
$REPO_ROOT/rtl/amba/shared/monbus_cam.sv
$REPO_ROOT/rtl/amba/shared/monbus_compressor.sv
# Half-beat packer (optional; selected by HALF_BEAT_EN=1, two 30-bit slots/beat).
$REPO_ROOT/rtl/amba/shared/monbus_halfbeat_packer.sv

# Protocol-agnostic core.
$REPO_ROOT/rtl/amba/shared/monbus_group_core.sv
