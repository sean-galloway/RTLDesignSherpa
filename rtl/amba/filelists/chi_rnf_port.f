# Filelist for chi_rnf_port
# Location: rtl/amba/filelists/chi_rnf_port.f
#
# CHI (Arm IHI 0050 Issue H). See docs/markdown/rtl-amba/chi/README.md
#
# Shared primitives are listed once here (the TX channels need the skid
# buffer, the RX channels the FIFO, both need counter_bin) rather than
# through the per-block filelists, so no module is declared twice.

# Package first: the module imports it in its header
-f $REPO_ROOT/rtl/amba/filelists/chi_pkg.f
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/common/filelists/fifo_control.f
-f $REPO_ROOT/rtl/cdc/filelists/glitch_free_n_dff_arn.f
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/chi/chi_tx_channel.sv
$REPO_ROOT/rtl/amba/chi/chi_rx_channel.sv
$REPO_ROOT/rtl/amba/chi/chi_link_tx.sv
$REPO_ROOT/rtl/amba/chi/chi_link_rx.sv
$REPO_ROOT/rtl/amba/chi/chi_rnf_port.sv
