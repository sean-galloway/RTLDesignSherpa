# Filelist for chi_hnf_port_monlite (rtl/amba/chi/chi_hnf_port_monlite.sv)
# chi_hnf_port with chi_monitor_lite tapping it. The port's filelist already
# carries gaxi_fifo_sync and reset_defs, so the monitor's dependencies are
# listed here individually rather than through chi_monitor_lite.f (which
# would declare gaxi_fifo_sync twice).
-f $REPO_ROOT/rtl/amba/filelists/chi_hnf_port.f
-f $REPO_ROOT/rtl/amba/filelists/ocelus_chi_pkg.f
-f $REPO_ROOT/rtl/common/filelists/counter_freq_invariant.f
$REPO_ROOT/rtl/amba/ocelus/chi_monitor_lite.sv
$REPO_ROOT/rtl/amba/chi/chi_hnf_port_monlite.sv
