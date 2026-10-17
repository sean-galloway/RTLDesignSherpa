# Filelist for the vendored SERV core (serv_rf_top and below)
# Location: vendor/filelists/serv.f
#
# Upstream RTL, see vendor/serv/PROVENANCE.md. Kept outside vendor/serv/ because
# its update procedure rsyncs with --delete. serv_debug.v is generate-gated
# (serv_top DEBUG=1) and is listed so that configuration still elaborates;
# serv_synth_wrapper.v is a separate synthesis top and is not part of the core.

$REPO_ROOT/vendor/serv/rtl/serv_rf_top.v
$REPO_ROOT/vendor/serv/rtl/serv_top.v
$REPO_ROOT/vendor/serv/rtl/serv_aligner.v
$REPO_ROOT/vendor/serv/rtl/serv_alu.v
$REPO_ROOT/vendor/serv/rtl/serv_bufreg.v
$REPO_ROOT/vendor/serv/rtl/serv_bufreg2.v
$REPO_ROOT/vendor/serv/rtl/serv_compdec.v
$REPO_ROOT/vendor/serv/rtl/serv_csr.v
$REPO_ROOT/vendor/serv/rtl/serv_ctrl.v
$REPO_ROOT/vendor/serv/rtl/serv_debug.v
$REPO_ROOT/vendor/serv/rtl/serv_decode.v
$REPO_ROOT/vendor/serv/rtl/serv_immdec.v
$REPO_ROOT/vendor/serv/rtl/serv_mem_if.v
$REPO_ROOT/vendor/serv/rtl/serv_rf_if.v
$REPO_ROOT/vendor/serv/rtl/serv_rf_ram_if.v
$REPO_ROOT/vendor/serv/rtl/serv_rf_ram.v
$REPO_ROOT/vendor/serv/rtl/serv_state.v
