# Filelist for the vendored PULP axi_xbar and the common_cells it uses
# Location: vendor/filelists/pulp_axi_xbar.f
#
# Upstream RTL, see vendor/pulp-axi/PROVENANCE.md and
# vendor/pulp-common_cells/PROVENANCE.md. Packages first. Consumer:
# fabric-benchmark leg C2 (rtl/filelists/fb_data_fabric_pulp.f).

+incdir+$REPO_ROOT/vendor/pulp-common_cells/include
+incdir+$REPO_ROOT/vendor/pulp-axi/include
$REPO_ROOT/vendor/pulp-common_cells/src/cf_math_pkg.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_pkg.sv
$REPO_ROOT/vendor/pulp-common_cells/src/addr_decode_dync.sv
$REPO_ROOT/vendor/pulp-common_cells/src/addr_decode.sv
$REPO_ROOT/vendor/pulp-common_cells/src/counter.sv
$REPO_ROOT/vendor/pulp-common_cells/src/delta_counter.sv
$REPO_ROOT/vendor/pulp-common_cells/src/fifo_v3.sv
$REPO_ROOT/vendor/pulp-common_cells/src/lzc.sv
$REPO_ROOT/vendor/pulp-common_cells/src/rr_arb_tree.sv
$REPO_ROOT/vendor/pulp-common_cells/src/spill_register_flushable.sv
$REPO_ROOT/vendor/pulp-common_cells/src/spill_register.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_intf.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_atop_filter.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_cut.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_multicut.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_demux_id_counters.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_demux_simple.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_demux.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_err_slv.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_id_prepend.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_mux.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_xbar_unmuxed.sv
$REPO_ROOT/vendor/pulp-axi/src/axi_xbar.sv
