# Filelist for the vendored Forencich AXI4 crossbar (axi_crossbar and below)
# Location: vendor/filelists/verilog_axi_crossbar.f
#
# Upstream RTL, see vendor/verilog-axi/PROVENANCE.md. Kept outside
# vendor/verilog-axi/ like the other vendor filelists. Consumer: fabric-benchmark
# leg C1 (rtl/filelists/fb_data_fabric_forencich.f).

$REPO_ROOT/vendor/verilog-axi/rtl/arbiter.v
$REPO_ROOT/vendor/verilog-axi/rtl/priority_encoder.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_register_rd.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_register_wr.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_crossbar_addr.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_crossbar_rd.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_crossbar_wr.v
$REPO_ROOT/vendor/verilog-axi/rtl/axi_crossbar.v
