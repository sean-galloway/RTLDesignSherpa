# Filelist for granite_top_geared (granite_core + CSR + formal AXI dwidth converters).
# Host AXI width decoupled from DW via axi4_dwidth_converter_wr/rd.
#
# COMPOSES granite.f rather than re-listing its closure. Two lists that must
# agree will not stay agreed; one that includes the other cannot drift.

# ---- Granite SKU plane selection (common-ip only) ----
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite.f

# ---- PeakRDL CSR regblock ----
-f $REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/top/granite_csr.f

# ---- AXI data-width converters (host <-> DW), the only thing geared adds ----
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_upsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi_data_dnsize.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_wr.f
-f $REPO_ROOT/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_rd.f

# ---- geared wrapper ----
$REPO_ROOT/projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_top_geared.sv
