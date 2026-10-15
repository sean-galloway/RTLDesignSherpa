# fb_endpoints: LFSR source + CRC sink on their own clock behind AXI4 CDCs,
# verdicts returned to the fabric clock as one coherent snapshot.
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_cdc_rd.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_cdc_wr.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_dma_slaves.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
$REPO_ROOT/projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_endpoints.sv
