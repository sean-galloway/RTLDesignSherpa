# Filelist for rapids_byte_top's board I/O and host front-end, and the top itself;
# everything but the harness. Pulled by rapids_byte_top.f and rapids_byte_top_16ch.f.
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_top_common.f

# ---- Host front-end: UART <-> AXIL master (uart_rx/tx, axil4_master_wr/rd,
#      gaxi_skid_buffer) ----

# ---- AXIL-slave cmd/rsp -> APB (reuses gaxi_skid_buffer from the bridge f) ----

# ---- Board status helpers: LED bank + 7-seg (+ their deps) ----
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/hex_to_7seg.f
$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/stream/rtl/led_status_driver.sv
$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/stream/rtl/seven_seg_4digit.sv

# ---- Verilator-only Xilinx primitive stub (BUFG); guarded by `ifdef VERILATOR
#      so Vivado ignores it and uses the real unisim BUFG at synthesis ----
-f $REPO_ROOT/projects/components/utility-ip/misc/rtl/filelists/verilator_xilinx_stubs.f

# ---- Board-level top (pins + host front-end + harness instantiation) ----
$REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/rtl/rapids_byte_top.sv
