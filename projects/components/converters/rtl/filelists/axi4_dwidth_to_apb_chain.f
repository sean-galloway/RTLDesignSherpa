# Filelist for axi4_dwidth_to_apb_chain FUB-level chain
# Location: projects/components/converters/rtl/filelists/axi4_dwidth_to_apb_chain.f
# Purpose: Chain wrapper: axi4_dwidth_converter_rd → axi4_to_apb_shim.
#          Exists to surface the bridge's 1x5_rd_boundary_probe hang
#          at the FUB level (same chain the bridge instantiates between
#          a wide master and a narrow APB peripheral).

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# AMBA/common dependencies come in via each component's OWN filelist; this
# file never hand-lists individual rtl/common or rtl/amba sources. A consumer
# that hand-lists a component's files has to track that component's internal
# dependencies, and it silently rots when they change (missing reporter
# sub-blocks, missing monitor_trans_cam, missing clock-gate chain). Each
# filelist below declares its own complete closure.
-f $REPO_ROOT/rtl/amba/filelists/apb4_master_stub.f
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_stub.f
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f
-f $REPO_ROOT/rtl/common/filelists/counter_bin.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f

# Both chain stages come in via the converters components' OWN filelists,
# which carry their full closures (the shim's gaxi_fifo_async CDC queues,
# the dwidth converter's axi_data_upsize/dnsize primitives). Hand-listing
# the stage sources here is how this chain missed gaxi_fifo_async.
# Stage 1: AXI4 read data width converter (wide -> narrow on R)
-f $CONVERTERS_ROOT/rtl/filelists/axi4_dwidth_converter_rd.f

# Stage 2: AXI4 -> APB shim
-f $CONVERTERS_ROOT/rtl/filelists/axi4_to_apb_shim.f

# Top: the chain wrapper
$CONVERTERS_ROOT/rtl/axi4_dwidth_to_apb_chain.sv
