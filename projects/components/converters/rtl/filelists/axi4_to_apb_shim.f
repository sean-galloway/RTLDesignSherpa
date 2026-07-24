# Filelist for axi4_to_apb_shim module
# Location: projects/components/converters/rtl/filelists/axi4_to_apb_shim.f
# Purpose: AXI4 to APB bridge/shim with clock domain crossing

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Dependencies come in via each component's OWN filelist, never by
# hand-listing individual rtl/amba or rtl/common sources here. A consumer that
# hand-lists a component's files has to track that component's internals, and
# it silently rots when they change. This filelist previously hand-listed the
# shim's dependencies and so never learned about gaxi_fifo_async, which
# axi4_to_apb_shim started instantiating when its APB cmd/rsp CDC moved from a
# 2-phase handshake to a pair of async FIFOs -- leaving every bridge with an
# APB slave unable to elaborate.

# Reset macro header
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# CDC and synchronization
-f $REPO_ROOT/rtl/cdc/filelists/cdc_2_phase_handshake.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_4_phase_handshake.f

# GAXI infrastructure. gaxi_fifo_async backs the APB cmd/rsp CDC queues.
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f
-f $REPO_ROOT/rtl/cdc/filelists/gaxi_fifo_async.f

# APB infrastructure (apb_master_stub.f carries apb_master and its
# counter_bin / fifo_control / gaxi dependencies)
-f $REPO_ROOT/rtl/amba/filelists/apb_master_stub.f

# AXI address generation
-f $REPO_ROOT/rtl/amba/filelists/axi_gen_addr.f

# AXI4 slave stubs (axi4_slave_stub.f carries the rd/wr stubs it wraps)
-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_stub.f

# Dependencies - AXI4 to APB converter core
$CONVERTERS_ROOT/rtl/axi4_to_apb_convert.sv

# Top-level AXI4 to APB shim
$CONVERTERS_ROOT/rtl/axi4_to_apb_shim.sv
