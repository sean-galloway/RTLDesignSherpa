# APB Crossbar Common Dependencies File List
# Location: projects/components/apb_xbar/rtl/filelists/core/apb_xbar_common.f
# Purpose: Common dependencies for all APB crossbar variants

# Include directories for SystemVerilog header files
+incdir+$REPO_ROOT/rtl/amba/includes

# GAXI dependencies (FIFO and skid buffer)
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv

# APB slave and master modules (core crossbar building blocks)
$REPO_ROOT/rtl/amba/apb/apb_slave.sv
$REPO_ROOT/rtl/amba/apb/apb_master.sv

# Common arbiter modules
$REPO_ROOT/rtl/common/arbiter_priority_encoder.sv
$REPO_ROOT/rtl/common/arbiter_round_robin.sv
$REPO_ROOT/rtl/common/encoder.sv
