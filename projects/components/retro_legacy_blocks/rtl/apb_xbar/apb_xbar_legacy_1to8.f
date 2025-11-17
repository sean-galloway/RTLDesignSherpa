# APB Crossbar Legacy 1-to-8 File List
# Location: projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_legacy_1to8.f
# Purpose: Named-port wrapper for legacy blocks crossbar

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

# Generated 1-to-8 crossbar
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_1to8.sv

# Named-port wrapper (top level)
$REPO_ROOT/projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_legacy_1to8.sv
