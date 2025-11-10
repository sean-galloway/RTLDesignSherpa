# Filelist for axi4_to_apb_shim module
# Location: projects/components/converters/rtl/filelists/axi4_to_apb_shim.f
# Purpose: AXI4 to APB bridge/shim with clock domain crossing

# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Header files with macros (MUST be compiled first)
$REPO_ROOT/rtl/amba/includes/reset_defs.svh

# Dependencies - CDC and synchronization
$REPO_ROOT/rtl/amba/shared/cdc_handshake.sv

# Dependencies - GAXI infrastructure
$REPO_ROOT/rtl/amba/gaxi/gaxi_skid_buffer.sv
$REPO_ROOT/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Dependencies - APB infrastructure
$REPO_ROOT/rtl/amba/apb/apb_master.sv
$REPO_ROOT/rtl/amba/apb/apb_master_stub.sv

# Dependencies - Common modules
$REPO_ROOT/rtl/common/counter_bin.sv
$REPO_ROOT/rtl/common/fifo_control.sv

# Dependencies - AXI address generation
$REPO_ROOT/rtl/amba/shared/axi_gen_addr.sv

# Dependencies - AXI4 to APB converter core
$CONVERTERS_ROOT/rtl/axi4_to_apb_convert.sv

# Dependencies - AXI4 slave stubs
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_wr_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_rd_stub.sv
$REPO_ROOT/rtl/amba/axi4/stubs/axi4_slave_stub.sv

# Top-level AXI4 to APB shim
$CONVERTERS_ROOT/rtl/axi4_to_apb_shim.sv
