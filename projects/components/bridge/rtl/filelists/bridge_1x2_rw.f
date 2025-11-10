# Include directories
+incdir+../../../../rtl/amba/includes

# Bridge RTL files (generated)
generated/bridge_1x2_rw/bridge_1x2_rw_pkg.sv
generated/bridge_1x2_rw/cpu_adapter.sv
generated/bridge_1x2_rw/bridge_1x2_rw.sv

# AXI4 Wrapper modules (timing isolation)
../../../../rtl/amba/axi4/axi4_slave_wr.sv
../../../../rtl/amba/axi4/axi4_slave_rd.sv

# GAXI skid buffers (used by wrappers)
../../../../rtl/amba/gaxi/gaxi_skid_buffer.sv

# AXI4 crossbar (internal)
../../../../rtl/amba/axi4/axi4_crossbar.sv