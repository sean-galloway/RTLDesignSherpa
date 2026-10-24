# Filelist for rapids_byte_top — FPGA synthesis / lint target for Nexys A7-100T.
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_top.f
#
# Wraps rapids_byte_harness with board I/O (clock, reset button, UART, LEDs,
# 7-seg) plus the host front-end (UART->AXIL bridge, AXIL slave decode/router,
# apb4_master for the DUT-register path). Sources shared with the harness or the
# converter filelists resolve to the same absolute path and are de-duplicated.

# ---- The characterization harness (+ DUT + pattern/mem blocks + incdirs) ----
-f $REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness.f

-f $REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_top_common.f
