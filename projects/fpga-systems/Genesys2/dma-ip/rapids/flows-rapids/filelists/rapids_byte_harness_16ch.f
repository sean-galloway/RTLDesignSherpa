# Filelist for rapids_byte_harness around the 16-channel DUTs (rapids TASK-036).
# Location: projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness_16ch.f
#
# rapids_byte_harness.f with the 16-channel tops: their base picks the 16-channel
# register map through an include directory, so they cannot share a compile with
# the 8-channel tops. Selected by CHANNELS=16 (make), which also defines RAPIDS_16CH.

# ---- Include directories ----
+incdir+$REPO_ROOT/rtl/amba/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/rapids/rtl/includes
+incdir+$REPO_ROOT/projects/components/dma-ip/stream/rtl/includes

# ---- DUT: split RAPIDS beats top (+ all its deps) ----
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top_beats/rapids_beats_top.f
# byte-granular RAPIDS at 16 channels; selected by BYTE_DUT=1 and RAPIDS_16CH
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top/rapids_16ch_top.f
# rapids-g at 16 channels (rapids TASK-036); selected by RAPIDS_G and RAPIDS_16CH
-f $REPO_ROOT/projects/components/dma-ip/rapids/rtl/filelists/top_g/rapids_g_16ch_top.f

-f $REPO_ROOT/projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/filelists/rapids_byte_harness_common.f
