# Filelist for stream_config_block
# Location: projects/components/dma-ip/stream/rtl/filelists/top/stream_config_block.f
#
# Created 2026-10-19 so formal/stream/stream_config_block builds its flat from this closure
# (make/formal_flat.mk) instead of a hand-listed SRCS.

+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
$STREAM_ROOT/rtl/top/stream_config_block.sv
