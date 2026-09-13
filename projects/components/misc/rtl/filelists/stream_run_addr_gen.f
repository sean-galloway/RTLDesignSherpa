# Filelist for stream_run_addr_gen
# Location: projects/components/misc/rtl/filelists/stream_run_addr_gen.f
#
# Run-base address generator: captures a descriptor's addr-gen config on
# `start`, drives dma_address_gen, and buffers the generated base addresses
# of runs 1..N-1 in a small prefetch FIFO.
#
# Lives in misc/rtl (beside dma_address_gen, its only real dependency) rather
# than in one DMA's fub/ tree: both STREAM and RAPIDS instantiate it, and a
# project area reaching into another project area's fub/ would be a worse
# version of the layering problem already noted in dma_address_gen.f.

-f $REPO_ROOT/projects/components/misc/rtl/filelists/dma_address_gen.f
-f $REPO_ROOT/rtl/amba/filelists/gaxi_fifo_sync.f

$REPO_ROOT/projects/components/misc/rtl/stream_run_addr_gen.sv
