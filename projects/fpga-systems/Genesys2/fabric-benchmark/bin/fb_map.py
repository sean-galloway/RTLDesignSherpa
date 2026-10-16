# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The fabric benchmark's data map, for every host-side consumer.

One copy, imported by the sim TB (dv/tbclasses/fb_harness_tb.py) and the board
program (bin/fb_char.py), so the two cannot disagree about where STREAM reads,
writes and fetches descriptors. The values mirror rtl/fb_harness.sv and the
bridge_fb_data.toml windows:

  S1 desc_ram  0x8000_0000  descriptors (STREAM fetches here; the host preloads
                            them through the config bridge at 0x0002_0000)
  S2 lfsr_src  0x9000_0000  source window -- fb_endpoints' LFSR source
  S3 crc_snk   0xA000_0000  sink window   -- fb_endpoints' CRC sink
  channel N    window base + N << CH_ADDR_LSB (fb_harness CH_ADDR_LSB = 25:
               32 MB per channel, room for the largest chain: 16 x 1 MB)
"""
import os
import sys

SRC_BASE = 0x9000_0000
DST_BASE = 0xA000_0000
DESC_DMA_BASE = 0x8000_0000
CH_ADDR_LSB = 25
DATA_WIDTH = 128


def stream_host_path() -> str:
    """Put the STREAM area's host layer on sys.path (via its stream_env) and
    return the directory. The fabric benchmark drives the Genesys 2 STREAM
    characterization runner unchanged."""
    here = os.path.dirname(os.path.abspath(__file__))
    stream_bin = os.path.normpath(os.path.join(here, '..', '..', 'dma-ip', 'stream', 'bin'))
    if stream_bin not in sys.path:
        sys.path.insert(0, stream_bin)
    import stream_env  # noqa: F401  (fpga-systems/bin and the stream libraries)
    return stream_bin


def make_builder(src_base: int = SRC_BASE, dst_base: int = DST_BASE):
    """The DescriptorBuilder for this fabric's map (same in every leg). The
    bases default to W2's endpoints; fb_workloads passes DDR3 regions."""
    stream_host_path()
    from descriptor_builder import DescriptorBuilder
    return DescriptorBuilder(data_width=DATA_WIDTH, src_base=src_base, dst_base=dst_base,
                             desc_dma_base=DESC_DMA_BASE, channel_stride=1 << CH_ADDR_LSB)
