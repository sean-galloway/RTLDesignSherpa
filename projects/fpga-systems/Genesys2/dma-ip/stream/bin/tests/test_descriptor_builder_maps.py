# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""DescriptorBuilder's two map knobs: the STREAM harness default is unchanged,
and the fabric benchmark's map (DMA-side descriptor base, per-channel
windows) lands where the hardware decodes it."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from descriptor_builder import (DescriptorBuilder, DESC_RAM_BASE,  # noqa: E402
                                DESC_INDEX_OFFSET, MAX_DESC_PER_CH)

W_SRC_LO, W_DST_LO, W_NEXT = 0, 2, 5


def _words(writes):
    """{host_addr: value}"""
    return dict(writes)


def test_stream_default_unchanged():
    b = DescriptorBuilder()
    w = _words(b.build_chain(channel=3, num_descriptors=2, transfer_bytes=4096))
    idx = DESC_INDEX_OFFSET + 3 * MAX_DESC_PER_CH
    host0 = DESC_RAM_BASE + idx * 32
    assert w[host0 + 4 * W_SRC_LO] == 0x8000_0000          # same for every channel
    assert w[host0 + 4 * W_DST_LO] == 0x9000_0000
    assert w[host0 + 4 * W_NEXT] == DESC_RAM_BASE + (idx + 1) * 32
    assert b.kick_address(3) == DESC_RAM_BASE + idx * 32


def test_fabric_map():
    stride = 1 << 25
    b = DescriptorBuilder(src_base=0x9000_0000, dst_base=0xA000_0000,
                          desc_dma_base=0x8000_0000, channel_stride=stride)
    w = _words(b.build_chain(channel=5, num_descriptors=2, transfer_bytes=4096))
    idx = DESC_INDEX_OFFSET + 5 * MAX_DESC_PER_CH
    host0 = DESC_RAM_BASE + idx * 32                         # preload: host's view
    assert w[host0 + 4 * W_SRC_LO] == 0x9000_0000 + 5 * stride
    assert w[host0 + 4 * W_DST_LO] == 0xA000_0000 + 5 * stride
    assert w[host0 + 32 + 4 * W_SRC_LO] == 0x9000_0000 + 5 * stride + 4096
    assert w[host0 + 4 * W_NEXT] == 0x8000_0000 + (idx + 1) * 32   # DMA's view
    assert b.kick_address(5) == 0x8000_0000 + idx * 32
    # channel bits [27:25] of every buffer address name the channel
    for ch in range(8):
        cw = _words(b.build_chain(channel=ch, num_descriptors=16, transfer_bytes=1 << 20))
        srcs = [v for a, v in cw.items() if (a - DESC_RAM_BASE) % 32 == 4 * W_SRC_LO]
        assert all((s >> 25) & 7 == ch for s in srcs), ch
