# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less validation of the named, multi-instance STREAM host API.

Drives `Stream` (host/stream_device.py) against a recording mock bridge — no RTL,
no UART — and checks that every board operation goes through named registers and
produces the exact bytes the FPGA would receive. This is the harness-methodology
"prove board-lessly with a mock bridge first" step; the same `Stream` object then
runs unchanged in cocotb sim and on silicon.
"""

import os
import sys

import pytest

_HOST = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "host")
sys.path.insert(0, os.path.abspath(_HOST))

from stream_device import Stream  # noqa: E402
import descriptor_builder as db    # noqa: E402


class RecordingBridge:
    """Mock bridge: records writes, serves reads from a byte-addressed store."""

    def __init__(self):
        self.writes = []
        self.mem = {}

    def write(self, addr, val):
        self.writes.append((addr & 0xFFFF_FFFF, val & 0xFFFF_FFFF))
        self.mem[addr & 0xFFFF_FFFF] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr & 0xFFFF_FFFF, 0)


BS = 16  # DATA_WIDTH=128 -> 16 bytes/beat


def _stream(bridge, name, regs_base, desc_ram_base):
    return Stream(bridge, name, regs_base=regs_base, desc_ram_base=desc_ram_base,
                  data_width=128)


def test_kick_is_by_named_register():
    """run() must write the descriptor address to CH0_CTRL_LOW *by name*."""
    br = RecordingBridge()
    s0 = _stream(br, "stream0", 0x0000_0000, 0x0002_0000)
    kick = s0.load_ext(0, 16 * BS,
                       rd=dict(s0=BS, s1=8 * BS, inner=4),
                       wr=dict(s0=4 * BS, s1=BS, inner=4))
    s0.run(0, kick)

    # The kick landed at the *named* CH0_CTRL_LOW register address with the
    # descriptor address as its value — not a hardcoded offset.
    ch0_low = s0.addr("CH0_CTRL_LOW")
    assert ch0_low == 0x000  # regs_base 0 + CH0_CTRL_LOW offset
    assert (ch0_low, kick & 0xFFFF_FFFF) in br.writes
    # Channel enable also went through CHANNEL_ENABLE by name.
    assert any(a == s0.addr("CHANNEL_ENABLE") for a, _ in br.writes)


def test_ext_descriptor_bytes():
    """The extended descriptor is written into this instance's desc RAM as two
    consecutive slots, with desc_type set and chunk1 at +0x20."""
    br = RecordingBridge()
    s0 = _stream(br, "stream0", 0x0000_0000, 0x0002_0000)
    s0.load_ext(0, 16 * BS,
                rd=dict(s0=BS, s1=8 * BS, inner=4),
                wr=dict(s0=4 * BS, s1=BS, inner=4))

    base = 0x0002_0000 + db.DESC_INDEX_OFFSET * 32  # channel 0, desc 0 slot
    # chunk0 word6 carries desc_type=1 (bit 16)
    assert br.mem[base + 6 * 4] & (1 << 16)
    # chunk1 sits exactly one slot (0x20) later; word2 = rd dim (inner=4)
    assert (br.mem[base + 0x20 + 2 * 4] & 0xFFFF) == 4
    # chunk1 rd_stride_1 (word1) = 8 * BS
    assert br.mem[base + 0x20 + 1 * 4] == 8 * BS


def test_multi_instance_isolation():
    """stream0 / stream1 use distinct register + desc-RAM bases; same names."""
    br = RecordingBridge()
    s0 = _stream(br, "stream0", 0x0000_0000, 0x0002_0000)
    s1 = _stream(br, "stream1", 0x0010_0000, 0x0012_0000)

    # Same register name resolves to different absolute addresses per instance.
    assert s0.addr("CH0_CTRL_LOW") == 0x0000_0000
    assert s1.addr("CH0_CTRL_LOW") == 0x0010_0000
    assert s0.addr("CHANNEL_IDLE") != s1.addr("CHANNEL_IDLE")

    # Descriptors land in each instance's own desc RAM region.
    s0.load_chain(0, 1, 8 * BS)
    s1.load_chain(0, 1, 8 * BS)
    s0_writes = [a for a, _ in br.writes if 0x0002_0000 <= a < 0x0010_0000]
    s1_writes = [a for a, _ in br.writes if a >= 0x0012_0000]
    assert s0_writes and s1_writes


def test_channel_idle_and_state_by_name():
    """Status polling reads named CHANNEL_IDLE / CH_STATEn registers."""
    br = RecordingBridge()
    s0 = _stream(br, "stream0", 0x0000_0000, 0x0002_0000)
    # Seed CHANNEL_IDLE so channel 2 reads idle.
    br.mem[s0.addr("CHANNEL_IDLE")] = 1 << 2
    assert s0.channel_idle(2)
    assert not s0.channel_idle(0)
