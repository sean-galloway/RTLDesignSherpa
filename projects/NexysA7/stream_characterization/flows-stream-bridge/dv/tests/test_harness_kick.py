# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less validation of the harness KICK_GO batch-kick fast path.

The harness exposes STREAM's i_kick_burst_mask / i_kick_burst_addr ports as CSRs
so the host can program N per-channel descriptor-address registers and then write
a single go bit that fires all N kicks back-to-back in one aclk cycle, instead of
serializing on the slow apbtodescr LOW/HIGH APB kick (a full UART round trip each).

These tests pin the CSR offset layout (which splits around the 0xC0 KICK_GO slot)
and the program-addresses-then-go-bit write ordering against a recording mock
bridge -- no RTL, no UART. The same batch_kick() then runs in cocotb sim and on
the NexysA7 (test_stream_char_ext_suite exercises it against the real harness).
"""

import os
import sys

import pytest

_HOST = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "host")
sys.path.insert(0, os.path.abspath(_HOST))

import harness_kick as hk                    # noqa: E402
import stream_ext_suite as suite             # noqa: E402
from stream_device import Stream             # noqa: E402


class RecordingBridge:
    """Mock bridge: records writes in order, serves reads from a byte store."""

    def __init__(self):
        self.writes = []
        self.mem = {}

    def write(self, addr, val):
        self.writes.append((addr & 0xFFFF_FFFF, val & 0xFFFF_FFFF))
        self.mem[addr & 0xFFFF_FFFF] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr & 0xFFFF_FFFF, 0)


# ---------------------------------------------------------------------------
# CSR offset layout
# ---------------------------------------------------------------------------
def test_kick_go_offset():
    assert hk.CSR_KICK_GO == hk.HARNESS_CSR_BASE + 0xC0


def test_kick_addr_slots_split_around_kick_go():
    """ch 0..3 -> 0xB0/B4/B8/BC, ch 4..7 -> 0xC4/C8/CC/D0. The naive base+4*ch
    stride would land ch=4 on 0xC0 (KICK_GO) -- this asserts it does not."""
    off = [hk.kick_addr_csr(c) - hk.HARNESS_CSR_BASE for c in range(8)]
    assert off == [0xB0, 0xB4, 0xB8, 0xBC, 0xC4, 0xC8, 0xCC, 0xD0]
    assert hk.CSR_KICK_GO - hk.HARNESS_CSR_BASE == 0xC0
    assert (0xC0) not in off               # KICK_GO slot never used as an address
    assert len(set(off)) == 8              # every channel distinct


@pytest.mark.parametrize("ch", [-1, 8, 99])
def test_kick_addr_out_of_range_rejected(ch):
    with pytest.raises(ValueError):
        hk.kick_addr_csr(ch)


# ---------------------------------------------------------------------------
# batch_kick: program addresses, then the go bit
# ---------------------------------------------------------------------------
def test_batch_kick_single_channel():
    br = RecordingBridge()
    mask = hk.batch_kick(br, {0: 0x1234_5678})
    assert mask == 0b1
    assert br.writes == [
        (hk.kick_addr_csr(0), 0x1234_5678),
        (hk.CSR_KICK_GO, 0b1),
    ]


def test_batch_kick_go_bit_written_last_after_all_addresses():
    """The go bit must be the FINAL write, after every address is latched, so a
    single KICK_GO fires all channels back-to-back."""
    br = RecordingBridge()
    kicks = {0: 0xA000, 2: 0xB000, 5: 0xC000}
    mask = hk.batch_kick(br, kicks)
    assert mask == (1 << 0) | (1 << 2) | (1 << 5)
    # last write is KICK_GO with the full mask
    assert br.writes[-1] == (hk.CSR_KICK_GO, mask)
    # exactly one KICK_GO write; the rest are address latches
    go_writes = [w for w in br.writes if w[0] == hk.CSR_KICK_GO]
    assert go_writes == [(hk.CSR_KICK_GO, mask)]
    for ch, addr in kicks.items():
        assert (hk.kick_addr_csr(ch), addr) in br.writes


def test_batch_kick_truncates_to_32_bits():
    """The shadow register is 32 bits (no separate HIGH word like apbtodescr)."""
    br = RecordingBridge()
    hk.batch_kick(br, {1: 0x9_ABCD_1234})
    assert (hk.kick_addr_csr(1), 0xABCD_1234) in br.writes


def test_batch_kick_empty_is_noop():
    br = RecordingBridge()
    assert hk.batch_kick(br, {}) == 0
    assert br.writes == []


def test_batch_kick_raises_on_write_failure():
    class FailBridge(RecordingBridge):
        def write(self, addr, val):
            super().write(addr, val)
            return False
    with pytest.raises(IOError):
        hk.batch_kick(FailBridge(), {0: 0x1000})


# ---------------------------------------------------------------------------
# Integration: the ext suite kicks via KICK_GO, not the slow apbtodescr path
# ---------------------------------------------------------------------------
def test_run_case_uses_kick_go_fast_path():
    """run_case must drive the harness KICK_GO fast path (a write to CSR_KICK_GO),
    NOT the per-channel apbtodescr CHx_CTRL LOW/HIGH kick."""
    br = RecordingBridge()
    s = Stream(br, "stream0", regs_base=0x0000_0000,
               desc_ram_base=0x0002_0000, data_width=128)
    # Script channel_state: leave IDLE then return IDLE.
    seq = iter([0x04, suite.CH_IDLE])
    s.channel_state = lambda ch: next(seq)

    res = suite.run_case(s, 0, "row/row", 4, 4, poll_max=10)
    assert res["ok"] and res["beats"] == 16

    addrs = [w[0] for w in br.writes]
    assert hk.CSR_KICK_GO in addrs, "run_case did not use the KICK_GO fast path"
    assert (hk.CSR_KICK_GO, 0b1) in br.writes
    # the slow apbtodescr kick register must NOT be used
    assert s.addr("CH0_CTRL_LOW") not in addrs
    assert s.addr("CH0_CTRL_HIGH") not in addrs
