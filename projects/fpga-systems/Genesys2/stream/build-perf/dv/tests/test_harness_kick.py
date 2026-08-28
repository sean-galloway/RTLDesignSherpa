# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less validation of the multi-channel batch kick.

The launch is stage-then-fire: write each channel's descriptor address into
STREAM's CHx_CTRL_LOW, then ONE write to STREAM's KICK_ENABLE carrying a channel
bitmask. Every selected channel starts on the same aclk cycle, so a
multi-channel run measures real concurrency instead of a staggered start that
drifts by a UART round trip per channel.

These tests pin the write ORDERING and the mask against a recording mock bridge
-- no RTL, no UART. The same batch_kick() then runs in cocotb sim and on the
board.

History: this file used to assert a harness-side KICK_GO CSR at
HARNESS_CSR_BASE+0xC0, with per-channel shadow registers at 0xB0..0xD0 split
around that slot, and asserted that CH0_CTRL_LOW was NEVER written. Commits
9cdd860d / c16b2041 internalized the kick: harness_csr no longer shadows
descriptor addresses, STREAM's i_kick_burst_* ports are gone, and CHx_CTRL_LOW
IS the staging register. The old assertions inverted -- what was once proof of
the fast path is now proof of the slow one -- so they are rewritten here rather
than deleted: the guarantee under test (single-shot launch, go bit last) is
unchanged and still worth pinning.
"""

import os
import sys

import pytest

# `../../host` still resolves (build-perf/host) -- but the modules under test
# MOVED: the shared libraries (harness_kick, stream_device, stream_ext_suite,
# descriptor_builder) are COMPONENT level in bin/ now, and only the host_*
# entry points remain in this build's host/. Both go on the path.
_TESTS = os.path.dirname(os.path.abspath(__file__))                     # dv/tests/
_BUILD = os.path.dirname(os.path.dirname(_TESTS))                       # build-perf/
_AREA  = os.path.dirname(_BUILD)                                        # stream/
for _p in (os.path.join(_BUILD, "host"), os.path.join(_AREA, "bin")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import harness_kick as hk                    # noqa: E402
import stream_ext_suite as suite             # noqa: E402
from stream_addrs import A                   # noqa: E402  (by-name STREAM regs)
from stream_device import Stream             # noqa: E402

# The launch register. By NAME -- never a literal offset, or this test pins a
# number the regmap is free to move (see [[registers-by-name]]).
KICK_ENABLE = A("KICK_ENABLE")


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
# Staging-register resolution
# ---------------------------------------------------------------------------
def test_kick_addr_is_the_stream_channel_ctrl_register():
    """kick_addr_csr(ch) resolves CHx_CTRL_LOW -- a STREAM register now, not a
    harness shadow. Resolved by name on both sides so the two cannot drift."""
    for ch in range(8):
        assert hk.kick_addr_csr(ch) == A(f"CH{ch}_CTRL_LOW")


def test_kick_addr_slots_are_distinct():
    """Eight channels, eight distinct staging registers. The old layout had to
    dodge a KICK_GO slot at 0xC0; the current one has no hole to avoid, but the
    channels must still never alias."""
    off = [hk.kick_addr_csr(c) for c in range(8)]
    assert len(set(off)) == 8
    assert KICK_ENABLE not in off, \
        "a channel's staging register collides with the launch register"


@pytest.mark.parametrize("ch", [-1, 8, 99])
def test_kick_addr_out_of_range_rejected(ch):
    with pytest.raises(ValueError):
        hk.kick_addr_csr(ch)


# ---------------------------------------------------------------------------
# batch_kick: stage every address, then fire once
# ---------------------------------------------------------------------------
def test_batch_kick_single_channel():
    br = RecordingBridge()
    mask = hk.batch_kick(br, {0: 0x1234_5678})
    assert mask == 0b1
    assert br.writes == [
        (hk.kick_addr_csr(0), 0x1234_5678),
        (KICK_ENABLE, 0b1),
    ]


def test_batch_kick_launch_written_last_after_all_addresses():
    """KICK_ENABLE must be the FINAL write, after every address is staged.

    This is the whole point of the batch kick: one write launches all selected
    channels on the same clock edge. If a launch were emitted mid-sequence, the
    channels staged after it would start a UART round trip late and every
    cross-channel perf number would be measuring the host, not the DUT.
    """
    br = RecordingBridge()
    kicks = {0: 0xA000, 2: 0xB000, 5: 0xC000}
    mask = hk.batch_kick(br, kicks)
    assert mask == (1 << 0) | (1 << 2) | (1 << 5)
    # last write is the launch, carrying the full mask
    assert br.writes[-1] == (KICK_ENABLE, mask)
    # exactly one launch write; everything else is address staging
    launches = [w for w in br.writes if w[0] == KICK_ENABLE]
    assert launches == [(KICK_ENABLE, mask)]
    # every requested channel was staged BEFORE the launch
    launch_idx = br.writes.index((KICK_ENABLE, mask))
    for ch, addr in kicks.items():
        assert (hk.kick_addr_csr(ch), addr) in br.writes[:launch_idx]


def test_batch_kick_truncates_to_32_bits():
    """batch_kick programs the LOW word only; CHx_CTRL_HIGH is a separate stored
    register a >4 GB caller must stage itself."""
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
# Integration: the ext suite launches via KICK_ENABLE
# ---------------------------------------------------------------------------
def test_run_case_uses_the_batch_launch():
    """run_case must stage CHx_CTRL_LOW and fire KICK_ENABLE.

    Note the inversion versus the pre-refactor version of this test: it used to
    assert CH0_CTRL_LOW was never written, because writing it WAS the slow
    apb4todescr kick. Now CH0_CTRL_LOW is the staging register and writing it is
    correct; what must not happen is a launch that is not the final write.
    """
    br = RecordingBridge()
    s = Stream(br, "stream0", regs_base=0x0000_0000,
               desc_ram_base=0x0002_0000, data_width=128)
    # Script channel_state: leave IDLE then return IDLE.
    seq = iter([0x04, suite.CH_IDLE])
    s.channel_state = lambda ch: next(seq)

    res = suite.run_case(s, 0, "row/row", 4, 4, poll_max=10)
    assert res["ok"] and res["beats"] == 16

    addrs = [w[0] for w in br.writes]
    assert KICK_ENABLE in addrs, "run_case did not launch via KICK_ENABLE"
    assert (KICK_ENABLE, 0b1) in br.writes
    # the descriptor address must be staged before the launch fires
    launch_idx = addrs.index(KICK_ENABLE)
    assert s.addr("CH0_CTRL_LOW") in addrs[:launch_idx], \
        "channel 0 was launched without its descriptor address staged first"
