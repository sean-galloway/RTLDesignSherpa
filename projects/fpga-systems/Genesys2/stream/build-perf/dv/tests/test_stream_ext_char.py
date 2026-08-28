# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less validation of the extended-addressing characterization sweeps.

Focuses on the channel-count scaling sweep (aggregate bus utilization vs. number
of channels for the transpose modes): each of N channels gets its own extended
descriptor programmed by name, all N are kicked back-to-back via the harness
KICK_GO fast path, and the run waits for every channel to return to IDLE. Checks
the programming/kick bytes against a recording mock bridge -- no RTL, no UART.
The same code runs in cocotb sim and on the board.
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

import harness_kick as hk                 # noqa: E402
import host_ext_char as ec              # noqa: E402
from stream_addrs import A                # noqa: E402  (by-name STREAM regs)
from stream_device import Stream          # noqa: E402

# The launch register, by NAME. Never a literal offset -- see
# [[registers-by-name]]; a pinned number is a test that fails the next time the
# regmap legitimately moves.
KICK_ENABLE = A("KICK_ENABLE")


class RecordingBridge:
    def __init__(self):
        self.writes = []
        self.mem = {}

    def write(self, addr, val):
        self.writes.append((addr & 0xFFFF_FFFF, val & 0xFFFF_FFFF))
        self.mem[addr & 0xFFFF_FFFF] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr & 0xFFFF_FFFF, 0)


def _stream(bridge):
    return Stream(bridge, "stream0", regs_base=0x0000_0000,
                  desc_ram_base=0x0002_0000, data_width=128)


def test_scaling_defaults():
    """The scaling sweep targets the two transpose modes and a 1..8 channel set."""
    assert ec.SCALING_CASES == ("row/col", "col/row")
    assert ec.DEFAULT_CHANNEL_COUNTS == (1, 2, 4, 8)
    # both scaling cases are genuinely transpose (per-beat on exactly one side)
    from stream_ext_suite import build_case
    BS = 16
    for case in ec.SCALING_CASES:
        rd, wr = build_case(case, 8, 8, BS)
        per_beat = (rd["s0"] != BS, wr["s0"] != BS)
        assert per_beat.count(True) == 1, f"{case} is not a transpose case"


@pytest.mark.parametrize("nch", [1, 2, 4, 8])
def test_measure_scaling_kicks_all_channels_once(nch):
    """N channels each get a descriptor, then ONE KICK_ENABLE fires them together.

    Was written against the harness KICK_GO CSR, which commits 9cdd860d /
    c16b2041 retired when the kick moved inside STREAM. The guarantee is
    unchanged -- one launch write, every channel's bit set, staged addresses
    first -- so only the register it is asserted against moves.
    """
    br = RecordingBridge()
    s = _stream(br)
    s.channel_state = lambda ch: CH_IDLE_VAL   # all idle -> _wait_all returns ok
    rec = ec.measure_scaling(s, "row/col", 8, 8, nch, poll_max=10)

    assert rec["nch"] == nch
    assert rec["beats"] == nch * 8 * 8
    assert rec["ok"] and rec["reason"] == "idle"

    # exactly one launch, with every channel's bit set, written after the addrs
    go = [w for w in br.writes if w[0] == KICK_ENABLE]
    assert len(go) == 1
    expected_mask = sum(1 << ch for ch in range(nch))
    assert go[0] == (KICK_ENABLE, expected_mask)
    # each channel's descriptor address was staged BEFORE the launch fired
    launch_idx = [w[0] for w in br.writes].index(KICK_ENABLE)
    for ch in range(nch):
        assert any(w[0] == hk.kick_addr_csr(ch)
                   for w in br.writes[:launch_idx]), \
            f"ch{ch} launched without its descriptor address staged first"


def test_measure_scaling_reports_error_channel():
    """A channel that enters CH_ERROR fails the run (not silently 'idle')."""
    br = RecordingBridge()
    s = _stream(br)
    s.channel_state = lambda ch: CH_ERROR_VAL if ch == 1 else CH_IDLE_VAL
    rec = ec.measure_scaling(s, "col/row", 8, 8, 4, poll_max=10)
    assert not rec["ok"]
    assert "CH_ERROR" in rec["reason"] and "ch1" in rec["reason"]


def test_run_channel_scaling_shape():
    """One record per (case, nch); util is present and finite."""
    br = RecordingBridge()
    s = _stream(br)
    s.channel_state = lambda ch: CH_IDLE_VAL
    recs = ec.run_channel_scaling(s, size=(8, 8), channel_counts=(1, 2, 4),
                                  poll_max=10)
    assert len(recs) == len(ec.SCALING_CASES) * 3
    nchs = sorted({r["nch"] for r in recs})
    assert nchs == [1, 2, 4]
    for r in recs:
        assert "util" in r["rd"] and "util" in r["wr"]


# stream_pkg.sv one-hot channel_state_t
CH_IDLE_VAL = 0x01
CH_ERROR_VAL = 0x20
