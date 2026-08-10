# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less validation of the STREAM extended-addressing FPGA suite.

Checks the four row/col cases map to the correct addressing modes and program
correct, distinct descriptors through the named Stream API (mock bridge, no RTL).
Separate from the existing characterization tests; the same suite then runs in
cocotb sim and on the board.
"""

import os
import sys

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

from stream_device import Stream          # noqa: E402
import stream_ext_suite as suite          # noqa: E402
import descriptor_builder as db           # noqa: E402

BS = 16  # DATA_WIDTH=128 -> 16 bytes/beat


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


def test_cases_and_modes():
    """row -> contiguous inner (burst); col -> strided inner (per-beat)."""
    W, H = 4, 4
    assert suite.CASES == ("row/row", "row/col", "col/row", "col/col")
    row = suite._layout("row", W, H, BS)
    col = suite._layout("col", W, H, BS)
    assert row["s0"] == BS               # contiguous -> burst
    assert col["s0"] == W * BS != BS     # strided   -> per-beat
    # per-direction mode is what the RTL infers (s0 != beat_size => per-beat)
    modes = {c: tuple(l["s0"] != BS for l in suite.build_case(c, W, H, BS))
             for c in suite.CASES}
    assert modes == {
        "row/row": (False, False),  # burst / burst
        "row/col": (False, True),   # burst / per-beat (transpose)
        "col/row": (True, False),   # per-beat / burst (transpose mirror)
        "col/col": (True, True),    # per-beat / per-beat
    }


def test_program_case_writes_ext_descriptor():
    """Each case programs a valid extended descriptor + kicks by name."""
    W, H = 4, 4
    for case in suite.CASES:
        br = RecordingBridge()
        s = _stream(br)
        kick = suite.program_case(s, 0, case, W, H)
        s.run(0, kick)
        base = 0x0002_0000 + db.DESC_INDEX_OFFSET * 32
        # desc_type=EXT in chunk0 word6, chunk1 present at +0x20
        assert br.mem[base + 6 * 4] & (1 << 16), f"{case}: desc_type not set"
        assert (base + 0x20 + 0 * 4) in br.mem, f"{case}: chunk1 missing"
        # kicked via the named CH0_CTRL_LOW register
        assert (s.addr("CH0_CTRL_LOW"), kick & 0xFFFF_FFFF) in br.writes


def test_cases_program_distinct_configs():
    """The four cases must produce different chunk1 stride words."""
    W, H = 4, 4
    sig = {}
    for case in suite.CASES:
        br = RecordingBridge()
        s = _stream(br)
        suite.program_case(s, 0, case, W, H)
        base = 0x0002_0000 + db.DESC_INDEX_OFFSET * 32 + 0x20
        # (rd_stride_0, rd_stride_1, wr_stride_0, wr_stride_1)
        sig[case] = (br.mem[base + 0], br.mem[base + 4],
                     br.mem[base + 12], br.mem[base + 16])
    assert len(set(sig.values())) == 4, f"cases not distinct: {sig}"


def test_run_suite_flow_completes():
    """run_suite drives all four cases to completion (scripted channel state)."""
    br = RecordingBridge()
    s = _stream(br)
    # Script channel_state: leave IDLE (CH_XFER_DATA) then return IDLE, per case.
    seq = iter([0x04, suite.CH_IDLE] * len(suite.CASES))
    s.channel_state = lambda ch: next(seq)
    results = suite.run_suite(s, channel=0, W=4, H=4, poll_max=10)
    assert set(results) == set(suite.CASES)
    assert all(r["ok"] for r in results.values())
    assert all(r["beats"] == 16 for r in results.values())
