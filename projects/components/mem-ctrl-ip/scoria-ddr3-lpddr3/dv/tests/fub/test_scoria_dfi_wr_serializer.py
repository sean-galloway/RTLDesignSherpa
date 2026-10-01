# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_dfi_wr_serializer` -- write-data drive timing.

This is the write-side mirror of the read aligner, and like it, it was
rewritten to be stateless for a specific reason recorded in its header: "The
prior FSM's 'seamless continuation' assumed the next burst was always due the
cycle after the last word, which drops the tCCD bubble and drives write data
early." Driving write data early puts DQ on the bus before the device is
expecting it -- the failure is at the pins, where sim cannot see it and the
board shows corrupt writes with a clean controller.

So the case that matters most here is `second_burst_waits_for_its_own_maturity`:
two writes spaced further apart than the burst is long must produce TWO drive
runs with a gap, not one contiguous run. The old FSM passes every other check
in this file.

The rest is the mechanical contract, which is still worth pinning because it
lands on the pins: the first `dfi_wrdata_en` exactly `t_phy_wrlat` cycles after
the command (including 0, the same cycle), one word per cycle with no bubbles
inside a burst, and `mask == ~strb` -- a strobe inversion that writes the
complement of the intended lanes is the quietest data-corruption bug in the
write path.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

DFI_DATA_WIDTH = 128
DFI_RATE = 4
STRB_W = DFI_DATA_WIDTH // 8
STRB_ALL = (1 << STRB_W) - 1


class SerTB(TBBase):
    def __init__(self, dut, bl, wrlat):
        super().__init__(dut)
        self.bl = bl                 # DFI words per burst
        self.wrlat = wrlat

    async def setup(self):
        await self.start_clock('dfi_clk', 10, 'ns')
        d = self.dut
        d.t_phy_wrlat_i.value = self.wrlat
        d.wr_fire_i.value = 0
        d.wd_valid_i.value = 0
        d.wd_data_i.value = 0
        d.wd_strb_i.value = STRB_ALL
        d.wd_last_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('dfi_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('dfi_clk', 2)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.dfi_rstn.value = 0

    async def deassert_reset(self):
        self.dut.dfi_rstn.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def tick(self):
        await RisingEdge(self.dut.dfi_clk)
        await Timer(1, 'ns')

    async def run_cycles(self, n, *, fires=(), words=None, strb=None,
                         feed=lambda i: True):
        """Step n cycles with a FIFO that presents `words` in order.

        The FIFO is modelled as always having the next word available (the
        header's "the burst is already waiting" -- the wr CAM pre-stages it),
        except where `feed` returns False, which is how the starved-FIFO case
        is built. A word is consumed only on wd_valid && wd_ready.
        """
        d = self.dut
        fires = set(fires)
        words = list(words if words is not None else [])
        wi = 0
        trace = []
        for i in range(n):
            d.wr_fire_i.value = 1 if i in fires else 0
            have = (wi < len(words)) and feed(i)
            d.wd_valid_i.value = 1 if have else 0
            if have:
                val, last = words[wi]
                d.wd_data_i.value = val
                d.wd_last_i.value = 1 if last else 0
                d.wd_strb_i.value = STRB_ALL if strb is None else strb[wi]
            else:
                d.wd_last_i.value = 0
            await Timer(1, 'ns')
            rec = {
                'cyc': i,
                'en': 1 if int(d.dfi_wrdata_en_o.value) else 0,
                'en_raw': int(d.dfi_wrdata_en_o.value),
                'data': int(d.dfi_wrdata_o.value),
                'mask': int(d.dfi_wrdata_mask_o.value),
                'ready': int(d.wd_ready_o.value),
                'popped': bool(have and int(d.wd_ready_o.value)),
                'word': words[wi] if have else None,
                'strb': (STRB_ALL if strb is None else strb[wi]) if have else None,
            }
            trace.append(rec)
            if rec['popped']:
                wi += 1
            await self.tick()
        d.wr_fire_i.value = 0
        d.wd_valid_i.value = 0
        d.wd_last_i.value = 0
        return trace


def burst(n, base=1):
    """n words, last on the final one."""
    return [(base + k, k == n - 1) for k in range(n)]


def runs(trace):
    """Contiguous runs of drive cycles: [(first_cyc, length), ...]."""
    out = []
    for t in trace:
        if t['en']:
            if out and out[-1][0] + out[-1][1] == t['cyc']:
                out[-1] = (out[-1][0], out[-1][1] + 1)
            else:
                out.append((t['cyc'], 1))
    return [tuple(r) for r in out]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_scoria_dfi_wr_serializer(dut):
    tt = os.environ.get("TEST_TYPE", "wrlat_is_exact")
    bl = int(os.environ.get("BL_WORDS", "2"))
    wrlat = int(os.environ.get("WRLAT", "4"))
    tb = SerTB(dut, bl, wrlat)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "wrlat_is_exact":
        # t_phy_wrlat is the PHY's command-to-data offset. Early and the device
        # is not listening yet; late and it has already sampled. Both are
        # pin-level failures a controller-only sim cannot see, which is why the
        # number is pinned here. wrlat=0 must drive on the fire cycle itself.
        for lat in (0, 1, 4, 9):
            await tb.setup()
            dut.t_phy_wrlat_i.value = lat
            await Timer(1, 'ns')
            trace = await tb.run_cycles(lat + bl + 6, fires=(3,),
                                        words=burst(bl))
            r = runs(trace)
            chk(r == [(3 + lat, bl)],
                f"t_phy_wrlat={lat}: drive runs {r}, expected one run of {bl} "
                f"words starting at cycle {3 + lat} (fire at 3)")

    elif tt == "burst_streams_without_bubbles":
        # "One pop = one DFI cycle = ZERO bubbles." A bubble inside a burst
        # leaves the device mid-burst with no data on DQ.
        await tb.setup()
        trace = await tb.run_cycles(wrlat + bl + 8, fires=(2,), words=burst(bl))
        r = runs(trace)
        chk(r == [(2 + wrlat, bl)],
            f"drive runs {r}; one burst must be one contiguous run of {bl}")
        drove = [t['data'] for t in trace if t['en']]
        chk(drove == [k + 1 for k in range(bl)],
            f"drove {drove}, expected the FIFO's words in order "
            f"{[k + 1 for k in range(bl)]}")
        chk(sum(1 for t in trace if t['popped']) == bl,
            f"{sum(1 for t in trace if t['popped'])} words popped for a "
            f"{bl}-word burst")

    elif tt == "second_burst_waits_for_its_own_maturity":
        # THE regression. Two writes spaced wider than the burst: the second
        # must wait for ITS OWN maturity (fire + wrlat), not start the cycle
        # after the first burst's last word. The old FSM's "seamless
        # continuation" drove the second burst early -- write data on DQ before
        # the device expects it.
        gap = bl + 3
        await tb.setup()
        trace = await tb.run_cycles(wrlat + 2 * bl + gap + 8,
                                    fires=(2, 2 + gap),
                                    words=burst(bl) + burst(bl, base=100))
        r = runs(trace)
        chk(r == [(2 + wrlat, bl), (2 + gap + wrlat, bl)],
            f"drive runs {r}, expected two separate runs at "
            f"{2 + wrlat} and {2 + gap + wrlat}. One merged run means the "
            f"second burst drove as soon as data was available instead of at "
            f"its command's maturity -- the tCCD bubble is gone and DQ is "
            f"driven early.")

    elif tt == "back_to_back_bursts_are_contiguous":
        # The other half of the same claim: writes exactly a burst apart must
        # drive with NO gap, or the datapath has bubbles it does not need.
        await tb.setup()
        trace = await tb.run_cycles(wrlat + 3 * bl + 8,
                                    fires=(2, 2 + bl),
                                    words=burst(bl) + burst(bl, base=100))
        r = runs(trace)
        chk(r == [(2 + wrlat, 2 * bl)],
            f"drive runs {r}, expected one contiguous run of {2 * bl} from "
            f"cycle {2 + wrlat} -- commands a burst apart mature back to back")

    elif tt == "mask_is_the_inverse_of_strb":
        # AXI wstrb=1 means WRITE the byte; DFI mask=1 means MASK it. An
        # inversion here writes the complement of the intended lanes and is the
        # quietest corruption in the write path -- every beat lands, with the
        # wrong bytes.
        pats = [STRB_ALL, 0, 0x00FF, 0xFF00, 0x0F0F,
                random.Random(7).randrange(1 << STRB_W)]
        words = burst(len(pats))
        await tb.setup()
        trace = await tb.run_cycles(wrlat + len(pats) + 8, fires=(2,),
                                    words=words, strb=pats)
        driven = [(t['strb'], t['mask']) for t in trace if t['en']]
        chk(len(driven) == len(pats),
            f"{len(driven)} words driven for {len(pats)} staged")
        for i, (s, m) in enumerate(driven):
            chk(m == (~s) & STRB_ALL,
                f"word {i}: strb=0x{s:X} drove mask=0x{m:X}, expected "
                f"0x{(~s) & STRB_ALL:X} (mask = ~strb)")
        # And nothing is asserted while idle.
        idle = [t for t in trace if not t['en']]
        chk(all(t['mask'] == 0 and t['en_raw'] == 0 for t in idle),
            "mask or en nonzero on an idle cycle -- the PHY would take a "
            "masked write it was never told about")

    elif tt == "no_fire_means_no_drive":
        # Data staged with no command must sit there: wd_ready low, nothing
        # popped, en low. A drive here writes a burst the DRAM never got a
        # command for.
        await tb.setup()
        trace = await tb.run_cycles(12, fires=(), words=burst(bl))
        chk(all(t['en'] == 0 for t in trace),
            "dfi_wrdata_en asserted with no WR command in flight")
        chk(all(t['ready'] == 0 for t in trace),
            "wd_ready asserted with no command -- the FIFO would be drained "
            "and the data lost before its command arrives")
        chk(not any(t['popped'] for t in trace), "a word was popped")

    elif tt == "starved_fifo_pauses_the_drive":
        # The header says the burst is pre-staged so the drive never stalls.
        # If it ever does, the words must still come out in order and exactly
        # once -- a pause must not duplicate or drop a word.
        await tb.setup()
        hole = 2 + wrlat + 1
        trace = await tb.run_cycles(wrlat + bl + 12, fires=(2,),
                                    words=burst(bl),
                                    feed=lambda i: i not in (hole, hole + 1))
        drove = [t['data'] for t in trace if t['en']]
        chk(drove == [k + 1 for k in range(bl)],
            f"with the FIFO starved for two cycles the drive produced {drove}, "
            f"expected {[k + 1 for k in range(bl)]} -- in order and once each")
        chk(all(t['en'] == 0 for t in trace if t['cyc'] in (hole, hole + 1)),
            "en asserted on a cycle with no FIFO word -- that drives stale "
            "data onto DQ")

    elif tt == "two_in_flight_before_any_data":
        # Two commands mature before any data arrives: both are owed, and when
        # the data comes both bursts drive. A single-slot tracker would lose
        # one and leave its burst's data in the FIFO forever.
        await tb.setup()
        n = wrlat + 2 * bl + 10
        start = 2 + wrlat + 2
        trace = await tb.run_cycles(n, fires=(2, 3),
                                    words=burst(bl) + burst(bl, base=100),
                                    feed=lambda i: i >= start)
        drove = [t['data'] for t in trace if t['en']]
        chk(len(drove) == 2 * bl,
            f"{len(drove)} words driven for two owed bursts, expected "
            f"{2 * bl} -- an owed burst was forgotten and its data is stuck "
            f"in the FIFO")
        chk(drove == [k + 1 for k in range(bl)] + [100 + k for k in range(bl)],
            f"drove {drove} -- the two bursts must come out in command order")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '47')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        nb = {"GATE": 4, "FUNC": 14, "FULL": 40}.get(lvl, 14)
        await tb.setup()
        fires, words, c = [], [], 2
        for k in range(nb):
            fires.append(c)
            words += burst(bl, base=1 + 50 * k)
            c += bl + rng.randrange(0, 4)
        trace = await tb.run_cycles(c + wrlat + bl + 12, fires=fires,
                                    words=words)
        drove = [t['data'] for t in trace if t['en']]
        chk(drove == [w[0] for w in words],
            f"{len(drove)} words driven for {len(words)} staged, in "
            f"{'the right' if drove == [w[0] for w in words] else 'the wrong'} "
            f"order")
        r = runs(trace)
        # Every run must start at some command's maturity, never earlier.
        mats = {f + wrlat for f in fires}
        for first, _ in r:
            chk(first in mats,
                f"a drive run starts at cycle {first}, which is no command's "
                f"maturity ({sorted(mats)}) -- data is on DQ early")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('dfi_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


# (case, BL_WORDS, t_phy_wrlat). The board point is BL8 over a 1:4 gear = 2 DFI
# words; BL_WORDS=1 is the x16 BL4 case the header names, where tCCD exceeds the
# DQ occupancy and the maturity bubble is the whole point.
_GATE = [("wrlat_is_exact", 2, 4),
         ("second_burst_waits_for_its_own_maturity", 2, 4),
         ("mask_is_the_inverse_of_strb", 2, 4)]
_FUNC = _GATE + [
    ("wrlat_is_exact", 1, 2),
    ("burst_streams_without_bubbles", 2, 4),
    ("burst_streams_without_bubbles", 4, 6),
    ("second_burst_waits_for_its_own_maturity", 1, 2),
    ("second_burst_waits_for_its_own_maturity", 4, 6),
    ("back_to_back_bursts_are_contiguous", 2, 4),
    ("no_fire_means_no_drive", 2, 4),
    ("starved_fifo_pauses_the_drive", 4, 4),
    ("two_in_flight_before_any_data", 2, 4),
    ("random_soak", 2, 4),
    ("random_soak", 4, 6),
]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type, bl_words, wrlat", _PARAMS)
def test_scoria_dfi_wr_serializer(request, test_type, bl_words, wrlat):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_dfi_wr_serializer"
    test_name = f"test_scoria_dfi_wr_serializer_{test_type}_b{bl_words}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_dfi_wr_serializer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_dfi_wr_serializer",
        sim_build=sim_build, simulator="verilator",
        parameters={"DFI_DATA_WIDTH": str(DFI_DATA_WIDTH),
                    "DFI_RATE": str(DFI_RATE)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "BL_WORDS": str(bl_words), "WRLAT": str(wrlat),
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
