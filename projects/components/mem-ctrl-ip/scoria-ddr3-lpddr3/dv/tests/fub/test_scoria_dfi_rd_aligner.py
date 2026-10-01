# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_dfi_rd_aligner` -- read-enable window + capture framing.

Two things in this module have been got wrong before, both recorded in its own
comments, and both are the reason this file exists:

  1. The ENABLE-WINDOW CREDIT must be COMBINATIONAL. Under the a7_read_gated
     model the device drives DQ inside the enable window, so data and enable
     land on the SAME cycle; a registered credit reads zero on the first enable
     cycle and the first word of the burst is thrown away. That was tried and
     reverted twice (dcaedce4b in July, again 2026-09-15). The case
     `first_word_captures_in_window` is that regression, as a test.
  2. The credit exists to reject the a7ddrphy PREAMBLE valid, which arrives one
     cycle BEFORE the window with the device not driving DQ -- and
     `r_outstanding` does not exclude it, because the read IS outstanding then.
     Capturing it fires rd_last a word early and shifts the entire stream.
     `preamble_valid_is_rejected` pins that.

Everything downstream is a stream, so an error here does not show up as a bad
beat: a single word dropped or added shifts every later beat and the run ends
"read engine did not complete" with the whole remainder mismatched. The checks
are therefore on the WHOLE captured stream -- word count, order, and where
`rd_last` falls -- not on individual beats.

The PHY model matters as much as the DUT. `phy='in_window'` drives a valid on
every cycle the aligner enables, which is the a7_read_gated behaviour and the
regime the board runs in; `phy='preamble'` adds the one early valid the real
a7ddrphy emits. A model that returns data on a fixed latency unrelated to the
enable window would test a device that does not exist.
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
MAX_OUTSTANDING = 8


class AlignTB(TBBase):
    def __init__(self, dut, bl_words, en_cyc, rdlat):
        super().__init__(dut)
        self.bl = bl_words
        self.en_cyc = en_cyc
        self.rdlat = rdlat
        self.word = 0

    async def setup(self):
        await self.start_clock('dfi_clk', 10, 'ns')
        d = self.dut
        d.t_rddata_en_i.value = self.rdlat
        d.op_valid_i.value = 0
        d.dfi_rddata_i.value = 0
        d.dfi_rddata_valid_i.value = 0
        d.rd_ready_i.value = 1
        self.word = 0
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

    def en(self):
        return 1 if int(self.dut.dfi_rddata_en_o.value) else 0

    async def run_cycles(self, n, *, admits=(), phy='none', ready=lambda i: True,
                         preamble_at=None):
        """Step n cycles; drive admits/PHY returns; collect everything.

        Each cycle: present op_valid and rd_ready, settle, read the enable the
        aligner is asserting NOW, drive the PHY's response for THIS cycle from
        it (data inside the window, as the gated model does), settle again, then
        sample the capture outputs. The second settle is what makes the
        same-cycle enable/data case -- the one a registered credit fails --
        reachable at all.
        """
        d = self.dut
        admits = set(admits)
        trace = []                 # per cycle: (en, admitted, rd_valid, data, last)
        offer = 0                  # words the PHY still owes (phy='bl_words')
        prev_en = 0
        for i in range(n):
            d.op_valid_i.value = 1 if i in admits else 0
            d.rd_ready_i.value = 1 if ready(i) else 0
            await Timer(1, 'ns')
            en_now = self.en()
            drive = False
            if phy == 'in_window' and en_now:
                drive = True
            elif phy == 'bl_words':
                # The device returns BL_WORDS words per read starting at the
                # window, whatever the window's width. Used only to show what
                # happens when EN_CYC < BL_WORDS.
                if en_now and not prev_en:
                    offer = self.bl
                if offer:
                    drive = True
                    offer -= 1
            elif phy == 'preamble':
                if en_now or (preamble_at is not None and i == preamble_at):
                    drive = True
            prev_en = en_now
            if drive:
                self.word += 1
                d.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
                d.dfi_rddata_i.value = self.word
            else:
                d.dfi_rddata_valid_i.value = 0
            await Timer(1, 'ns')
            rec = {
                'cyc': i,
                'en': en_now,
                'admit': bool(int(d.op_valid_i.value) and int(d.op_ready_o.value)),
                'op_ready': int(d.op_ready_o.value),
                'rd_valid': int(d.rd_valid_o.value),
                'data': int(d.rd_data_o.value),
                'last': int(d.rd_last_o.value),
                'fired': bool(int(d.rd_valid_o.value) and int(d.rd_ready_i.value)),
                'drove': self.word if drive else None,
            }
            trace.append(rec)
            await self.tick()
        d.op_valid_i.value = 0
        d.dfi_rddata_valid_i.value = 0
        return trace


def captured(trace):
    """The accepted read stream: (data, last) per handshake."""
    return [(t['data'], t['last']) for t in trace if t['fired']]


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_scoria_dfi_rd_aligner(dut):
    tt = os.environ.get("TEST_TYPE", "enable_window_is_exact")
    bl = int(os.environ.get("BL_WORDS", "2"))
    en_cyc = int(os.environ.get("EN_CYC", "2"))
    rdlat = int(os.environ.get("RDLAT", "4"))
    tb = AlignTB(dut, bl, en_cyc, rdlat)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "enable_window_is_exact":
        # dfi_rddata_en tells the PHY when to sample DQ. Too early or too late
        # and the data is latched off the eye -- which on silicon reads as a
        # calibration problem, not as a controller bug.
        for lat in (0, 1, 4, 9):
            await tb.setup()
            dut.t_rddata_en_i.value = lat
            await Timer(1, 'ns')
            trace = await tb.run_cycles(lat + en_cyc + 6, admits=(2,))
            hi = [t['cyc'] for t in trace if t['en']]
            want = list(range(2 + lat, 2 + lat + en_cyc))
            chk(hi == want,
                f"t_rddata_en={lat}: enable high on cycles {hi}, expected "
                f"{want} -- the window must be EN_CYC={en_cyc} cycles wide and "
                f"open exactly {lat} cycles after the admit")

    elif tt == "enable_windows_union_for_overlapping_reads":
        # Reads issue every tCCD, so windows overlap. The delay line asserts
        # enable if ANY in-flight read is inside its own window; a design that
        # tracked one read at a time would drop the second window.
        await tb.setup()
        trace = await tb.run_cycles(rdlat + en_cyc + 10, admits=(2, 3, 4))
        hi = [t['cyc'] for t in trace if t['en']]
        want = sorted({2 + rdlat + k + j for k in range(3)
                       for j in range(en_cyc)})
        chk(hi == want,
            f"three admits one cycle apart gave enable on {hi}, expected the "
            f"union {want} -- a gap inside the union is a read whose data the "
            f"PHY was never told to sample")

    elif tt == "op_ready_backpressures_at_max":
        # The safety net: with MAX_OUTSTANDING reads in flight and no returns,
        # op_ready must drop, or the aligner loses track of which words belong
        # to which read.
        await tb.setup()
        trace = await tb.run_cycles(MAX_OUTSTANDING + 6,
                                    admits=tuple(range(MAX_OUTSTANDING + 4)))
        n_admit = sum(1 for t in trace if t['admit'])
        chk(n_admit == MAX_OUTSTANDING,
            f"{n_admit} reads admitted with no returns; MAX_OUTSTANDING is "
            f"{MAX_OUTSTANDING} and op_ready must refuse the rest")
        chk(trace[-1]['op_ready'] == 0,
            "op_ready still high with the queue full")

    elif tt == "capture_frames_each_read":
        # BL_WORDS words per read, rd_last on the last of them, data forwarded
        # unchanged and in order.
        await tb.setup()
        trace = await tb.run_cycles(rdlat + en_cyc + 8, admits=(2,),
                                    phy='in_window')
        got = captured(trace)
        chk(len(got) == bl,
            f"{len(got)} words captured for one read, expected BL_WORDS={bl} "
            f"-- a short frame leaves the AR-order drain waiting forever and a "
            f"long one shifts the next read")
        chk([g[1] for g in got] == [0] * (bl - 1) + [1],
            f"rd_last pattern {[g[1] for g in got]}, expected it only on word "
            f"{bl}")
        chk([g[0] for g in got] == list(range(1, bl + 1)),
            f"data {[g[0] for g in got]} -- the PHY drove "
            f"{list(range(1, bl + 1))} in that order and the aligner must "
            f"forward it unchanged")

    elif tt == "en_cyc_below_bl_words_is_unsupported":
        # NOT a wish -- a measurement of a constraint nothing states. The
        # enable-window credit mints ONE credit per enable cycle and spends one
        # per captured word, so EN_CYC cycles can only ever admit EN_CYC words.
        # A build with EN_CYC < BL_WORDS therefore DROPS words silently: the
        # stream goes short and every later beat shifts.
        #
        # Reachable? RD_EN_CYC exists in scoria_dfi_layer precisely for the
        # narrow-device case ("set separately when the DRAM beat != device
        # word") and NO instantiation ever sets it -- it defaults to BL_WORDS
        # everywhere, while scoria_top computes the true DQ occupancy
        # ceil(DRAM_BL/DFI_RATE) for its tRTW floor and keeps it local. So the
        # knob is dead today and the two values agree; this case is the gate
        # that makes a future narrow build fail here instead of on the board.
        await tb.setup()
        trace = await tb.run_cycles(rdlat + bl + 8, admits=(2,),
                                    phy='bl_words')
        got = captured(trace)
        chk(len(got) == min(bl, en_cyc),
            f"the PHY offered {bl} words into a {en_cyc}-cycle enable window "
            f"and {len(got)} were captured. The credit admits at most EN_CYC "
            f"words per read, so this must be {min(bl, en_cyc)} -- if it is "
            f"now {bl}, the gate has been reworked and the EN_CYC >= BL_WORDS "
            f"constraint is lifted: update the module header and this case.")
        chk(len(got) < bl,
            f"EN_CYC={en_cyc} < BL_WORDS={bl} captured the whole burst "
            f"({len(got)} words), which would mean the constraint recorded in "
            f"the header no longer holds")

    elif tt == "first_word_captures_in_window":
        # THE REGRESSION. Data and enable on the same cycle: a registered
        # credit reads 0 on the first enable cycle and drops word 1, so the
        # stream is short by one and every later beat is shifted.
        await tb.setup()
        trace = await tb.run_cycles(rdlat + en_cyc + 8, admits=(2,),
                                    phy='in_window')
        got = captured(trace)
        first_en = next(t['cyc'] for t in trace if t['en'])
        fired_on_first_en = any(t['fired'] for t in trace
                                if t['cyc'] == first_en)
        chk(fired_on_first_en,
            f"nothing was captured on the first enable cycle ({first_en}) "
            f"even though the PHY drove data there. This is the registered-"
            f"credit regression: the credit must include THIS cycle's enable "
            f"(w_credit_avail = r_credit + w_en), or the first word of every "
            f"burst is lost.")
        chk(len(got) == bl and got[0][0] == 1,
            f"captured {got}; the first word the PHY drove (1) must be the "
            f"first word out")

    elif tt == "preamble_valid_is_rejected":
        # The a7ddrphy preamble: one valid one cycle BEFORE the window, device
        # not driving DQ. r_outstanding does not exclude it -- the read IS
        # outstanding -- so only the enable-window credit can.
        await tb.setup()
        pre = 2 + rdlat - 1
        trace = await tb.run_cycles(rdlat + en_cyc + 8, admits=(2,),
                                    phy='preamble', preamble_at=pre)
        got = captured(trace)
        pre_fired = any(t['fired'] for t in trace if t['cyc'] == pre)
        chk(not pre_fired,
            f"the preamble valid at cycle {pre} was CAPTURED. It carries no "
            f"device data, and taking it fires rd_last one word early and "
            f"shifts the whole stream.")
        chk(len(got) == bl,
            f"{len(got)} words captured with a preamble present, expected "
            f"{bl}: the gate must reject the preamble and nothing else")
        chk([g[1] for g in got] == [0] * (bl - 1) + [1],
            f"rd_last pattern {[g[1] for g in got]} with a preamble present")

    elif tt == "stray_valid_without_a_read_is_dropped":
        # Nothing outstanding: a valid is noise (a trailing PHY beat, a
        # mis-trained gate) and must not enter the stream.
        await tb.setup()
        d = dut
        for _ in range(6):
            d.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
            d.dfi_rddata_i.value = 0xDEAD
            await Timer(1, 'ns')
            chk(int(d.rd_valid_o.value) == 0,
                "rd_valid high for a PHY beat with no read outstanding -- that "
                "word would be returned to whichever request drains next")
            await tb.tick()
        d.dfi_rddata_valid_i.value = 0
        # And a real read still works afterwards.
        trace = await tb.run_cycles(rdlat + en_cyc + 8, admits=(2,),
                                    phy='in_window')
        chk(len(captured(trace)) == bl,
            f"after stray valids a real read captured "
            f"{len(captured(trace))} words, expected {bl}")

    elif tt == "two_reads_frame_independently":
        # Back-to-back reads: the word stream must split BL_WORDS / BL_WORDS
        # with rd_last on each boundary. This is where an off-by-one credit
        # shows as "the second read returns the first read's tail".
        await tb.setup()
        trace = await tb.run_cycles(rdlat + 3 * en_cyc + 12,
                                    admits=(2, 2 + en_cyc), phy='in_window')
        got = captured(trace)
        chk(len(got) == 2 * bl,
            f"{len(got)} words for two reads, expected {2 * bl}")
        lasts = [i for i, g in enumerate(got) if g[1]]
        chk(lasts == [bl - 1, 2 * bl - 1],
            f"rd_last fell at word indices {lasts}, expected "
            f"{[bl - 1, 2 * bl - 1]} -- each read must be delimited at its own "
            f"BL_WORDS boundary")
        chk([g[0] for g in got] == list(range(1, 2 * bl + 1)),
            f"data order {[g[0] for g in got]}")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '43')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        reads = {"GATE": 4, "FUNC": 16, "FULL": 50}.get(lvl, 16)
        await tb.setup()
        # Admit reads on a random cadence no tighter than the enable window, so
        # the PHY model's one-valid-per-enable-cycle stays physical.
        admits, c = [], 2
        for _ in range(reads):
            admits.append(c)
            c += en_cyc + rng.randrange(0, 3)
        trace = await tb.run_cycles(c + rdlat + en_cyc + 12, admits=admits,
                                    phy='in_window')
        got = captured(trace)
        chk(len(got) == reads * bl,
            f"{len(got)} words for {reads} reads, expected {reads * bl}")
        lasts = [i for i, g in enumerate(got) if g[1]]
        chk(lasts == [bl * (k + 1) - 1 for k in range(reads)],
            f"rd_last at {lasts}, expected every {bl}th word")
        chk([g[0] for g in got] == list(range(1, len(got) + 1)),
            "the captured data is not the drive order -- a word was dropped, "
            "duplicated or reordered")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('dfi_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


# (case, BL_WORDS, EN_CYC, t_rddata_en). The board point is BL8 over a 1:4 DFI
# gear: 2 DFI words per read, 2 cycles of DQ occupancy. BL_WORDS != EN_CYC is
# the narrow-device case the header calls out ("equal only when the scoria DRAM
# beat == the device word").
_GATE = [("enable_window_is_exact", 2, 2, 4),
         ("capture_frames_each_read", 2, 2, 4),
         ("first_word_captures_in_window", 2, 2, 4)]
_FUNC = _GATE + [
    ("enable_window_is_exact", 4, 4, 6),
    ("enable_windows_union_for_overlapping_reads", 2, 2, 4),
    ("op_ready_backpressures_at_max", 2, 2, 4),
    ("capture_frames_each_read", 4, 4, 6),
    ("en_cyc_below_bl_words_is_unsupported", 2, 1, 4),
    ("first_word_captures_in_window", 4, 4, 6),
    ("preamble_valid_is_rejected", 2, 2, 4),
    ("preamble_valid_is_rejected", 4, 4, 6),
    ("stray_valid_without_a_read_is_dropped", 2, 2, 4),
    ("two_reads_frame_independently", 2, 2, 4),
    ("random_soak", 2, 2, 4),
    ("random_soak", 4, 4, 6),
]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type, bl_words, en_cyc, rdlat", _PARAMS)
def test_scoria_dfi_rd_aligner(request, test_type, bl_words, en_cyc, rdlat):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_dfi_rd_aligner"
    test_name = (f"test_scoria_dfi_rd_aligner_{test_type}"
                 f"_b{bl_words}_e{en_cyc}")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_dfi_rd_aligner.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_dfi_rd_aligner",
        sim_build=sim_build, simulator="verilator",
        parameters={"DFI_DATA_WIDTH": str(DFI_DATA_WIDTH),
                    "DFI_RATE": str(DFI_RATE),
                    "BL_WORDS": str(bl_words), "EN_CYC": str(en_cyc),
                    "MAX_OUTSTANDING": str(MAX_OUTSTANDING)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "BL_WORDS": str(bl_words), "EN_CYC": str(en_cyc),
                   "RDLAT": str(rdlat), "TEST_LEVEL": _TEST_LEVEL,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
