# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_dfi_rd_aligner`.

Checks: rd_fire -> dfi_rddata_en asserts at +t_rddata_en for BL_WORDS cycles;
PHY rddata_valid words are captured + pushed to the read FIFO one/cycle
(bubble-free), data in order, `last` on the BL_WORDS-th word.
"""

import os
import sys
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_consumer, fub_pulse_producer  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_dfi_rd_aligner.f")

DFI_DW = 128
DFI_RATE = 2
# BL_WORDS is env-overridable so a wrapper can exercise the x16 BL4 case
# (BL_WORDS=1), where tCCD (2) > DQ-bus occupancy (1) leaves a read-command
# bubble the contiguous-window aligner must honor. Default 4 = legacy.
BL_WORDS = int(os.environ.get("BL_WORDS", "4"))



def fire_cycles_horizon(nreads, tccd, rden, bl_words):
    """Cycles to run after queueing so every window has landed."""
    return nreads * tccd + rden + bl_words + 10


class _CycleObs:
    """Free-running cycle counter that records WHEN things actually happened.

    The rewrite that makes this file BFM-drivable. The old code measured
    rddata_en relative to the loop index at which the TESTBENCH asserted
    op_valid. A BFM owns the scheduling between "queue a request" and "valid
    asserts", so that index stops meaning anything -- measured as +1 instead
    of +0, and tCCD gaps as [1,1] instead of [2,2].

    Measuring relative to the OBSERVED op handshake instead is both
    BFM-compatible and strictly more honest: it is the DUT's real latency,
    not latency-from-when-the-testbench-decided.

    Samples immediately after the edge with no intervening await -- op_valid_i
    is BFM-driven, and a delayed sample reads the driver's NEXT intent rather
    than what the DUT's flops saw. See [[structure-trackers]].
    """

    def __init__(self, dut):
        self.dut = dut
        self.cycle = -1
        self.fires = []        # cycles where op_valid && op_ready
        self.ens = []          # cycles where dfi_rddata_en_o != 0

    async def run(self):
        while True:
            await RisingEdge(self.dut.dfi_clk)
            self.cycle += 1
            if int(self.dut.op_valid_i.value) and int(self.dut.op_ready_o.value):
                self.fires.append(self.cycle)
            if int(self.dut.dfi_rddata_en_o.value) != 0:
                self.ens.append(self.cycle)


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_pumice_dfi_rd_aligner(dut):
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_rddata_en_i.value = 0
    # op_* and rd_* are BFM-owned. dfi_rddata_* stays hand-driven: DFI read
    # data has NO ready -- an unconditional strobe per spec, not a handshake.
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    op_src = fub_pulse_producer(dut, "op", dut.dfi_clk, log=dut._log,
                                valid="op_valid_i", ready="op_ready_o")
    fub_consumer(dut, "rd", dut.dfi_clk, log=dut._log,
                 valid="rd_valid_o", ready="rd_ready_i",
                 fields={'data': ("rd_data_o", DFI_DW),
                         'resp': ("rd_resp_o", 2),
                         'last': ("rd_last_o", 1)})
    obs = _CycleObs(dut)
    cocotb.start_soon(obs.run())
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    for RDEN in (0, 2, 4):
        await _run(dut, op_src, obs, RDEN)
    dut._log.info("PASS: rddata_en window + bubble-free capture at t_rddata_en in {0,2,4}")


async def _run(dut, op_src, obs, RDEN):
    dut.t_rddata_en_i.value = RDEN
    rng = random.Random(0xEE ^ RDEN)
    words = [rng.randrange(1 << DFI_DW) for _ in range(BL_WORDS)]

    # 1) fire; measure the rddata_en window RELATIVE TO THE OBSERVED FIRE
    n_fire0, n_en0 = len(obs.fires), len(obs.ens)
    await op_src._driver_send(op_src.create_packet(req=1))
    for _ in range(RDEN + BL_WORDS + 8):
        await RisingEdge(dut.dfi_clk)
    assert len(obs.fires) == n_fire0 + 1, "op request never handshook"
    fire = obs.fires[n_fire0]
    en_idx = [c - fire for c in obs.ens[n_en0:]]
    assert len(en_idx) == BL_WORDS, f"rddata_en cycles {len(en_idx)} != {BL_WORDS}: {en_idx}"
    assert en_idx[0] == RDEN, f"rddata_en at +{en_idx[0]}, expected t_rddata_en={RDEN}"
    for a, b in zip(en_idx, en_idx[1:]):
        assert b == a + 1, f"rddata_en window not contiguous: {en_idx}"

    # 2) PHY returns the burst (some cycles later): drive rddata_valid+data,
    #    capture the read-FIFO pushes.
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)
    got, last_at = [], []
    for i, w in enumerate(words):
        dut.dfi_rddata_i.value = w
        dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
        await RisingEdge(dut.dfi_clk)
        # sample the push this cycle
        if int(dut.rd_valid_o.value) and int(dut.rd_ready_i.value):
            got.append(int(dut.rd_data_o.value))
            if int(dut.rd_last_o.value):
                last_at.append(len(got) - 1)
    dut.dfi_rddata_valid_i.value = 0
    await RisingEdge(dut.dfi_clk)

    assert got == words, f"rddata capture {[hex(x) for x in got]} != {[hex(x) for x in words]}"
    assert last_at == [BL_WORDS - 1], f"rd_last at {last_at}, expected only [{BL_WORDS-1}]"

@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_rd_aligner_tccd_paced(dut):
    """x16 BL4 (BL_WORDS=1): reads paced at tCCD=2, one cycle WIDER than the
    DQ-bus occupancy (BL_WORDS=1). The aligner must place each read's
    rddata_en window at ITS OWN fire+t_rddata_en (i.e. tCCD apart), NOT collapse
    them into contiguous back-to-back windows. Collapsing fires the 2nd+ read's
    enable a cycle early -> on the real a7ddrphy that read captures a ZERO beat
    (ILA-confirmed on the Nexys A7: beats_mismatched=32). This is the isolated,
    PHY-model-free reproduction of that silicon read failure."""
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_rddata_en_i.value = 0
    # op_* and rd_* are BFM-owned. dfi_rddata_* stays hand-driven: DFI read
    # data has NO ready -- an unconditional strobe per spec, not a handshake.
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    op_src = fub_pulse_producer(dut, "op", dut.dfi_clk, log=dut._log,
                                valid="op_valid_i", ready="op_ready_o")
    fub_consumer(dut, "rd", dut.dfi_clk, log=dut._log,
                 valid="rd_valid_o", ready="rd_ready_i",
                 fields={'data': ("rd_data_o", DFI_DW),
                         'resp': ("rd_resp_o", 2),
                         'last': ("rd_last_o", 1)})
    obs = _CycleObs(dut)
    cocotb.start_soon(obs.run())
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    assert BL_WORDS == 1, f"tCCD-bubble case needs BL_WORDS=1 (x16 BL4); got {BL_WORDS}"
    RDEN, TCCD, NREADS = 4, 2, 3
    dut.t_rddata_en_i.value = RDEN
    # Space the requests by tCCD using the randomizer -- upstream pacing is a
    # TIMING PROFILE, which is what a randomizer is for. Whatever spacing the
    # profile actually delivers, the property under test is that the OUTPUT
    # tracks the INPUT: the aligner must place each read's window at its own
    # fire+t_rddata_en and must NOT collapse them.
    from tbclasses.pumice_fub_bfm import set_profile
    set_profile(op_src, "fixed", "master")     # valid_delay 1 -> tCCD=2 cadence
    for _ in range(NREADS):
        await op_src._driver_send(op_src.create_packet(req=1))
    for _ in range(fire_cycles_horizon(NREADS, TCCD, RDEN, BL_WORDS)):
        await RisingEdge(dut.dfi_clk)

    fires, en_cycles = obs.fires, obs.ens
    assert len(fires) == NREADS, f"expected {NREADS} op handshakes, got {fires}"
    assert len(en_cycles) == NREADS, \
        f"expected {NREADS} rddata_en pulses, got {en_cycles}"

    in_gaps = [b - a for a, b in zip(fires, fires[1:])]
    out_gaps = [b - a for a, b in zip(en_cycles, en_cycles[1:])]
    assert all(g >= TCCD for g in in_gaps), (
        f"stimulus did not pace the reads: op handshakes at {fires} "
        f"(gaps {in_gaps}) -- this window cannot test tCCD placement")
    assert out_gaps == in_gaps, (
        f"rddata_en pulses at {en_cycles} (gaps {out_gaps}) do not track the "
        f"request cadence {fires} (gaps {in_gaps}). Collapsed windows mean the "
        f"2nd+ read's enable fires early and the real PHY captures a zero beat "
        f"(Nexys A7 board read failure, beats_mismatched=32).")
    assert all(c - f == RDEN for f, c in zip(fires, en_cycles)), (
        f"each window must sit at its OWN fire+t_rddata_en={RDEN}: "
        f"fires {fires}, en {en_cycles}")
    dut._log.info("PASS: rddata_en tracks the request cadence -- fires %s, "
                  "en %s (gaps %s)", fires, en_cycles, out_gaps)


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_rd_aligner_backpressure(dut):
    """Multi-outstanding + safe backpressure (MAX_OUTSTANDING=2, set by wrapper).
    Hold op_valid with NO returns: admits must stop at MAX_OUTSTANDING and
    op_ready must DEASSERT (queue full -> command issue would stall). Then return
    the outstanding reads' data: op_ready reasserts as reads retire, and exactly
    the admitted number of words are captured in order (correct association)."""
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_rddata_en_i.value = 0
    # op_* and rd_* are BFM-owned. dfi_rddata_* stays hand-driven: DFI read
    # data has NO ready -- an unconditional strobe per spec, not a handshake.
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    op_src = fub_pulse_producer(dut, "op", dut.dfi_clk, log=dut._log,
                                valid="op_valid_i", ready="op_ready_o")
    fub_consumer(dut, "rd", dut.dfi_clk, log=dut._log,
                 valid="rd_valid_o", ready="rd_ready_i",
                 fields={'data': ("rd_data_o", DFI_DW),
                         'resp': ("rd_resp_o", 2),
                         'last': ("rd_last_o", 1)})
    obs = _CycleObs(dut)
    cocotb.start_soon(obs.run())
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    assert BL_WORDS == 1, f"backpressure case targets BL_WORDS=1; got {BL_WORDS}"
    MAXO = 2                                   # must match the wrapper param
    dut.t_rddata_en_i.value = 4

    # Phase 1: hold op_valid, no data returns. op_ready MUST deassert (queue
    # fills at MAX_OUTSTANDING) — that's the backpressure to command issue.
    # Queue more than the aligner can hold: the BFM keeps valid asserted
    # while it has work and ready is low, which IS the sustained-op_valid
    # condition -- and is what a real producer does.
    for _ in range(MAXO + 8):
        await op_src._driver_send(op_src.create_packet(req=1))
    ready_hist = []
    for _ in range(MAXO + 4):
        await RisingEdge(dut.dfi_clk)
        ready_hist.append(int(dut.op_ready_o.value))
    assert 0 in ready_hist, \
        f"op_ready never deasserted under sustained op_valid: {ready_hist}"
    assert int(dut.op_ready_o.value) == 0, "op_ready must be low while queue full"
    # bounded: once full it stays full (no returns) — no spurious re-admits.
    assert ready_hist[-1] == 0 and ready_hist[-2] == 0, \
        f"op_ready should stay low with no returns: {ready_hist}"

    # Phase 2: return the outstanding reads' data; ready reasserts, all captured.
    words = [0xA5A03F18A5A03F1C, 0x0BADC0DE0BADC0DE]
    got = []
    for w in words:
        dut.dfi_rddata_i.value = w
        dut.dfi_rddata_valid_i.value = (1 << DFI_RATE) - 1
        await RisingEdge(dut.dfi_clk)
        if int(dut.rd_valid_o.value) and int(dut.rd_ready_i.value):
            got.append(int(dut.rd_data_o.value))
    dut.dfi_rddata_valid_i.value = 0
    await RisingEdge(dut.dfi_clk)

    assert got == words, f"captured {[hex(x) for x in got]} != {[hex(x) for x in words]}"
    assert int(dut.op_ready_o.value) == 1, "op_ready must reassert after reads retire"
    dut._log.info("PASS: backpressure at MAX_OUTSTANDING, in-order multi-outstanding capture")


def _run_fub(testcase: str, bl_words: int, max_outstanding: int = 8):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_rd_aligner"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DFI_DATA_WIDTH": str(DFI_DW), "DFI_RATE": str(DFI_RATE),
              "BL_WORDS": str(bl_words), "MAX_OUTSTANDING": str(max_outstanding)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000)))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")


def test_pumice_dfi_rd_aligner(request):
    _run_fub("cocotb_test_pumice_dfi_rd_aligner", bl_words=4)


def test_pumice_dfi_rd_aligner_tccd_paced(request):
    # x16 BL4 (BL_WORDS=1): reads paced at tCCD > DQ occupancy. Reproduces the
    # on-silicon read failure at the FUB level (no PHY model needed).
    _run_fub("cocotb_test_rd_aligner_tccd_paced", bl_words=1)


def test_pumice_dfi_rd_aligner_backpressure(request):
    # Multi-outstanding + op_ready backpressure with a small tracking depth.
    _run_fub("cocotb_test_rd_aligner_backpressure", bl_words=1, max_outstanding=2)
