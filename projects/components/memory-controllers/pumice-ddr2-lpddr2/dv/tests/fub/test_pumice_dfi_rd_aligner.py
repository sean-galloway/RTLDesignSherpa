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

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_dfi_rd_aligner.f")

DFI_DW = 128
DFI_RATE = 2
# BL_WORDS is env-overridable so a wrapper can exercise the x16 BL4 case
# (BL_WORDS=1), where tCCD (2) > DQ-bus occupancy (1) leaves a read-command
# bubble the contiguous-window aligner must honor. Default 4 = legacy.
BL_WORDS = int(os.environ.get("BL_WORDS", "4"))


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_pumice_dfi_rd_aligner(dut):
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_rddata_en_i.value = 0
    dut.rd_fire_i.value = 0
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.rd_ready_i.value = 1
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    for RDEN in (0, 2, 4):
        await _run(dut, RDEN)
    dut._log.info("PASS: rddata_en window + bubble-free capture at t_rddata_en in {0,2,4}")


async def _run(dut, RDEN):
    dut.t_rddata_en_i.value = RDEN
    rng = random.Random(0xEE ^ RDEN)
    words = [rng.randrange(1 << DFI_DW) for _ in range(BL_WORDS)]

    # 1) fire; measure rddata_en window (idx 0 = fire cycle)
    en_idx = []
    dut.rd_fire_i.value = 1
    await RisingEdge(dut.dfi_clk)
    dut.rd_fire_i.value = 0
    if int(dut.dfi_rddata_en_o.value) != 0:
        en_idx.append(0)
    for i in range(1, RDEN + BL_WORDS + 6):
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_rddata_en_o.value) != 0:
            en_idx.append(i)
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
    dut.rd_fire_i.value = 0
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.rd_ready_i.value = 1
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    assert BL_WORDS == 1, f"tCCD-bubble case needs BL_WORDS=1 (x16 BL4); got {BL_WORDS}"
    RDEN, TCCD, NREADS = 4, 2, 3
    dut.t_rddata_en_i.value = RDEN
    fire_cycles = [i * TCCD for i in range(NREADS)]   # 0, 2, 4 — tCCD-paced
    en_cycles = []
    horizon = fire_cycles[-1] + RDEN + BL_WORDS + 6
    for c in range(horizon):
        dut.rd_fire_i.value = 1 if c in fire_cycles else 0
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_rddata_en_o.value) != 0:
            en_cycles.append(c)
    dut.rd_fire_i.value = 0

    assert len(en_cycles) == NREADS, \
        f"expected {NREADS} rddata_en pulses, got {en_cycles}"
    gaps = [b - a for a, b in zip(en_cycles, en_cycles[1:])]
    assert all(g == TCCD for g in gaps), (
        f"rddata_en pulses at {en_cycles} (gaps {gaps}) — expected tCCD spacing "
        f"{TCCD}. Contiguous (gap 1) windows mean the aligner collapsed the "
        f"tCCD-paced reads: the 2nd+ read's enable fires a cycle early and the "
        f"real PHY captures a zero beat (Nexys A7 board read failure).")
    dut._log.info("PASS: rddata_en follows tCCD read cadence %s (gaps %s)", en_cycles, gaps)


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_rd_aligner_preamble_valid(dut):
    """x16 board reality: the a7ddrphy asserts a PREAMBLE dfi_rddata_valid one
    cycle BEFORE the aligner's enable window (data still 0), then the real
    valid+data one cycle AFTER (ILA reports/ila_read_fixed.csv: en@N,
    spurious valid@N-1 data=0, real valid@N+1). Capturing on raw |valid| grabs
    the zero preamble beat and shifts the whole read stream -> the on-silicon
    2-of-4 device-word corruption. The aligner MUST capture only within its own
    expected data window (keyed on the enable), ignoring the pre-enable preamble.
    EXPECTED TO FAIL until the capture is gated to the enable window."""
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_rddata_en_i.value = 0
    dut.rd_fire_i.value = 0
    dut.dfi_rddata_i.value = 0
    dut.dfi_rddata_valid_i.value = 0
    dut.rd_ready_i.value = 1
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    assert BL_WORDS == 1, f"preamble case targets x16 BL_WORDS=1; got {BL_WORDS}"
    REAL = 0xA5A03F18A5A03F1C
    ALLV = (1 << DFI_RATE) - 1

    # Sweep the single scenario (a7ddrphy preamble valid before the enable window)
    # across the whole timing window: enable latency (RDEN), where the real data
    # lands relative to the enable (data_lat, incl. AT the enable cycle), and how
    # far the preamble leads the enable (pre_off). The aligner must, in EVERY
    # case, ignore the preamble and capture exactly the real word.
    fails = []
    for RDEN in (2, 4, 6):
        for data_lat in (0, 1, 2, 3):        # real data at enable + data_lat
            for pre_off in (1, 2):           # preamble at enable - pre_off
                pre_cycle = RDEN - pre_off
                if pre_cycle < 1:            # preamble must be a distinct pre-enable cycle
                    continue
                # reset per scenario so r_age/r_credit/r_rcnt don't carry over
                dut.dfi_rstn.value = 0
                dut.rd_fire_i.value = 0
                dut.dfi_rddata_valid_i.value = 0
                dut.dfi_rddata_i.value = 0
                for _ in range(3):
                    await RisingEdge(dut.dfi_clk)
                dut.dfi_rstn.value = 1
                dut.t_rddata_en_i.value = RDEN
                for _ in range(2):
                    await RisingEdge(dut.dfi_clk)

                real_cycle = RDEN + data_lat
                got = []
                for c in range(real_cycle + 6):
                    dut.rd_fire_i.value = 1 if c == 0 else 0
                    if c == pre_cycle:                       # PREAMBLE (data=0)
                        dut.dfi_rddata_valid_i.value = ALLV
                        dut.dfi_rddata_i.value = 0
                    elif c == real_cycle:                    # REAL valid + data
                        dut.dfi_rddata_valid_i.value = ALLV
                        dut.dfi_rddata_i.value = REAL
                    else:
                        dut.dfi_rddata_valid_i.value = 0
                        dut.dfi_rddata_i.value = 0
                    await RisingEdge(dut.dfi_clk)
                    if int(dut.rd_valid_o.value) and int(dut.rd_ready_i.value):
                        got.append(int(dut.rd_data_o.value))
                dut.dfi_rddata_valid_i.value = 0
                if got != [REAL]:
                    fails.append(dict(RDEN=RDEN, data_lat=data_lat, pre_off=pre_off,
                                      got=[hex(x) for x in got]))

    assert not fails, (
        "preamble-valid sweep FAILURES (aligner must ignore the pre-enable "
        f"preamble and capture only the real word) -> {fails}")
    dut._log.info("PASS: preamble ignored across RDEN x data_lat x pre_off window")


def _run_fub(testcase: str, bl_words: int):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_rd_aligner"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DFI_DATA_WIDTH": str(DFI_DW), "DFI_RATE": str(DFI_RATE), "BL_WORDS": str(bl_words)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
                 "SEED": str(random.randint(0, 100000))}
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


def test_pumice_dfi_rd_aligner_preamble_valid(request):
    # x16 BL4 (BL_WORDS=1): a7ddrphy preamble rddata_valid before the enable
    # window. Reproduces the on-silicon 2-of-4 device-word corruption at FUB level.
    _run_fub("cocotb_test_rd_aligner_preamble_valid", bl_words=1)
