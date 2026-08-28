# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_dfi_wr_serializer`.

Proves the mechanical, bubble-free write drive: wr_fire -> (t_phy_wrlat cycles)
-> dfi_wrdata_en asserts and the burst streams ONE word per cycle with NO gaps
until `last`; data matches the FIFO, mask = ~strb.
"""

import os
import sys
import random
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_producer      # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_dfi_wr_serializer.f")

DFI_DW = 128
DFI_RATE = 2
DFI_SW = DFI_DW // 8
WRLAT = 3


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_pumice_dfi_wr_serializer(dut):
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_phy_wrlat_i.value = 0
    dut.wr_fire_i.value = 0
    # wd_* is BFM-owned. wr_fire_i above is NOT a handshake -- it is the
    # per-cycle fire strobe from the command path, no ready -- so it stays.
    wd_bfm = fub_producer(dut, "wd", dut.dfi_clk, log=dut._log,
                          valid="wd_valid_i", ready="wd_ready_o",
                          fields={'data': ("wd_data_i", DFI_DW),
                                  'strb': ("wd_strb_i", DFI_SW),
                                  'last': ("wd_last_i", 1)})
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    # sweep t_phy_wrlat incl. 0 (a7ddrphy pre-pull board case) and 1
    for wrlat in (0, 1, 3, 5):
        await _run_burst(dut, wd_bfm, wrlat)
    dut._log.info("PASS: bubble-free burst at t_phy_wrlat in {0,1,3,5}")


async def _run_burst(dut, wd_bfm, WRLAT):
    dut.t_phy_wrlat_i.value = WRLAT
    rng = random.Random((int(os.environ.get("SEED", "1")) << 4) ^ WRLAT)
    BL_WORDS = 4
    burst = [rng.randrange(1 << DFI_DW) for _ in range(BL_WORDS)]
    strb = (1 << DFI_SW) - 1     # full-write

    # FIFO source: always-valid, present head; advance on wd_ready. Runs in one
    # coroutine so latency counting is race-free.

    # The BFM IS the "always-valid FIFO source" this used to hand-roll: at
    # backtoback it presents the head continuously and advances on
    # wd_ready_o, holding valid until accepted. Queue the burst once and
    # let it stream; the latency accounting below is unchanged because the
    # presentation semantics are identical.
    async def _stream_burst():
        # QUEUE-AND-GO, not await-each. `send()` blocks until its packet is
        # accepted, so awaiting per beat leaves a gap between beats -- the
        # old hand-rolled present() re-presented the head EVERY cycle, i.e.
        # always-valid. `_driver_send` appends to the transmit queue and
        # returns, so the master's pipeline drives them back-to-back.
        n_b = len(burst)
        for i, d in enumerate(burst):
            await wd_bfm._driver_send(wd_bfm.create_packet(
                data=d, strb=strb, last=1 if i == n_b - 1 else 0))

    async def step():
        await RisingEdge(dut.dfi_clk)

    # Start the source streaming, then let it settle so valid is presented
    # before the fire pulse -- same precondition the old present() call gave.
    cocotb.start_soon(_stream_burst())
    await RisingEdge(dut.dfi_clk)

    # pulse fire (cycle index 0); sample en/data at each cycle from fire onward.
    samples = []   # (idx, en, data, mask), idx 0 = the fire cycle
    dut.wr_fire_i.value = 1
    await RisingEdge(dut.dfi_clk)
    dut.wr_fire_i.value = 0
    samples.append((0, int(dut.dfi_wrdata_en_o.value), int(dut.dfi_wrdata_o.value),
                    int(dut.dfi_wrdata_mask_o.value)))

    for i in range(1, WRLAT + BL_WORDS + 8):
        await step()
        samples.append((i, int(dut.dfi_wrdata_en_o.value), int(dut.dfi_wrdata_o.value),
                        int(dut.dfi_wrdata_mask_o.value)))

    en_idx = [s[0] for s in samples if s[1] != 0]
    en_words = [(s[2], s[3]) for s in samples if s[1] != 0]
    assert len(en_idx) == BL_WORDS, f"expected {BL_WORDS} en cycles, got {len(en_idx)} at {en_idx}"
    lat = en_idx[0]
    assert lat == WRLAT, f"first wrdata_en at +{lat}, expected t_phy_wrlat={WRLAT}"
    for a, b in zip(en_idx, en_idx[1:]):
        assert b == a + 1, f"BUBBLE: en cycles {en_idx} not contiguous"
    got = [w[0] for w in en_words]
    assert got == burst, f"wrdata mismatch: {[hex(x) for x in got]} != {[hex(x) for x in burst]}"
    for _, mask in en_words:
        assert mask == 0, f"mask should be 0 for full-write, got {mask:#x}"

    dut._log.info(f"PASS: burst of {BL_WORDS} words, en at +{WRLAT} (t_phy_wrlat), "
                  f"{BL_WORDS} contiguous cycles (0 bubbles), data+mask correct")


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_wr_serializer_tccd_paced(dut):
    """x16 BL4 (single-DFI-word bursts) at t_phy_wrlat>0: writes paced at
    tCCD=2, one cycle WIDER than the DQ-bus occupancy (1 word). Each burst's
    wrdata_en/wrdata must land at ITS OWN fire+t_phy_wrlat (tCCD apart), NOT
    collapse into contiguous back-to-back drives. Collapsing drives the 2nd+
    write's data a cycle early -> latent silicon write corruption whenever
    t_phy_wrlat>0 (the pre-pull t_phy_wrlat=0 board config sidesteps it via the
    combinational word0 path, which is why board writes survived). Mirror of the
    rd_aligner tCCD case."""
    cocotb.start_soon(Clock(dut.dfi_clk, 10, units='ns').start())
    dut.dfi_rstn.value = 0
    dut.t_phy_wrlat_i.value = 0
    dut.wr_fire_i.value = 0
    # wd_* is BFM-owned. wr_fire_i above is NOT a handshake -- it is the
    # per-cycle fire strobe from the command path, no ready -- so it stays.
    wd_bfm = fub_producer(dut, "wd", dut.dfi_clk, log=dut._log,
                          valid="wd_valid_i", ready="wd_ready_o",
                          fields={'data': ("wd_data_i", DFI_DW),
                                  'strb': ("wd_strb_i", DFI_SW),
                                  'last': ("wd_last_i", 1)})
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    WRLAT, TCCD, NWR = 3, 2, 3
    dut.t_phy_wrlat_i.value = WRLAT
    strb = (1 << DFI_SW) - 1
    words = [0xA1, 0xB2, 0xC3]             # 3 single-word bursts
    fire_cycles = [i * TCCD for i in range(NWR)]   # 0, 2, 4 — tCCD-paced
    en_cycles = []
    # Each word is its own single-word burst, so every packet carries last=1.
    async def _stream_words():
        for w in words:
            await wd_bfm._driver_send(
                wd_bfm.create_packet(data=w, strb=strb, last=1))
    cocotb.start_soon(_stream_words())
    await RisingEdge(dut.dfi_clk)

    for c in range(fire_cycles[-1] + WRLAT + 8):
        dut.wr_fire_i.value = 1 if c in fire_cycles else 0
        await RisingEdge(dut.dfi_clk)
        if int(dut.dfi_wrdata_en_o.value) != 0:
            en_cycles.append(c)
    dut.wr_fire_i.value = 0

    assert len(en_cycles) == NWR, \
        f"expected {NWR} wrdata_en pulses, got {en_cycles}"
    gaps = [b - a for a, b in zip(en_cycles, en_cycles[1:])]
    assert all(g == TCCD for g in gaps), (
        f"wrdata_en pulses at {en_cycles} (gaps {gaps}) — expected tCCD spacing "
        f"{TCCD}. Contiguous (gap 1) means the serializer collapsed the tCCD-"
        f"paced writes: the 2nd+ write's data drives a cycle early (latent write "
        f"corruption at t_phy_wrlat>0).")
    dut._log.info("PASS: wrdata_en follows tCCD write cadence %s (gaps %s)", en_cycles, gaps)


def _run_wr_fub(testcase: str):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_wr_serializer"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DFI_DATA_WIDTH": str(DFI_DW), "DFI_RATE": str(DFI_RATE)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
                 "SEED": os.environ.get('SEED', str(random.randint(0, 100000)))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")


def test_pumice_dfi_wr_serializer(request):
    _run_wr_fub("cocotb_test_pumice_dfi_wr_serializer")


def test_pumice_dfi_wr_serializer_tccd_paced(request):
    # x16 BL4 single-word bursts paced at tCCD > DQ occupancy, t_phy_wrlat>0.
    # Reproduces the latent write-serializer cadence bug at the FUB level.
    _run_wr_fub("cocotb_test_wr_serializer_tccd_paced")
