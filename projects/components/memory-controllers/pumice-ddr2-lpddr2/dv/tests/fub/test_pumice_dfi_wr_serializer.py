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

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

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
    dut.wd_valid_i.value = 0
    dut.wd_data_i.value = 0
    dut.wd_strb_i.value = 0
    dut.wd_last_i.value = 0
    for _ in range(4):
        await RisingEdge(dut.dfi_clk)
    dut.dfi_rstn.value = 1
    for _ in range(3):
        await RisingEdge(dut.dfi_clk)

    # sweep t_phy_wrlat incl. 0 (a7ddrphy pre-pull board case) and 1
    for wrlat in (0, 1, 3, 5):
        await _run_burst(dut, wrlat)
    dut._log.info("PASS: bubble-free burst at t_phy_wrlat in {0,1,3,5}")


async def _run_burst(dut, WRLAT):
    dut.t_phy_wrlat_i.value = WRLAT
    rng = random.Random((int(os.environ.get("SEED", "1")) << 4) ^ WRLAT)
    BL_WORDS = 4
    burst = [rng.randrange(1 << DFI_DW) for _ in range(BL_WORDS)]
    strb = (1 << DFI_SW) - 1     # full-write

    # FIFO source: always-valid, present head; advance on wd_ready. Runs in one
    # coroutine so latency counting is race-free.
    q = deque(burst)

    def present():
        if q:
            dut.wd_data_i.value = q[0]
            dut.wd_strb_i.value = strb
            dut.wd_last_i.value = 1 if len(q) == 1 else 0
            dut.wd_valid_i.value = 1
        else:
            dut.wd_valid_i.value = 0

    async def step():
        # advance one clock, then pop if the DUT accepted a word
        present()
        await RisingEdge(dut.dfi_clk)
        if q and int(dut.wd_valid_i.value) and int(dut.wd_ready_o.value):
            q.popleft()

    # pulse fire (cycle index 0); sample en/data at each cycle from fire onward.
    samples = []   # (idx, en, data, mask), idx 0 = the fire cycle
    present()
    dut.wr_fire_i.value = 1
    await RisingEdge(dut.dfi_clk)
    dut.wr_fire_i.value = 0
    samples.append((0, int(dut.dfi_wrdata_en_o.value), int(dut.dfi_wrdata_o.value),
                    int(dut.dfi_wrdata_mask_o.value)))
    if q and int(dut.wd_ready_o.value):     # wrlat==0 drives on the fire cycle
        q.popleft()

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


def test_pumice_dfi_wr_serializer(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_wr_serializer"
    test_name = "cocotb_test_pumice_dfi_wr_serializer"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DFI_DATA_WIDTH": str(DFI_DW), "DFI_RATE": str(DFI_RATE)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "SEED": str(random.randint(0, 100000))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_dfi_wr_serializer",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")
