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
BL_WORDS = 4


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

def test_pumice_dfi_rd_aligner(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_rd_aligner"
    test_name = "cocotb_test_pumice_dfi_rd_aligner"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DFI_DATA_WIDTH": str(DFI_DW), "DFI_RATE": str(DFI_RATE), "BL_WORDS": str(BL_WORDS)}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                 "SEED": str(random.randint(0, 100000))}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_dfi_rd_aligner",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET"], waves=False, keep_files=True, timescale="1ns/1ps")
