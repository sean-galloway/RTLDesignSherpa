#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI3 Review Focus 1/4 positive contract.
#
# bridge_1x2_axi3 has a single AXI3 master port. AXI3 permits up to 16
# outstanding transactions and requires same-ID ordering. This test checks:
#   - four same-ID ARs return their R data in the order they were issued;
#   - two IDs' write bursts complete with correct per-ID data;
#   - the bridge_id FIFO does not misroute or interleave responses.
# Depth (TEST_LEVEL): outstanding_count reads and write ids scale with level.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge1x2_axi3_tb import Bridge1x2Axi3TB

S0_BASE, S1_BASE = 0x0000_0000, 0x8000_0000


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_axi3_multioutstanding(dut):
    tb = Bridge1x2Axi3TB(dut)
    await tb.setup_clocks_and_reset()

    n_reads = tb.level_cfg.get('outstanding_count', 4)
    n_write_ids = tb.level_cfg.get('write_id_count', 2)
    tb.log.info("=" * 80)
    tb.log.info(f"AXI3 multi-outstanding ordering: {n_reads} same-ID reads, "
                f"{n_write_ids} write IDs (level={tb.level})")
    tb.log.info("=" * 80)

    # The generated TB's AXI4MasterWrite does not drive AXI3 WID.  Drive WID
    # directly from the test so it matches AWID during each write burst; the
    # AXI4 BFM then handles the rest of the write channel correctly.
    cpu_wid = dut.cpu_axi_wid

    # ---- Phase 1: same-ID outstanding reads, order preserved ----------------
    read_id = 3
    read_results = [None] * n_reads
    read_order = []

    async def _rd(i, addr):
        resp = await tb.master_rd[0].read_transaction(
            addr, burst_len=1, size=tb._natural_arsize(0), id=read_id)
        read_results[i] = resp[0]
        read_order.append(i)

    rd_tasks = []
    for i in range(n_reads):
        addr = S0_BASE + 0x200 + i * 8
        rd_tasks.append(cocotb.start_soon(_rd(i, addr)))
    for t in rd_tasks:
        await t

    assert len(read_order) == n_reads, f"only {len(read_order)}/{n_reads} reads completed"
    assert read_order == list(range(n_reads)), (
        f"same-ID read completion order violated: {read_order}")
    for i in range(n_reads):
        addr = S0_BASE + 0x200 + i * 8
        exp = tb.slave_mem_read(0, addr, master_idx=0)
        assert read_results[i] == exp, (
            f"read {i} data mismatch: got 0x{read_results[i]:08x}, "
            f"expected 0x{exp:08x}")
    tb.log.info(f"  same-ID reads: completion order {read_order} OK")

    # ---- Phase 2: multi-ID writes, per-ID data correct, no interleaving -----
    # Use distinct IDs and disjoint addresses; each ID writes a burst.
    # Sequential issue because the AXI3-to-AXI4 write converter serializes
    # outstanding writes to one active burst.
    write_results = {}

    # Master 0 is 64-bit AXI3; build 64-bit data beats and verify them at
    # 8-byte granularity so the data width is respected end-to-end.
    bytes_per_beat = tb.master_data_width[0] // 8

    for wid in range(n_write_ids):
        addr = S1_BASE + 0x1000 + wid * 0x100
        data = [(0xDEAD0000_00000000 | (wid << 40) | (i & 0xFFFF_FFFF)) for i in range(4)]
        cpu_wid.value = wid
        r = await tb.master_wr[0].write_transaction(
            addr, data, size=tb._natural_arsize(0), id=wid)
        write_results[wid] = r

    for wid in range(n_write_ids):
        r = write_results[wid]
        assert r.get('success'), f"write id={wid} failed: {r}"
        assert r.get('response') == 0, f"write id={wid} non-OKAY: {r.get('response')}"
        addr = S1_BASE + 0x1000 + wid * 0x100
        for i in range(4):
            exp = 0xDEAD0000_00000000 | (wid << 40) | (i & 0xFFFF_FFFF)
            got = tb.slave_mem_read(1, addr + i * bytes_per_beat, master_idx=0)
            assert got == exp, (
                f"id={wid} beat {i} data mismatch: got 0x{got:016x}, expected 0x{exp:016x}")
    tb.log.info(f"  multi-ID writes: {n_write_ids} IDs completed OKAY, data verified")

    await ClockCycles(tb.clock, 20)
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI3 multi-outstanding ordering test PASSED")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_axi3_multioutstanding(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_1x2_axi3"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_multioutstanding_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_axi3_multioutstanding",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )
