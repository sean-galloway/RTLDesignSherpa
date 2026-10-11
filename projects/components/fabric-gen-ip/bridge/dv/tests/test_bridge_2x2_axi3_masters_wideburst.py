#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI3 Review Focus 3 width-converted burst.
#
# bridge_2x2_axi3_masters has cpu as a 32-bit AXI3 master and both slaves
# on a 64-bit AXI4 fabric.  This test drives multi-beat INCR bursts from
# the 32-bit master through the 32->64 upsize converter and back, checking
# byte-exact data round-trip across the width boundary.
# Depth (TEST_LEVEL): wideburst_beats scales with level.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_axi3_masters_tb import Bridge2x2Axi3MastersTB

DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_axi3_masters_wideburst(dut):
    tb = Bridge2x2Axi3MastersTB(dut)
    await tb.setup_clocks_and_reset()

    beats = tb.level_cfg.get('wideburst_beats', 8)
    tb.log.info("=" * 80)
    tb.log.info(f"AXI3 32->64 width-converted burst from cpu: {beats} beats "
                f"(level={tb.level})")
    tb.log.info("=" * 80)

    # Master 0 (cpu) is 32-bit AXI3.  The generated TB uses AXI4MasterRead/
    # Write, which does not drive AXI3 WID.  Keep AWID/WID at 0 for every
    # transaction so the default-zero WID matches AWID and the converter's
    # WID-stability assertion stays quiet.
    txn_id = 0

    # Master 0 (cpu) is 32-bit.  Build a burst of 32-bit words, write to a
    # 64-bit slave, read back, and compare byte-for-byte.
    for slave_idx, base in ((0, DDR_BASE), (1, SRAM_BASE)):
        addr = base + 0x400
        data = [(0xC0FF0000 | (slave_idx << 16) | (i & 0xFFFF)) for i in range(beats)]

        tb.log.info(f"  slave {slave_idx}: write {beats}-beat INCR @0x{addr:08x}")
        wr = await tb.master_wr[0].write_transaction(
            addr, data, size=tb._natural_arsize(0), id=txn_id)
        assert wr.get('success'), f"slave {slave_idx} write failed: {wr}"
        assert wr.get('response') == 0, f"slave {slave_idx} non-OKAY: {wr.get('response')}"

        tb.log.info(f"  slave {slave_idx}: read {beats}-beat INCR @0x{addr:08x}")
        rd = await tb.master_rd[0].read_transaction(
            addr, burst_len=beats, size=tb._natural_arsize(0), id=txn_id)
        assert len(rd) == beats, f"slave {slave_idx}: expected {beats} beats, got {len(rd)}"
        for i, (got, exp) in enumerate(zip(rd, data)):
            assert got == exp, (
                f"slave {slave_idx} beat {i}: got 0x{got:08x}, expected 0x{exp:08x}")

    await ClockCycles(tb.clock, 20)
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI3 32->64 width-converted burst test PASSED")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_axi3_masters_wideburst(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_axi3_masters"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_wideburst_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_axi3_masters_wideburst",
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
