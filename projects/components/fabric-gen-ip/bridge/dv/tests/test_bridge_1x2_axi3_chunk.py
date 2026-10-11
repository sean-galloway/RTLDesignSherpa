#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI3 Review Focus 2 burst chopping.
#
# The original brief targets the AXI3 slave in bridge_1x2_axi3, but that
# fixture's single master is AXI3 and AXI3 limits bursts to 16 beats.  To
# drive a >16-beat INCR burst we instead use bridge_2x2_axi3_slaves: its
# cpu_axi4 master is AXI4 and its ddr_axi3/sram_axi3 slaves cross
# axi4_to_axi3 in the slave adapter.  A 32-beat AXI4 transaction is chopped
# into two 16-beat AXI3 bursts; the converter must merge the two slave
# responses into exactly one B with OKAY and return all 32 beats of data.
# Depth (TEST_LEVEL): chunk_beats scales with level but is always >16.

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

from bridge2x2_axi3_slaves_tb import Bridge2x2Axi3SlavesTB

DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_axi3_chunk(dut):
    tb = Bridge2x2Axi3SlavesTB(dut)
    await tb.setup_clocks_and_reset()

    beats = max(17, tb.level_cfg.get('chunk_beats', 32))
    tb.log.info("=" * 80)
    tb.log.info(f"AXI3 burst chopping: {beats}-beat INCR to AXI3 slave "
                f"(level={tb.level})")
    tb.log.info("=" * 80)

    for slave_idx, base in ((0, DDR_BASE), (1, SRAM_BASE)):
        addr = base + 0x800
        data = [(0xCAFE0000 | (slave_idx << 16) | (i & 0xFFFF)) for i in range(beats)]

        tb.log.info(f"  slave {slave_idx}: write {beats}-beat INCR @0x{addr:08x}")
        wr = await tb.master_wr[0].write_transaction(
            addr, data, size=tb._natural_arsize(0), id=slave_idx)
        assert wr.get('success'), f"slave {slave_idx} write failed: {wr}"
        assert wr.get('response') == 0, (
            f"slave {slave_idx}: expected OKAY, got response={wr.get('response')}")
        tb.log.info(f"  slave {slave_idx}: exactly one B returned OKAY")

        tb.log.info(f"  slave {slave_idx}: read {beats}-beat INCR @0x{addr:08x}")
        rd = await tb.master_rd[0].read_transaction(
            addr, burst_len=beats, size=tb._natural_arsize(0), id=slave_idx)
        assert len(rd) == beats, f"slave {slave_idx}: expected {beats} beats, got {len(rd)}"
        for i, (got, exp) in enumerate(zip(rd, data)):
            assert got == exp, (
                f"slave {slave_idx} beat {i}: got 0x{got:016x}, expected 0x{exp:016x}")

        # Byte-exact check via the slave memory model as well.
        for i in range(beats):
            exp = data[i]
            got = tb.slave_mem_read(slave_idx, addr + i * 8, master_idx=0)
            assert got == exp, (
                f"slave {slave_idx} memory beat {i}: got 0x{got:016x}, expected 0x{exp:016x}")

    await ClockCycles(tb.clock, 20)
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI3 burst-chopping chunk test PASSED")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_axi3_chunk(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    # Fixture adaptation: the test file name follows the brief, but the DUT
    # under test is bridge_2x2_axi3_slaves because it provides an AXI4 master
    # that can legally issue >16-beat bursts toward AXI3 slaves.
    dut_name = "bridge_2x2_axi3_slaves"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_bridge_1x2_axi3_chunk_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_1x2_axi3_chunk",
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
