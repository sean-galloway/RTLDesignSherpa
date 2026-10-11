#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI3 Review Focus 5 lock pass-through.
#
# bridge_1x2_axi3 has a 2-bit AxLOCK AXI3 master port.  The generated TB
# uses AXI4MasterRead/Write which can only drive a 1-bit lock field, so
# this test instantiates AXI3MasterRead/Write on the same cpu_axi_ prefix
# for the lock transactions.  It drives AxLOCK=2'b10 (locked access per
# AXI3 encoding; the brief calls this the exclusive/lock pass-through
# case) and asserts the response is OKAY with no fabricated lock semantics.
# Depth (TEST_LEVEL): fixed single address, so level only affects repeats.

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

from CocoTBFramework.components.axi3.axi3_interfaces import (
    AXI3MasterRead, AXI3MasterWrite
)
from bridge1x2_axi3_tb import Bridge1x2Axi3TB

S0_BASE = 0x0000_0000
AXI3_LOCKED = 2  # 2'b10 on the AXI3 2-bit AxLOCK field


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_axi3_lock(dut):
    tb = Bridge1x2Axi3TB(dut)
    await tb.setup_clocks_and_reset()

    repeats = tb.level_cfg.get('lock_repeats', 1)
    tb.log.info("=" * 80)
    tb.log.info(f"AXI3 AxLOCK pass-through: {repeats} locked read+write pair(s) "
                f"(level={tb.level})")
    tb.log.info("=" * 80)

    # AXI3 BFMs that can drive the 2-bit lock field.
    axi3_rd = AXI3MasterRead(
        dut, tb.clock, prefix="cpu_axi_", log=tb.log,
        data_width=64, addr_width=32, id_width=4, user_width=1, multi_sig=True)
    axi3_wr = AXI3MasterWrite(
        dut, tb.clock, prefix="cpu_axi_", log=tb.log,
        data_width=64, addr_width=32, id_width=4, user_width=1, multi_sig=True)

    for i in range(repeats):
        addr = S0_BASE + 0x1000 + i * 0x100
        write_data = 0xA5A5_B5B5_C5C5_D5D5 + i

        # Locked read first.
        rd = await axi3_rd.read_transaction(
            addr, burst_len=1, size=3, id=0, lock=AXI3_LOCKED)
        assert len(rd) == 1, f"locked read {i} returned {len(rd)} beats"
        tb.log.info(f"  locked read {i} @0x{addr:08x} returned 0x{rd[0]:016x} OKAY")

        # Locked write to the same address.
        wr = await axi3_wr.write_transaction(
            addr, write_data, burst_len=1, size=3, id=0, lock=AXI3_LOCKED)
        assert wr.get('success'), f"locked write {i} failed: {wr}"
        assert wr.get('response') == 0, (
            f"locked write {i}: expected OKAY, got {wr.get('response')}")
        tb.log.info(f"  locked write {i} @0x{addr:08x} returned OKAY")

    await ClockCycles(tb.clock, 20)
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI3 AxLOCK pass-through test PASSED")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_axi3_lock(request, test_level):
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
    test_name_plus_params = f"test_{dut_name}_lock_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_1x2_axi3_lock",
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
