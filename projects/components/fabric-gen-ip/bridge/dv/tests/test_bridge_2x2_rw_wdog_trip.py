#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): the slave watchdog (GitHub #119 L3).
#
# bridge_2x2_rw_wdog puts axi4_slave_watchdog (TIMEOUT_CYCLES = 64) in front
# of the ddr slave; sram has none. This file checks, in order:
#
#   1. healthy: ddr answering 20 cycles late (under the timeout) is passed
#      through untouched -- OKAY, data correct, ddr_timeout low;
#   2. trip: ddr stops answering with a write and a 4-beat read outstanding
#      from different masters. Both complete with DECERR (the read with all
#      four beats), shortly after the timeout, and ddr_timeout rises;
#   3. isolated: a new write and read to ddr are answered DECERR at once,
#      and the neighbour sram still reads back what was written to it;
#   4. the master ports' protocol checkers saw no violation throughout.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_wdog_tb import Bridge2x2RwWdogTB, AxiResponseError

CPU, DMA = 0, 1
DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
TIMEOUT = 64
DECERR = 3


def cycles_now():
    return int(get_sim_time('ns')) // 10


async def expect_decerr(coro, what):
    try:
        await coro
    except AxiResponseError as e:
        assert e.resp == DECERR, f"{what}: expected DECERR, got resp={e.resp} ({e})"
        return
    raise AssertionError(f"{what}: completed OKAY, expected DECERR")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_wdog_trip(dut):
    tb = Bridge2x2RwWdogTB(dut)
    await tb.setup_clocks_and_reset()

    # 1. Healthy, slow but alive.
    tb.set_slave_response_delay(DDR, 20)
    await tb.master_write(CPU, DDR_BASE + 0x40, 0x1234_5678)
    got = await tb.master_read(DMA, DDR_BASE + 0x40)
    assert got == 0x1234_5678, f"healthy read 0x{got:08X}"
    await ClockCycles(dut.aclk, 2 * TIMEOUT)
    assert int(dut.ddr_timeout.value) == 0, "watchdog tripped on a slow but live slave"
    tb.log.info("healthy: 20-cycle-late slave passed through, no trip")

    # 2. Hang ddr with a write and a 4-beat read outstanding.
    tb.set_slave_response_delay(DDR, 1_000_000)
    t0 = cycles_now()
    done = {}

    async def hung_write():
        await expect_decerr(tb.master_write(CPU, DDR_BASE + 0x80, 0xCAFE_0001), "hung write")
        done['w'] = cycles_now()

    async def hung_read():
        rd = tb.master_rd[DMA]
        try:
            await rd.read_transaction(DDR_BASE + 0x100, burst_len=4, id=3, size=2)
        except RuntimeError as e:
            assert 'DECERR' in str(e), f"hung read: {e}"
            done['r'] = cycles_now()
            return
        raise AssertionError("hung read: completed OKAY, expected DECERR")

    w = cocotb.start_soon(hung_write())
    r = cocotb.start_soon(hung_read())
    for _ in range(40):
        if 'w' in done and 'r' in done:
            break
        await ClockCycles(dut.aclk, 25)
    assert 'w' in done and 'r' in done, f"outstanding transactions not answered: {done}"
    assert int(dut.ddr_timeout.value) == 1, "ddr_timeout did not rise"
    lat_w, lat_r = done['w'] - t0, done['r'] - t0
    tb.log.info(f"trip: write answered DECERR after {lat_w} cycles, read after {lat_r}")
    assert TIMEOUT <= max(lat_w, lat_r) <= TIMEOUT + 60, \
        f"DECERR came {lat_w}/{lat_r} cycles after issue, timeout is {TIMEOUT}"

    # 3. Isolated: new requests answered at once; sram unaffected.
    t1 = cycles_now()
    await expect_decerr(tb.master_write(DMA, DDR_BASE + 0x200, 0xBEEF), "write after trip")
    await expect_decerr(tb.master_read(CPU, DDR_BASE + 0x200), "read after trip")
    assert cycles_now() - t1 < TIMEOUT, "an isolated slave should be answered without a timeout"
    await tb.master_write(CPU, SRAM_BASE + 0x40, 0x5A5A_A5A5)
    got = await tb.master_read(DMA, SRAM_BASE + 0x40)
    assert got == 0x5A5A_A5A5, f"sram read 0x{got:08X} beside a tripped ddr"
    assert int(dut.ddr_timeout.value) == 1, "ddr_timeout must stay set until reset"

    tb.assert_compliance()
    tb.log.info("GitHub #119 L3 slave watchdog PASSED")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_wdog_trip(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_wdog"
    # With the protocol checkers bound (GitHub #119 L3): the slave ports are
    # checked across the trip too.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}_checkers.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_trip_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_rw_wdog_trip",
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
