#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): PWAKEUP on an APB5 slave port (IHI 0024E
# 3.7.2, GitHub #102 item 7).
#
# The bridge is the APB5 REQUESTER on periph5, so it DRIVES PWAKEUP (the
# port used to take it as an input). axi4_to_apb5_shim drives it from a flop
# of PSEL. Checked on every cycle of real AXI traffic into the port:
#   - PWAKEUP is high in every Access phase (PSEL & PENABLE) up to and
#     including the PREADY cycle -- 3.7.2: once PWAKEUP and PSEL are high
#     together it must stay high until PREADY, and a Completer that waits
#     for PWAKEUP before PREADY must never be left waiting;
#   - PWAKEUP is low once the port is idle (recommended);
#   - the data round-trips.
# PWAKEUP is a level signal the test only OBSERVES; traffic is BFM-driven.
# Depth (TEST_LEVEL): sideband_beats write+read pairs.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge, ReadOnly
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge1x2_rw_apb5_tb import Bridge1x2RwApb5TB

PERIPH5_BASE = 0x8000_0000


class PwakeupChecker:
    def __init__(self, dut, clock):
        self.dut, self.clock = dut, clock
        self.access_cycles = 0
        self.violations = []

    async def run(self):
        d = self.dut
        cyc = 0
        while True:
            await RisingEdge(self.clock)
            await ReadOnly()
            cyc += 1
            if int(d.periph5_PSEL.value) and int(d.periph5_PENABLE.value):
                self.access_cycles += 1
                if not int(d.periph5_PWAKEUP.value):
                    self.violations.append(cyc)


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rw_apb5_pwakeup(dut):
    """The bridge drives PWAKEUP as the APB5 requester."""
    tb = Bridge1x2RwApb5TB(dut)
    await tb.setup_clocks_and_reset()
    chk = PwakeupChecker(dut, tb.clock)
    cocotb.start_soon(chk.run())
    n = max(4, tb.level_cfg['sideband_beats'])

    await ClockCycles(tb.clock, 10)
    await ReadOnly()
    assert int(dut.periph5_PWAKEUP.value) == 0, "PWAKEUP high on an idle APB5 port"
    await RisingEdge(tb.clock)

    for i in range(n):
        addr = PERIPH5_BASE + 0x40 + 4 * i
        data = 0x9A00_0000 | i
        await tb.master_write(0, addr, data)
        got = await tb.master_read(0, addr)
        assert got == data, f"APB5 round trip @0x{addr:08x}: 0x{got:08x} != 0x{data:08x}"

    await ClockCycles(tb.clock, 20)
    await ReadOnly()
    assert chk.access_cycles >= 2 * n, f"only {chk.access_cycles} APB access cycles seen"
    assert not chk.violations, (
        f"PWAKEUP low in {len(chk.violations)} Access-phase cycle(s), first {chk.violations[:5]}")
    assert int(dut.periph5_PWAKEUP.value) == 0, "PWAKEUP still high after the port went idle"
    tb.log.info(f"APB5 PWAKEUP PASSED: high on all {chk.access_cycles} access cycles, low when idle")


# ============================================================================
# Pytest wrapper
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rw_apb5_pwakeup(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rw_apb5"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_1x2_rw_apb5.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_pwakeup_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rw_apb5_pwakeup",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
