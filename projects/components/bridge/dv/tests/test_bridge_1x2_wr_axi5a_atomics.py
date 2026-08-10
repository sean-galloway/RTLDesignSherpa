#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-3a sign-off test.
#
# Real ATOP values through the fabric:
#   - plain writes and AtomicStore (6'b010000) forward natively — the
#     slave-side boundary shows the SAME awatop at its AW handshake and
#     the write completes OKAY;
#   - AtomicLoad (6'b100000) and AtomicSwap (6'b110000) are swallowed
#     by the master adapter's axi5_atomic_filter: no slave AW handshake,
#     and the master's B response is DECERR (2'b11) with the right ID.

import os
import sys

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.components.bridge.dv.tbclasses.bridge1x2_wr_axi5a_tb import (
    Bridge1x2WrAxi5aTB,
)

ATOP_STORE = 0b010000
ATOP_LOAD = 0b100000
ATOP_SWAP = 0b110000


class AtomicSampler:
    """Capture the slave-side awatop at each ddr AW handshake and every
    master-side B response (id, resp)."""

    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.ddr_aw_atop = []
        self.master_b = []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.ddr_wr_axi_awvalid.value) and int(d.ddr_wr_axi_awready.value):
                self.ddr_aw_atop.append(int(d.ddr_wr_axi_awatop.value))
            if int(d.cpu_wr_axi_bvalid.value) and int(d.cpu_wr_axi_bready.value):
                self.master_b.append((int(d.cpu_wr_axi_bid.value),
                                      int(d.cpu_wr_axi_bresp.value)))


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_wr_axi5a_atomics(dut):
    """Store-class atomics forward natively; read-return classes DECERR
    at the boundary filter without reaching the slave."""
    tb = Bridge1x2WrAxi5aTB(dut)
    await tb.setup_clocks_and_reset()

    sampler = AtomicSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    tb.log.info("=" * 80)
    tb.log.info("A5-3a sign-off: ATOP through the fabric + boundary filter")
    tb.log.info("=" * 80)

    # 1. Plain write (atop=0) forwards.
    dut.cpu_wr_axi_awatop.value = 0
    await tb.master_write(0, 0x0000_0100, 0xA5A5_0001)

    # 2. AtomicStore forwards with the atop value intact.
    dut.cpu_wr_axi_awatop.value = ATOP_STORE
    await tb.master_write(0, 0x0000_0200, 0xA5A5_0002)

    # 3/4. Read-return classes: swallowed + local DECERR. The AXI4 BFM
    # still completes because the filter answers the B channel.
    dut.cpu_wr_axi_awatop.value = ATOP_LOAD
    await tb.master_write(0, 0x0000_0300, 0xA5A5_0003)
    dut.cpu_wr_axi_awatop.value = ATOP_SWAP
    await tb.master_write(0, 0x0000_0400, 0xA5A5_0004)

    # 5. Plain write after the swallows still forwards and completes.
    dut.cpu_wr_axi_awatop.value = 0
    await tb.master_write(0, 0x0000_0500, 0xA5A5_0005)

    await ClockCycles(tb.clock, 50)

    # Slave saw exactly the three forwarded AWs, with atop intact.
    assert sampler.ddr_aw_atop == [0, ATOP_STORE, 0], (
        f"forwarded atop stream wrong: {[bin(x) for x in sampler.ddr_aw_atop]}")

    # Five B responses: writes 1/2/5 OKAY, 3/4 DECERR.
    resps = [r for _i, r in sampler.master_b]
    assert len(resps) == 5, f"expected 5 B responses, saw {sampler.master_b}"
    assert resps.count(3) == 2, (
        f"expected exactly 2 DECERRs (read-return atomics): {sampler.master_b}")
    assert resps.count(0) == 3, (
        f"expected 3 OKAYs (plain + store-class): {sampler.master_b}")

    # Forwarded writes actually landed in the slave memory.
    for addr, data in ((0x100, 0xA5A5_0001), (0x200, 0xA5A5_0002),
                      (0x500, 0xA5A5_0005)):
        got = tb.slave_mem_read(0, addr, master_idx=0)
        assert got == data, f"@0x{addr:x}: 0x{got:08x} != 0x{data:08x}"
    # Swallowed writes did NOT land.
    for addr in (0x300, 0x400):
        got = tb.slave_mem_read(0, addr, master_idx=0)
        assert (got >> 16) != 0xA5A5, (
            f"swallowed atomic leaked into slave mem @0x{addr:x}: 0x{got:08x}")

    tb.log.info("=" * 80)
    tb.log.info("A5-3a atomics test PASSED (3 forwarded / 2 DECERRed)")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================


def test_bridge_1x2_wr_axi5a_atomics(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_wr_axi5a"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_wr_axi5a.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_atomics"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_wr_axi5a_atomics",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
