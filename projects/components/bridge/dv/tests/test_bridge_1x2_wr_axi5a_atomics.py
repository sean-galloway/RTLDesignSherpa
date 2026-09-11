#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-3a sign-off test.
#
# Real ATOP values through the fabric, driven per transaction by the AXI5
# master BFM's atomic_operation (no pin poking since 2026-09-09):
#   - plain writes and AtomicStore (6'b010000) forward natively — the
#     slave-side boundary shows the SAME awatop at its AW handshake and
#     the write completes OKAY;
#   - AtomicLoad (6'b100000), AtomicSwap (6'b110000) and AtomicCompare
#     (6'b110001) are swallowed by the master adapter's axi5_atomic_filter:
#     no slave AW handshake, and the master's B response is DECERR (2'b11)
#     with the right ID. Compare was untested until 2026-09-09.

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

from projects.components.bridge.dv.tbclasses.bridge1x2_wr_axi5a_tb import (
    Bridge1x2WrAxi5aTB,
)

ATOP_STORE = 0b010000
ATOP_LOAD = 0b100000
ATOP_SWAP = 0b110000
ATOP_COMPARE = 0b110001


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


@cocotb.test(timeout_time=2000, timeout_unit="ms")
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

    # Depth (TEST_LEVEL): the six-op sequence (plain, store, load, swap,
    # compare, plain) is repeated `rounds` times on page-separated windows
    # -- gate 1, func 2, full 8 -- so the filter's swallow/answer path is
    # exercised back-to-back across rounds, not once from reset.
    rounds = max(1, tb.level_cfg['sideband_beats'] // 3)
    tb.log.info(f"  level={tb.level}: {rounds} round(s) of 6 ops")
    landed, swallowed = [], []
    for r in range(rounds):
        base = 0x0000_0000 + r * 0x1000
        tag = 0xA5A5_0000 | (r << 8)

        wr = tb.master_wr[0]

        # 1. Plain write (atop=0) forwards.
        r = await wr.write_transaction(base + 0x100, tag | 1, size=2)
        assert r.get('success') and r.get('response') == 0, f"plain write: {r}"

        # 2. AtomicStore forwards with the atop value intact. It is a
        # store-class ADD, and the slave BFM performs it as one (since A5-3b;
        # before that it wrote the operand as a plain write, which is what
        # this test used to expect): memory becomes old + operand.
        store_old = tb.slave_mem_read(0, base + 0x200, master_idx=0)
        r = await wr.atomic_operation(base + 0x200, tag | 2, ATOP_STORE, size=2)
        assert r.get('success') and r.get('response') == 0, f"AtomicStore: {r}"

        # 3/4/5. Read-return classes: swallowed + local DECERR. The filter
        # answers the B channel, so the transaction completes -- with the
        # error response the BFM reports in its result. DECERR IS the
        # expected outcome here, and anything else is a failure.
        for atop, off, idx in ((ATOP_LOAD, 0x300, 3), (ATOP_SWAP, 0x400, 4),
                               (ATOP_COMPARE, 0x600, 6)):
            r = await wr.atomic_operation(base + off, tag | idx, atop, size=2)
            assert r.get('response') == 3, (
                f"read-return atomic {atop:#08b} answered resp={r.get('response')} "
                f"({r}); the boundary filter should answer DECERR")

        # 6. Plain write after the swallows still forwards and completes.
        r = await wr.write_transaction(base + 0x500, tag | 5, size=2)
        assert r.get('success') and r.get('response') == 0, f"plain write after swallows: {r}"

        landed += [(base + 0x100, tag | 1),
                   (base + 0x200, (store_old + (tag | 2)) & 0xFFFF_FFFF),
                   (base + 0x500, tag | 5)]
        swallowed += [base + 0x300, base + 0x400, base + 0x600]

    await ClockCycles(tb.clock, 50)

    # Slave saw exactly the three forwarded AWs per round, with atop intact.
    assert sampler.ddr_aw_atop == [0, ATOP_STORE, 0] * rounds, (
        f"forwarded atop stream wrong: {[bin(x) for x in sampler.ddr_aw_atop]}")

    # Six B responses per round: writes 1/2/6 OKAY, 3/4/5 DECERR.
    resps = [r for _i, r in sampler.master_b]
    assert len(resps) == 6 * rounds, f"expected {6 * rounds} B responses, saw {sampler.master_b}"
    assert resps.count(3) == 3 * rounds, (
        f"expected exactly {3 * rounds} DECERRs (read-return atomics): {sampler.master_b}")
    assert resps.count(0) == 3 * rounds, (
        f"expected {3 * rounds} OKAYs (plain + store-class): {sampler.master_b}")

    # Forwarded writes actually landed in the slave memory.
    for addr, data in landed:
        got = tb.slave_mem_read(0, addr, master_idx=0)
        assert got == data, f"@0x{addr:x}: 0x{got:08x} != 0x{data:08x}"
    # Swallowed writes did NOT land.
    for addr in swallowed:
        got = tb.slave_mem_read(0, addr, master_idx=0)
        assert (got >> 16) != 0xA5A5, (
            f"swallowed atomic leaked into slave mem @0x{addr:x}: 0x{got:08x}")

    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info(f"A5-3a atomics test PASSED ({3 * rounds} forwarded / {3 * rounds} DECERRed)")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_wr_axi5a_atomics(request, test_level):
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
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_atomics_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_1x2_wr_axi5a_atomics",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
