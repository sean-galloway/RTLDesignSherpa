#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-015 / BRIDGE-016 sign-off test.
#
# Two masters issue reads with IDENTICAL AXI IDs to the same slave at the same
# time, and that slave answers out of order across IDs. Two things have to be
# true for every read to get its own data back:
#   - the fabric's IDs are {master index, master id} (BRIDGE-016), so the two
#     masters' id 3 are different IDs at the slave and the slave-side ARID
#     stream must contain BOTH {0,3} and {1,3};
#   - the slave adapter tracks by that full ID in bridge_cam (enable_ooo,
#     BRIDGE-015), so a beat that comes back early is routed by who owns its
#     ID, not by whose request happened to be oldest.
# Each master checks every returned word against what it wrote there, and the
# AXI4 compliance checker on both master ports is armed throughout.

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

from projects.components.bridge.dv.tbclasses.bridge2x2_ooo_tb import Bridge2x2OooTB

MASTER_ID_W = 4
ID_PREFIX_W = 1
MASK32 = 0xFFFF_FFFF


class SlaveIdSampler:
    """Every ARID / AWID seen at a slave port's handshakes, full width."""

    def __init__(self, dut, clock, prefix):
        self.dut, self.clock, self.prefix = dut, clock, prefix
        self.arid, self.awid = [], []

    async def run(self):
        d, p = self.dut, self.prefix
        while True:
            await RisingEdge(self.clock)
            if int(getattr(d, f"{p}arvalid").value) and int(getattr(d, f"{p}arready").value):
                self.arid.append(int(getattr(d, f"{p}arid").value))
            if int(getattr(d, f"{p}awvalid").value) and int(getattr(d, f"{p}awready").value):
                self.awid.append(int(getattr(d, f"{p}awid").value))


async def _phase(tb, slave_idx, base, n_reads, ids, log):
    """Both masters: seed n words each, then read them all back concurrently
    using the SAME id sequence, through one out-of-order slave."""
    words = {}
    for m in (0, 1):
        for i in range(n_reads):
            a = base + 0x1000 * m + 4 * i
            v = (0x5EED_0000 | (m << 12) | i) & MASK32
            r = await tb.master_wr[m].write_transaction(a, v, size=2, id=ids[i % len(ids)])
            assert r.get('response') == 0, f"seed write m{m} @{a:#x}: {r}"
            words[(m, a)] = v

    async def read(m, a, txn_id):
        # AXI4MasterRead.read_transaction returns the data words; an error
        # response surfaces through the compliance checker and the data check.
        data = await tb.master_rd[m].read_transaction(a, burst_len=1, id=txn_id)
        return m, a, txn_id, data[0]

    # Same IDs, same instant, same slave -- the aliasing case.
    tasks = []
    for i in range(n_reads):
        for m in (0, 1):
            a = base + 0x1000 * m + 4 * i
            tasks.append(cocotb.start_soon(read(m, a, ids[i % len(ids)])))
    results = [await t for t in tasks]
    for m, a, txn_id, data in results:
        assert data == words[(m, a)], (
            f"m{m} read @{a:#x} id {txn_id} got {data:#x}, wrote {words[(m, a)]:#x}: a response "
            f"was delivered to the wrong master or the wrong waiter")
    log.info(f"  slave {slave_idx}: {2 * n_reads} concurrent reads with shared IDs, all data correct")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_ooo_reorder(dut):
    """Shared IDs from two masters through reordering slaves route correctly."""
    tb = Bridge2x2OooTB(dut)
    await tb.setup_clocks_and_reset()

    samplers = {0: SlaveIdSampler(dut, tb.clock, "ddr_axi_"),
                1: SlaveIdSampler(dut, tb.clock, "sram_axi_")}
    for s in samplers.values():
        cocotb.start_soon(s.run())

    n_reads = max(4, tb.level_cfg['arb_per_master'])
    ids = list(range(1 << MASTER_ID_W))      # every master ID, so the prefix is all that differs
    tb.log.info("=" * 80)
    tb.log.info(f"BRIDGE-015/016 sign-off: level={tb.level}, {n_reads} reads per master per slave, "
                f"ids {ids[0]}..{ids[-1]} shared by both masters")
    tb.log.info("=" * 80)

    await _phase(tb, 0, 0x0000_2000, n_reads, ids, tb.log)
    await _phase(tb, 1, 0x8000_2000, n_reads, ids, tb.log)
    await ClockCycles(tb.clock, 50)

    # The prefix is visible at the slave: for every master id both masters
    # used, the slave saw BOTH {0,id} and {1,id}, and nothing else.
    used = {ids[i % len(ids)] for i in range(n_reads)}
    expect = {(m << MASTER_ID_W) | i for m in (0, 1) for i in used}
    for slave_idx, s in samplers.items():
        seen = set(s.arid)
        assert seen == expect, (
            f"slave {slave_idx} ARIDs {sorted(seen)} != expected {sorted(expect)}: the master "
            f"index is not being prepended, or a read never reached this slave")
        assert all((w >> MASTER_ID_W) in (0, 1) for w in s.awid), f"slave {slave_idx} AWID prefix out of range"
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("BRIDGE-015/016 PASSED: out-of-order slaves routed shared-ID reads by master-unique ID")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_ooo_reorder(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_ooo"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_2x2_ooo.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_reorder_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_ooo_reorder",
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
