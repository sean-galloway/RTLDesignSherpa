#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI5 sideband THROUGH THE ARBITER.
#
# bridge_2x2_axi5 is the first multi-master AXI5 fixture. Both masters are
# AXI5 with nsaid/trace/unique; the AXI5 BFMs drive the sideband per
# transaction (no pin poking), both masters hit the AXI5 slave concurrently,
# and the slave-side AW/AR sideband is sampled at every handshake:
#   - every sampled NSAID belongs to the master that issued it (cpu 0xA,
#     dma 0x5) and each master's count matches what it issued -- a sideband
#     mux that picked the wrong master's value under contention would show
#     a foreign NSAID or a miscount;
#   - trace echoes back on every B and R from the AXI5 slave (the AXI5 slave
#     BFM returns trace=aw/ar trace), and returns 0 from the AXI4 slave;
#   - every write reads back, per master, and the AXI5 compliance checkers
#     on both master ports report zero violations.
# Depth (TEST_LEVEL): arb_per_master transactions per master and phase.

import os
import sys
import random
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.components.bridge.dv.tbclasses.bridge2x2_axi5_tb import Bridge2x2Axi5TB

NSAID = {0: 0xA, 1: 0x5}          # per master; distinct so a swap is visible
SRAM_BASE, DDR_BASE = 0x8000_0000, 0x0000_0000


class SramSidebandSampler:
    """AW/AR sideband at every sram (AXI5 slave) handshake."""

    def __init__(self, dut, clock):
        self.dut, self.clock = dut, clock
        self.aw, self.ar = [], []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.sram_axi_awvalid.value) and int(d.sram_axi_awready.value):
                self.aw.append((int(d.sram_axi_awnsaid.value), int(d.sram_axi_awtrace.value),
                                int(d.sram_axi_awunique.value)))
            if int(d.sram_axi_arvalid.value) and int(d.sram_axi_arready.value):
                self.ar.append((int(d.sram_axi_arnsaid.value), int(d.sram_axi_artrace.value),
                                int(d.sram_axi_arunique.value)))


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_axi5_sideband_arb(dut):
    """Concurrent AXI5 sideband from two masters through the arbiter."""
    tb = Bridge2x2Axi5TB(dut)
    await tb.setup_clocks_and_reset()
    sampler = SramSidebandSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    n = tb.level_cfg['arb_per_master']
    tb.log.info("=" * 80)
    tb.log.info(f"AXI5 sideband through arbitration: {n} txn/master/phase (level={tb.level})")
    tb.log.info("=" * 80)

    # Slow the AXI5 slave so the two masters genuinely contend at the arbiter.
    tb.set_slave_response_delay(1, 24)

    # ---- phase 1: concurrent writes to the AXI5 slave, per-master sideband
    plan = {0: [], 1: []}
    for m in (0, 1):
        for i in range(n):
            addr = SRAM_BASE + (m * 0x1000) + i * 4 + tb.rng.randrange(0, 0x400, 0x100)
            plan[m].append((addr, 0x5B00_0000 | (m << 20) | (i & 0xFFFF)))
    b_trace = {0: [], 1: []}
    done = []

    async def _w(m, addr, data, i):
        r = await tb.master_wr[m].write_transaction(
            addr, data, size=2, id=(m << 3) | (i % 8),
            nsaid=NSAID[m], trace=1, unique=1)
        assert r.get('success'), f"master {m} write @0x{addr:08x} failed: {r}"
        b_trace[m].append(r.get('trace', 0))
        done.append(m)

    for m in (0, 1):
        for i, (addr, data) in enumerate(plan[m]):
            cocotb.start_soon(_w(m, addr, data, i))
    for _ in range(6000):
        if len(done) == 2 * n:
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == 2 * n, f"writes completed {len(done)}/{2 * n}"

    aw_nsaid = [x[0] for x in sampler.aw]
    assert set(aw_nsaid) <= set(NSAID.values()), (
        f"foreign NSAID on the slave AW under contention: {sorted(set(aw_nsaid))}")
    for m in (0, 1):
        assert aw_nsaid.count(NSAID[m]) == n, (
            f"master {m}: issued {n} AWs with nsaid={NSAID[m]:#x}, slave saw "
            f"{aw_nsaid.count(NSAID[m])} (all: {aw_nsaid})")
        assert all(t == 1 for t in b_trace[m]), f"master {m}: btrace not echoed: {b_trace[m]}"
    assert all(x[1] == 1 and x[2] == 1 for x in sampler.aw), f"trace/unique lost on AW: {sampler.aw}"
    tb.log.info(f"  AW: {len(sampler.aw)} handshakes, nsaid counts "
                f"cpu={aw_nsaid.count(NSAID[0])} dma={aw_nsaid.count(NSAID[1])}, btrace echoed")

    # ---- phase 2: concurrent reads back, per-master sideband, data checked
    r_trace = {0: [], 1: []}
    rdone = []

    async def _r(m, addr, expect, i):
        resp = await tb.master_rd[m].read_transaction(
            addr, size=2, id=(m << 3) | (i % 8), nsaid=NSAID[m], trace=1, unique=1)
        assert resp[0]['data'] == expect, (
            f"master {m} read @0x{addr:08x}: 0x{resp[0]['data']:08x} != 0x{expect:08x}")
        r_trace[m].append(resp[0].get('trace', 0))
        rdone.append(m)

    for m in (0, 1):
        for i, (addr, data) in enumerate(plan[m]):
            cocotb.start_soon(_r(m, addr, data, i))
    for _ in range(6000):
        if len(rdone) == 2 * n:
            break
        await ClockCycles(tb.clock, 10)
    assert len(rdone) == 2 * n, f"reads completed {len(rdone)}/{2 * n}"
    ar_nsaid = [x[0] for x in sampler.ar]
    assert set(ar_nsaid) <= set(NSAID.values()), f"foreign NSAID on the slave AR: {sorted(set(ar_nsaid))}"
    for m in (0, 1):
        assert ar_nsaid.count(NSAID[m]) == n, (
            f"master {m}: issued {n} ARs with nsaid={NSAID[m]:#x}, slave saw {ar_nsaid.count(NSAID[m])}")
        assert all(t == 1 for t in r_trace[m]), f"master {m}: rtrace not echoed: {r_trace[m]}"
    tb.log.info(f"  AR: {len(sampler.ar)} handshakes, per-master counts hold, rtrace echoed")

    # ---- phase 3: the drop path -- same sideband into the AXI4 slave returns trace=0
    tb.set_slave_response_delay(1, 0)
    for m in (0, 1):
        addr = DDR_BASE + 0x2000 + m * 0x100
        r = await tb.master_wr[m].write_transaction(addr, 0xD0B0_0000 | m, size=2, id=m,
                                                    nsaid=NSAID[m], trace=1, unique=1)
        assert r.get('success') and r.get('trace', 0) == 0, (
            f"master {m}: AXI4 slave path returned trace={r.get('trace')}, expected 0")
        resp = await tb.master_rd[m].read_transaction(addr, size=2, id=m, nsaid=NSAID[m], trace=1)
        assert resp[0]['data'] == (0xD0B0_0000 | m) and resp[0].get('trace', 0) == 0
    tb.log.info("  drop path: AXI4 slave answers with trace=0, data intact")

    await ClockCycles(tb.clock, 20)
    # Phase 3 wrote once per master to the AXI4 slave with trace=1 and got
    # btrace=0 back -- the fabric's documented drop, which the AXI5 checker
    # at each master port counts as one TRACE mismatch (BRIDGE-012). Exactly
    # one per master is allowed; the native-path phases must stay clean.
    tb.assert_compliance(allow={'trace_consistency_violation': 1})
    tb.log.info("=" * 80)
    tb.log.info(f"AXI5 sideband-through-arbitration test PASSED ({4 * n + 4} transactions)")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest wrapper
# ============================================================================


def generate_bridge_levels():
    """REG_LEVEL selects the grid: the test_level cells this wrapper expands to.

    GATE 1 (gate), FUNC 2 (gate, func), FULL 3 (gate, func, full) -- different
    counts, so the three make targets run different matrices. The depth each
    cell runs at is read by the TB from TEST_LEVEL (bridge_levels.PROFILE)."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return ['gate']
    if reg_level == 'FUNC':
        return ['gate', 'func']
    return ['gate', 'func', 'full']


bridge_levels = generate_bridge_levels()


@pytest.mark.parametrize("test_level", bridge_levels)
def test_bridge_2x2_axi5_sideband_arb(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_2x2_axi5"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_2x2_axi5.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_sideband_arb_{test_level}_{reg_level}"
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
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_2x2_axi5_sideband_arb",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
