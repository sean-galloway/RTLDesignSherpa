#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AWAKEUP across the bridge (IHI 0022L A14.1.1,
# GitHub #102 item 5).
#
# bridge_2x2_axi5: cpu (AXI5, 'wakeup') and dma (AXI5, no AWAKEUP) masters,
# sram (AXI5, 'wakeup') and ddr (AXI4) slaves. The bridge's contract:
#   - a master port's AWAKEUP reaches every connected wake-capable slave
#     port ahead of any request, so the slave can wake before AxVALID
#     (the A14.1.1 recommendation);
#   - a slave port's AWAKEUP is high on every cycle it presents AWVALID,
#     WVALID or ARVALID -- including traffic from dma, which has no AWAKEUP
#     (the A14.1.1 "derive from AxVALID" fallback), so a Subordinate that
#     waits for AWAKEUP before AxREADY can never deadlock on the bridge;
#   - AWAKEUP falls again when nothing is requested (recommended);
#   - an AXI4 slave port has no AWAKEUP pin; dma has none either.
# AWAKEUP is a level wake signal, not a valid/ready interface, and the AXI5
# BFMs do not model it, so the test drives cpu_axi_awakeup directly.
# Depth (TEST_LEVEL): arb_per_master transactions per master.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge, ReadOnly, Lock
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_axi5_tb import Bridge2x2Axi5TB

CPU, DMA = 0, 1
SRAM = 1
SRAM_BASE = 0x8000_0000


class SramWakeChecker:
    """Every cycle: if the sram port presents a request, AWAKEUP must be high."""

    def __init__(self, dut, clock):
        self.dut, self.clock = dut, clock
        self.req_cycles = 0
        self.violations = []

    async def run(self):
        d = self.dut
        cyc = 0
        while True:
            await RisingEdge(self.clock)
            await ReadOnly()
            cyc += 1
            req = (int(d.sram_axi_awvalid.value) or int(d.sram_axi_wvalid.value)
                   or int(d.sram_axi_arvalid.value))
            if req:
                self.req_cycles += 1
                if not int(d.sram_axi_awakeup.value):
                    self.violations.append(cyc)


async def _settle(tb, n=4):
    await ClockCycles(tb.clock, n)
    await ReadOnly()


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_axi5_wakeup(dut):
    """AWAKEUP forwarding and the held-while-requesting rule."""
    tb = Bridge2x2Axi5TB(dut)
    for pin in ("ddr_axi_awakeup", "dma_axi_awakeup"):
        assert not hasattr(dut, pin), f"{pin} exists, but that port has no 'wakeup' feature"
    dut.cpu_axi_awakeup.value = 0
    await tb.setup_clocks_and_reset()
    n = tb.level_cfg['arb_per_master']

    # 1. Idle with no wake request: sram AWAKEUP low (recommended low when idle).
    await _settle(tb, 8)
    assert int(dut.sram_axi_awakeup.value) == 0, "sram AWAKEUP high on an idle bridge"
    await RisingEdge(tb.clock)

    # 2. cpu raises AWAKEUP with no transaction: sram wakes ahead of any request.
    dut.cpu_axi_awakeup.value = 1
    await _settle(tb, 1)
    assert int(dut.sram_axi_awakeup.value) == 1, "cpu AWAKEUP did not reach the sram port"
    assert not int(dut.sram_axi_awvalid.value) and not int(dut.sram_axi_arvalid.value)
    await RisingEdge(tb.clock)
    dut.cpu_axi_awakeup.value = 0
    await _settle(tb, 2)
    assert int(dut.sram_axi_awakeup.value) == 0, "sram AWAKEUP stuck high after cpu dropped it"
    await RisingEdge(tb.clock)
    tb.log.info("  forwarding: cpu AWAKEUP reaches sram with no request, and falls with it")

    # 3. Traffic into sram with every master's AWAKEUP LOW: the port must still
    # hold AWAKEUP on every requesting cycle (derived from its own requests),
    # including dma's, whose port has no AWAKEUP at all. A slow slave makes
    # requests wait on READY, the case A14.1.1 constrains.
    chk = SramWakeChecker(dut, tb.clock)
    cocotb.start_soon(chk.run())
    tb.set_slave_response_delay(SRAM, 16)
    done = []
    # One write+read pair in flight per (master, ID). The requester BFMs keep
    # one response queue per ID and hand a beat to whichever waiting call
    # wakes first, not to the oldest; two concurrent same-ID calls could swap
    # responses (seed 80505 at full: a later write took an earlier write's B,
    # started its read early and took that read's R). The bridge returned
    # them in order -- verified at the cpu port -- so this is a test-side
    # constraint until the BFM serves same-ID waiters in issue order.
    id_locks = {(m, k): Lock() for m in (CPU, DMA) for k in range(8)}

    async def _rw(m, i):
        addr = SRAM_BASE + m * 0x1000 + 4 * i
        data = 0x3A00_0000 | (m << 16) | i
        async with id_locks[(m, i % 8)]:
            r = await tb.master_wr[m].write_transaction(addr, data, size=2, id=(m << 3) | (i % 8))
            assert r.get('success'), f"master {m} write @0x{addr:08x}: {r}"
            resp = await tb.master_rd[m].read_transaction(addr, size=2, id=(m << 3) | (i % 8))
            assert resp[0]['data'] == data, f"master {m} read @0x{addr:08x}: {resp[0]['data']:#x}"
        done.append(m)

    for m in (CPU, DMA):
        for i in range(n):
            cocotb.start_soon(_rw(m, i))
    for _ in range(8000):
        if len(done) == 2 * n:
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == 2 * n, f"{len(done)}/{2 * n} write+read pairs completed"
    assert chk.req_cycles > 0, "no request cycles observed at the sram port"
    assert not chk.violations, (
        f"sram presented a request with AWAKEUP low on {len(chk.violations)} cycle(s), "
        f"first at {chk.violations[:5]} (A14.1.1)")
    tb.log.info(f"  held: AWAKEUP high on all {chk.req_cycles} sram request cycles "
                f"(cpu and dma traffic, no master AWAKEUP)")

    # 4. Idle again: AWAKEUP falls.
    await _settle(tb, 40)
    assert int(dut.sram_axi_awakeup.value) == 0, "sram AWAKEUP high after all traffic drained"
    await RisingEdge(tb.clock)

    tb.assert_compliance()
    tb.log.info("AXI5 AWAKEUP test PASSED")


# ============================================================================
# Pytest wrapper
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_axi5_wakeup(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_2x2_axi5"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_2x2_axi5.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_wakeup_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_axi5_wakeup",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
