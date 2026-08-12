#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# APBX-001: mixed APB4/APB5 routing through apbx_xbar_thin.
#
# Config under test: M=2, S=2, MST_APB5=2'b10, SLV_APB5=2'b01 —
# master0=APB4, master1=APB5, slave0=APB5, slave1=APB4.
#
#   - Base APB4 transfers route for every (master, slave) pairing.
#   - PAUSER/PWUSER reach slave0 (APB5) ONLY from master1 (APB5).
#   - Slave1 (APB4) never sees nonzero request sideband.
#   - PWAKEUP/PRUSER/PBUSER return from slave0 to master1 only; tied
#     nonzero values on slave1's completer-sideband inputs must be
#     gated off for every master.
#
# The DUT's per-port buses are packed 2-D vectors, which the Verilator
# VPI exposes as single flat registers — all driving/sampling below
# goes through whole-vector shadow values and bit slicing.

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

S0_BASE, S0_LIMIT = 0x1000_0000, 0x1000_0FFF   # slave0 (APB5)
S1_BASE, S1_LIMIT = 0x2000_0000, 0x2000_0FFF   # slave1 (APB4)

AW = DW = 32
SW = 4


def field(value, idx, width):
    """Extract element idx from a flat packed [N-1:0][width-1:0] value."""
    return (value >> (idx * width)) & ((1 << width) - 1)


class MasterPins:
    """Shadow-vector driver for the M=2 master-side packed buses."""

    def __init__(self, dut):
        self.dut = dut
        self.psel = self.penable = self.pwrite = 0
        self.paddr = self.pwdata = self.pstrb = self.pprot = 0
        self.pauser = self.pwuser = 0
        self.flush()

    def set(self, m, addr, write, wdata, pauser, pwuser):
        self.paddr = (self.paddr & ~(0xFFFFFFFF << (m * AW))) | (addr << (m * AW))
        self.pwdata = (self.pwdata & ~(0xFFFFFFFF << (m * DW))) | (wdata << (m * DW))
        self.pstrb = (self.pstrb & ~(0xF << (m * SW))) | ((0xF if write else 0) << (m * SW))
        self.pwrite = (self.pwrite & ~(1 << m)) | (int(write) << m)
        self.pauser = (self.pauser & ~(1 << m)) | (int(pauser) << m)
        self.pwuser = (self.pwuser & ~(1 << m)) | (int(pwuser) << m)

    def sel(self, m, psel, penable):
        self.psel = (self.psel & ~(1 << m)) | (int(psel) << m)
        self.penable = (self.penable & ~(1 << m)) | (int(penable) << m)

    def flush(self):
        d = self.dut
        d.m_apb_psel.value = self.psel
        d.m_apb_penable.value = self.penable
        d.m_apb_pwrite.value = self.pwrite
        d.m_apb_paddr.value = self.paddr
        d.m_apb_pwdata.value = self.pwdata
        d.m_apb_pstrb.value = self.pstrb
        d.m_apb_pprot.value = self.pprot
        d.m_apb_pauser.value = self.pauser
        d.m_apb_pwuser.value = self.pwuser


async def _xfer(dut, pins, m, addr, write, wdata=0, pauser=0, pwuser=0,
                timeout=200):
    """One APB transfer from master m; returns master-side response +
    completer sideband sampled at the ready edge."""
    pins.set(m, addr, write, wdata, pauser, pwuser)
    pins.sel(m, 1, 0)
    pins.flush()
    await RisingEdge(dut.pclk)
    pins.sel(m, 1, 1)
    pins.flush()
    got = None
    for _ in range(timeout):
        await RisingEdge(dut.pclk)
        if (int(dut.m_apb_pready.value) >> m) & 1:
            got = {
                'prdata': field(int(dut.m_apb_prdata.value), m, DW),
                'pwakeup': (int(dut.m_apb_pwakeup.value) >> m) & 1,
                'pruser': (int(dut.m_apb_pruser.value) >> m) & 1,
                'pbuser': (int(dut.m_apb_pbuser.value) >> m) & 1,
            }
            break
    assert got is not None, f"master {m} transfer timed out"
    pins.sel(m, 0, 0)
    pins.flush()
    await RisingEdge(dut.pclk)
    return got


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def apbx_thin_mixed_test(dut):
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    dut.SLAVE_ENABLE.value = 0b11
    dut.SLAVE_ADDR_BASE.value = (S1_BASE << AW) | S0_BASE
    dut.SLAVE_ADDR_LIMIT.value = (S1_LIMIT << AW) | S0_LIMIT
    dut.THRESHOLDS.value = (1 << 4) | 1

    pins = MasterPins(dut)

    # Always-ready completers; slave0 (APB5) drives live completer
    # sideband, slave1's inputs are tied NONZERO on purpose — the core
    # must gate them (a real APB4 completer has no such pins).
    dut.s_apb_pready.value = 0b11
    dut.s_apb_prdata.value = (0xC0DE1111 << DW) | 0xC0DE0000
    dut.s_apb_pslverr.value = 0
    dut.s_apb_pwakeup.value = 0b11
    dut.s_apb_pruser.value = 0b11
    dut.s_apb_pbuser.value = 0b11

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 2)

    s0_sb = []

    async def monitor():
        while True:
            await RisingEdge(dut.pclk)
            psel = int(dut.s_apb_psel.value)
            pen = int(dut.s_apb_penable.value)
            rdy = int(dut.s_apb_pready.value)
            if (psel & pen & rdy) & 1:                       # slave0 access
                s0_sb.append((int(dut.s_apb_pauser.value) & 1,
                              int(dut.s_apb_pwuser.value) & 1))
            # APB4 slave1 must never see request sideband
            assert (int(dut.s_apb_pauser.value) >> 1) & 1 == 0, \
                "APB4 slave1 saw nonzero PAUSER"
            assert (int(dut.s_apb_pwuser.value) >> 1) & 1 == 0, \
                "APB4 slave1 saw nonzero PWUSER"
    cocotb.start_soon(monitor())

    # 1. APB5 master1 -> APB5 slave0: sideband both directions.
    got = await _xfer(dut, pins, 1, S0_BASE + 0x10, write=1,
                      wdata=0xA5A50001, pauser=1, pwuser=1)
    assert (got['pwakeup'], got['pruser'], got['pbuser']) == (1, 1, 1), \
        f"APB5->APB5 completer sideband lost: {got}"
    assert s0_sb and s0_sb[-1] == (1, 1), \
        f"APB5->APB5 request sideband lost: {s0_sb}"

    # 2. APB4 master0 -> APB5 slave0: base transfer OK; request sideband
    #    gated to 0 even with master0's (tied) pins driven high.
    got = await _xfer(dut, pins, 0, S0_BASE + 0x20, write=0,
                      pauser=1, pwuser=1)
    assert got['prdata'] == 0xC0DE0000
    assert (got['pwakeup'], got['pruser'], got['pbuser']) == (0, 0, 0), \
        f"APB4 master0 saw completer sideband: {got}"
    assert s0_sb[-1] == (0, 0), \
        f"APB4 master's sideband leaked to slave0: {s0_sb[-1]}"

    # 3. APB5 master1 -> APB4 slave1: base OK; slave1's tied-high
    #    completer sideband must NOT reach master1.
    got = await _xfer(dut, pins, 1, S1_BASE + 0x30, write=0,
                      pauser=1, pwuser=1)
    assert got['prdata'] == 0xC0DE1111
    assert (got['pwakeup'], got['pruser'], got['pbuser']) == (0, 0, 0), \
        f"APB4 slave1's tied sideband leaked to master1: {got}"

    # 4. APB4 master0 -> APB4 slave1: plain APB4.
    got = await _xfer(dut, pins, 0, S1_BASE + 0x40, write=1,
                      wdata=0x5A5A0004)
    assert got['prdata'] == 0xC0DE1111
    assert (got['pwakeup'], got['pruser'], got['pbuser']) == (0, 0, 0)

    await ClockCycles(dut.pclk, 10)
    dut._log.info("apbx_xbar_thin mixed APB4/APB5 routing: all 4 pairings OK")


def test_apbx_xbar_thin_mixed(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_xbar': 'projects/components/apbx-xbar/rtl',
    })

    dut_name = "apbx_xbar_thin"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_thin.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}_mixed{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="apbx_thin_mixed_test",
        sim_build=sim_build,
        waves=False,
        # M=2,S=2; master1 and slave0 are APB5
        parameters={'M': 2, 'S': 2, 'MST_APB5': 2, 'SLV_APB5': 1},
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **waves['extra_env'],
        },
    )
