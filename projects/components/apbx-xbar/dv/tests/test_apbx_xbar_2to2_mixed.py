#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# APBX-001: generated mixed-version crossbar apbx_xbar_2to2_mixed
# (m0=APB4, m1=APB5, s0=APB5, s1=APB4) through the real apb4/apb5
# boundary IP (cmd/rsp fabric).
#
#   - Base transfers route for all four (master, slave) pairings.
#   - PAUSER/PWUSER values from APB5 master1 arrive at APB5 slave0;
#     transfers from APB4 master0 present '0 there.
#   - APB4 slave1 has no sideband pins at all (structural).
#   - PRUSER/PBUSER driven at slave0 return to master1 only.

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

S0_BASE = 0x1000_0000   # slave0 (APB5), 64KB window
S1_BASE = 0x1001_0000   # slave1 (APB4), 64KB window


async def _completer(dut, s, rdata, apb5=False):
    """Always-ready external completer on slave port s; logs request
    sideband (apb5 only) at each access phase."""
    getattr(dut, f"s{s}_apb_PREADY").value = 1
    getattr(dut, f"s{s}_apb_PRDATA").value = rdata
    getattr(dut, f"s{s}_apb_PSLVERR").value = 0
    if apb5:
        getattr(dut, f"s{s}_apb_PWAKEUP").value = 0
        getattr(dut, f"s{s}_apb_PRUSER").value = 1
        getattr(dut, f"s{s}_apb_PBUSER").value = 1
    log = getattr(dut, f"_s{s}_log")
    while True:
        await RisingEdge(dut.pclk)
        if int(getattr(dut, f"s{s}_apb_PSEL").value) and \
                int(getattr(dut, f"s{s}_apb_PENABLE").value):
            entry = {'addr': int(getattr(dut, f"s{s}_apb_PADDR").value)}
            if apb5:
                entry['pauser'] = int(getattr(dut, f"s{s}_apb_PAUSER").value)
                entry['pwuser'] = int(getattr(dut, f"s{s}_apb_PWUSER").value)
            log.append(entry)


async def _xfer(dut, m, addr, write, wdata=0, apb5_sideband=None, timeout=300,
                allow_timeout=False):
    """One APB transfer on master port m. apb5_sideband=(pauser,pwuser)
    drives the APB5 master's request pins. Returns rdata, pslverr, and
    (for the APB5 master) the completer sideband at the ready edge.
    allow_timeout=True returns None instead of asserting -- the
    decode-miss scenario needs to tell a HANG from an error response."""
    if apb5_sideband is not None:
        dut.m1_apb_PAUSER.value = apb5_sideband[0]
        dut.m1_apb_PWUSER.value = apb5_sideband[1]
    p = f"m{m}_apb_"
    getattr(dut, p + "PADDR").value = addr
    getattr(dut, p + "PWRITE").value = int(write)
    getattr(dut, p + "PWDATA").value = wdata
    getattr(dut, p + "PSTRB").value = 0xF if write else 0
    getattr(dut, p + "PPROT").value = 0
    getattr(dut, p + "PSEL").value = 1
    getattr(dut, p + "PENABLE").value = 0
    await RisingEdge(dut.pclk)
    getattr(dut, p + "PENABLE").value = 1
    got = None
    for _ in range(timeout):
        await RisingEdge(dut.pclk)
        if int(getattr(dut, p + "PREADY").value):
            got = {'prdata': int(getattr(dut, p + "PRDATA").value),
                   'pslverr': int(getattr(dut, p + "PSLVERR").value)}
            if m == 1:
                got['pruser'] = int(dut.m1_apb_PRUSER.value)
                got['pbuser'] = int(dut.m1_apb_PBUSER.value)
            break
    if got is None and not allow_timeout:
        assert False, f"master {m} transfer timed out"
    getattr(dut, p + "PSEL").value = 0
    getattr(dut, p + "PENABLE").value = 0
    await ClockCycles(dut.pclk, 3)
    return got


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def apbx_2to2_mixed_test(dut):
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    # Structural: the APB4 slave port must not have sideband pins.
    for pin in ("s1_apb_PAUSER", "s1_apb_PWUSER", "s1_apb_PWAKEUP",
                "s1_apb_PRUSER", "s1_apb_PBUSER", "m0_apb_PAUSER",
                "m0_apb_PRUSER"):
        assert not hasattr(dut, pin), f"APB4 port grew sideband pin {pin}"

    for m in range(2):
        getattr(dut, f"m{m}_apb_PSEL").value = 0
        getattr(dut, f"m{m}_apb_PENABLE").value = 0
    dut.m1_apb_PAUSER.value = 0
    dut.m1_apb_PWUSER.value = 0

    dut._s0_log, dut._s1_log = [], []
    cocotb.start_soon(_completer(dut, 0, 0xC0DE0000, apb5=True))
    cocotb.start_soon(_completer(dut, 1, 0xC0DE1111, apb5=False))

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 5)

    # 1. APB5 m1 -> APB5 s0: request sideband arrives; completer
    #    sideband returns.
    got = await _xfer(dut, 1, S0_BASE + 0x10, write=1, wdata=0xA5A50001,
                      apb5_sideband=(1, 1))
    assert got['pruser'] == 1 and got['pbuser'] == 1, \
        f"completer sideband lost m1<-s0: {got}"
    assert dut._s0_log and dut._s0_log[-1]['pauser'] == 1 \
        and dut._s0_log[-1]['pwuser'] == 1, \
        f"request sideband lost m1->s0: {dut._s0_log[-1:]}"

    # 2. APB4 m0 -> APB5 s0: base OK, sideband gated to '0.
    got = await _xfer(dut, 0, S0_BASE + 0x20, write=0)
    assert got['prdata'] == 0xC0DE0000
    assert dut._s0_log[-1]['pauser'] == 0 and dut._s0_log[-1]['pwuser'] == 0, \
        f"APB4 master's sideband leaked to s0: {dut._s0_log[-1]}"

    # 3. APB5 m1 -> APB4 s1: base OK; nothing returns on m1's
    #    completer-sideband pins for an APB4 slave.
    got = await _xfer(dut, 1, S1_BASE + 0x30, write=0, apb5_sideband=(1, 1))
    assert got['prdata'] == 0xC0DE1111
    assert got['pruser'] == 0 and got['pbuser'] == 0, \
        f"APB4 slave1 sideband ghost on m1: {got}"

    # 4. APB4 m0 -> APB4 s1: plain.
    got = await _xfer(dut, 0, S1_BASE + 0x40, write=1, wdata=0x5A5A0004)
    assert got['prdata'] == 0xC0DE1111

    assert len(dut._s1_log) >= 2, f"slave1 transfer count: {len(dut._s1_log)}"
    dut._log.info("apbx_xbar_2to2_mixed: all four pairings OK "
                  f"(s0={len(dut._s0_log)} xfers, s1={len(dut._s1_log)})")

    # 5. APBX-002 (qc round_7): decode miss must COMPLETE with PSLVERR.
    #    An out-of-range access used to leave cmd_ready low forever,
    #    wedging that master with PREADY low and no error signature.
    #    Run last: on the old RTL the first miss wedges the crossbar.
    n_s0, n_s1 = len(dut._s0_log), len(dut._s1_log)
    for m, bad_addr in ((0, S0_BASE - 4), (1, S1_BASE + 0x10000)):
        got = await _xfer(dut, m, bad_addr, write=0, timeout=60,
                          allow_timeout=True)
        assert got is not None, (
            f"decode miss m{m} at 0x{bad_addr:08X} HUNG: PREADY never "
            f"asserted -- out-of-range access wedges that master")
        assert got['pslverr'] == 1, (
            f"decode miss m{m} at 0x{bad_addr:08X} completed without "
            f"PSLVERR: {got}")
    assert len(dut._s0_log) == n_s0 and len(dut._s1_log) == n_s1, \
        "decode miss leaked a transfer to a slave"

    # fabric must still work after the misses
    got = await _xfer(dut, 0, S0_BASE + 0x50, write=1, wdata=0x600D0005)
    assert got['pslverr'] == 0, f"m0 wedged after decode miss: {got}"
    got = await _xfer(dut, 1, S1_BASE + 0x60, write=0)
    assert got['pslverr'] == 0, f"m1 wedged after decode miss: {got}"
    dut._log.info("apbx_xbar_2to2_mixed: decode misses PSLVERR'd, fabric alive")


def test_apbx_xbar_2to2_mixed(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_xbar': 'projects/components/apbx-xbar/rtl',
    })

    dut_name = "apbx_xbar_2to2_mixed"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_2to2_mixed.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}{worker_suffix}"

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
        testcase="apbx_2to2_mixed_test",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **waves['extra_env'],
        },
    )
