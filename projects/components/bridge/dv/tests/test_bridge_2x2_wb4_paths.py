#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-019 sign-off for Wishbone B4 ports.
#
# bridge_2x2_wb4 has a Wishbone requester (wbm) and an AXI4 requester (cpu)
# in front of a 64-bit AXI4 memory (mem) and a 32-bit Wishbone completer
# (wbp). The generated tests prove the plain round trip on every path; this
# file covers what the two Wishbone ports specifically owe:
#
#   - error folding both ways: an unmapped address from the Wishbone
#     requester terminates ERR (the subtractive slave's DECERR has one
#     Wishbone spelling), the AXI4 requester's out-of-range access at the
#     Wishbone completer comes back SLVERR from the completer's ERR, and
#     every port keeps working afterwards;
#   - SEL is the byte-lane truth: partial-SEL writes from the Wishbone
#     requester touch only their lanes, at the 32-bit Wishbone completer and
#     in the 64-bit memory (through the wide-slave aligner);
#   - an AXI4 burst at the Wishbone completer becomes exactly one transfer
#     per beat, in address order, and the read burst returns the memory;
#   - the AXI4 requester's bursts and the Wishbone requester's transfers in
#     flight at the Wishbone completer together: every response goes to the
#     port that asked, in the order it asked (B4 terminates in issue order).

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

from projects.components.bridge.dv.tbclasses.bridge2x2_wb4_tb import (
    Bridge2x2Wb4TB, AxiResponseError,
)
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK

WBM, CPU = 0, 1            # masters
MEM, WBP = 0, 1            # slaves
MEM_BASE, WBP_BASE, WBP_RANGE = 0x0000_0000, 0x5000_0000, 0x0001_0000
UNMAPPED = 0xC000_0000

COUNTS = {'gate': 4, 'func': 12, 'full': 32}


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_wb4_err_fold(dut):
    tb = Bridge2x2Wb4TB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]
    failures = []
    for i in range(n):
        # Wishbone requester -> nothing owns it -> DECERR -> ERR.
        bad = UNMAPPED + 0x100 * i
        for op in ('write', 'read'):
            try:
                if op == 'write':
                    await tb.master_write(WBM, bad, 0xDEAD_0000 | i)
                else:
                    await tb.master_read(WBM, bad)
                failures.append(f"wbm {op} to unmapped 0x{bad:08X} terminated ACK")
            except AxiResponseError as e:
                if e.resp != 2:
                    failures.append(f"wbm {op} to unmapped: resp {e.resp}, expected ERR reported as 2")
        # AXI4 requester -> past the Wishbone completer's memory -> its ERR -> SLVERR.
        past = WBP_BASE + tb._slave_mem_bytes(WBP) + 0x10 * i
        if past < WBP_BASE + WBP_RANGE:
            for op in ('write', 'read'):
                try:
                    if op == 'write':
                        await tb.master_write(CPU, past, 0xBAD0_0000 | i)
                    else:
                        await tb.master_read(CPU, past)
                    failures.append(f"cpu {op} past wbp memory 0x{past:08X} answered OKAY")
                except AxiResponseError as e:
                    if e.resp != 2:
                        failures.append(f"cpu {op} past wbp memory: resp {e.resp}, expected SLVERR (ERR folded)")
        # Both ports still work.
        for m, addr in ((WBM, WBP_BASE + 0x100 + 4 * i), (CPU, WBP_BASE + 0x200 + 4 * i),
                        (WBM, MEM_BASE + 0x1000 + 4 * i)):
            data = 0x600D_0000 | (m << 8) | i
            try:
                await tb.master_write(m, addr, data)
                got = await tb.master_read(m, addr)
            except AxiResponseError as e:
                failures.append(f"m{m} in-range access after an error failed: {e}")
                continue
            if got != data:
                failures.append(f"m{m} read back 0x{got:08X} after writing 0x{data:08X} at 0x{addr:08X}")
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-019 error folding PASSED: {n} rounds")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_wb4_sel_lanes(dut):
    tb = Bridge2x2Wb4TB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]
    wb = tb.master_wb[WBM]
    failures = []
    shadow = {}

    def _expect(slave, addr, data, sel):
        cur = shadow.get((slave, addr))
        if cur is None:
            cur = tb.slave_mem_read(slave, addr, byte_count=4)
        for b in range(4):
            if (sel >> b) & 1:
                cur = (cur & ~(0xFF << (8 * b))) | (((data >> (8 * b)) & 0xFF) << (8 * b))
        shadow[(slave, addr)] = cur
        return cur

    for i in range(n):
        for slave, base in ((WBP, WBP_BASE + 0x400), (MEM, MEM_BASE + 0x2000)):
            addr = base + 4 * (i % 16) + (0 if slave == WBP else 8 * (i // 16))
            data = tb.rng.getrandbits(32)
            sel = tb.rng.randrange(1, 16)
            pkt = await wb.write(addr, data, sel=sel)
            if int(pkt.fields['status']) != WB4_STATUS_ACK:
                failures.append(f"round {i}: SEL write to slave {slave} @0x{addr:08X} terminated {pkt.fields['status']}")
            want = _expect(slave, addr, data, sel)
            got = tb.slave_mem_read(slave, addr, byte_count=4)
            if got != want:
                failures.append(f"round {i}: slave {slave} @0x{addr:08X} sel=0x{sel:X}: memory 0x{got:08X}, expected 0x{want:08X}")
            rd = await tb.master_read(WBM, addr)
            if rd != want:
                failures.append(f"round {i}: wbm read 0x{rd:08X} at 0x{addr:08X}, expected 0x{want:08X}")
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-019 SEL lanes PASSED: {2 * n} partial writes")


@cocotb.test(timeout_time=6000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_wb4_bursts(dut):
    tb = Bridge2x2Wb4TB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]
    wbp = tb.slave_wb[WBP]
    failures = []
    for i in range(n):
        beats = 2 + (i % 7)                     # 2..8
        addr = WBP_BASE + 0x1000 + 0x40 * i
        data = [(0xB0 << 24) | (i << 8) | k for k in range(beats)]
        accepted0 = wbp.stats['accepted']
        res = await tb.master_wr[CPU].write_transaction(addr, data, id=i % 16, size=2)
        if isinstance(res, dict) and not res.get('success', True):
            failures.append(f"burst {i}: write x{beats} @0x{addr:08X} failed: {res}")
        got_txns = wbp.stats['accepted'] - accepted0
        if got_txns != beats:
            failures.append(f"burst {i}: {beats} AXI beats became {got_txns} Wishbone transfers")
        adrs = [int(p.fields['adr']) for p in list(wbp.sentQ)[-beats:]]
        if adrs != [addr + 4 * k for k in range(beats)]:
            failures.append(f"burst {i}: Wishbone addresses {[hex(a) for a in adrs]} not in beat order from 0x{addr:08X}")
        for k, d in enumerate(data):
            got = tb.slave_mem_read(WBP, addr + 4 * k, byte_count=4)
            if got != d:
                failures.append(f"burst {i} beat {k}: wbp memory 0x{got:08X}, wrote 0x{d:08X}")
        rd = await tb.master_rd[CPU].read_transaction(addr, burst_len=beats, id=i % 16, size=2)
        if list(rd) != data:
            failures.append(f"burst {i}: read x{beats} returned {[hex(x) for x in rd]}, expected {[hex(x) for x in data]}")
    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-019 bursts PASSED: {n} bursts decomposed one transfer per beat")


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_wb4_concurrent(dut):
    tb = Bridge2x2Wb4TB(dut)
    await tb.setup_clocks_and_reset()
    n = {'gate': 6, 'func': 16, 'full': 40}[tb.level]
    tb.set_slave_response_delay(WBP, 3)

    errors, done = [], []

    async def _cpu():
        for i in range(n):
            beats = 4
            addr = WBP_BASE + 0x4000 + 0x20 * i
            data = [(0xC0 << 24) | (i << 8) | k for k in range(beats)]
            try:
                await tb.master_wr[CPU].write_transaction(addr, data, id=i % 16, size=2)
                rd = await tb.master_rd[CPU].read_transaction(addr, burst_len=beats, id=i % 16, size=2)
                if list(rd) != data:
                    errors.append(f"cpu burst {i}: {[hex(x) for x in rd]} != {[hex(x) for x in data]}")
            except Exception as e:  # noqa: BLE001 -- recorded, asserted below
                errors.append(f"cpu burst {i}: {e}")
        done.append('cpu')

    async def _wbm():
        for i in range(2 * n):
            addr = WBP_BASE + 0x8000 + 4 * i
            data = (0xD0 << 24) | i
            try:
                await tb.master_write(WBM, addr, data)
                got = await tb.master_read(WBM, addr)
                if got != data:
                    errors.append(f"wbm {i}: read 0x{got:08X}, wrote 0x{data:08X}")
            except Exception as e:  # noqa: BLE001
                errors.append(f"wbm {i}: {e}")
        done.append('wbm')

    cocotb.start_soon(_cpu())
    cocotb.start_soon(_wbm())
    for _ in range(8000):
        if len(done) == 2:
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == 2, f"streams finished: {done}"
    assert not errors, f"{len(errors)} failure(s):\n  " + "\n  ".join(errors[:10])
    for i in range(n):
        for k in range(4):
            got = tb.slave_mem_read(WBP, WBP_BASE + 0x4000 + 0x20 * i + 4 * k, byte_count=4)
            want = (0xC0 << 24) | (i << 8) | k
            assert got == want, f"cpu burst {i} beat {k}: memory 0x{got:08X}, expected 0x{want:08X}"
    for i in range(2 * n):
        got = tb.slave_mem_read(WBP, WBP_BASE + 0x8000 + 4 * i, byte_count=4)
        assert got == (0xD0 << 24) | i, f"wbm {i}: memory 0x{got:08X}"
    tb.log.info(f"BRIDGE-019 concurrent PASSED: {n} cpu bursts + {2 * n} wbm transfers at the Wishbone completer")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_wb4"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_{testcase}_{test_level}_{reg_level}"
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
        testcase=f"cocotb_test_bridge_2x2_wb4_{testcase}",
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


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_wb4_err_fold(request, test_level):
    _run(request, test_level, "err_fold")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_wb4_sel_lanes(request, test_level):
    _run(request, test_level, "sel_lanes")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_wb4_bursts(request, test_level):
    _run(request, test_level, "bursts")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_wb4_concurrent(request, test_level):
    _run(request, test_level, "concurrent")
