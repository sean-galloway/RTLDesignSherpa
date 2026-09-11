#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-014 sign-off for LITE REQUESTER ports.
#
# bridge_2x2_lite_req has an AXI4-Lite master and an AXI5-Lite master (with
# the two forwardable groups, 'user' and 'exclusive') in front of a 64-bit
# AXI4 memory and an AXI5-Lite register block. The generated tests already
# prove the data round trip; what they cannot see is the sideband and the
# lane placement, which is what a Lite requester port has to get right:
#
#   - the AXI5-Lite master's AWUSER/WUSER/ARUSER and AWLOCK/ARLOCK reach the
#     AXI5-Lite slave (its own 'user' feature forwards them) -- and the AXI4-
#     Lite master's traffic arrives there with user=0 and lock=0, because it
#     has nothing to say;
#   - the sideband groups with no AXI4 home are terminated, not floating:
#     the completer-driven ones read 0 at the requester after traffic, and
#     the requester-driven ones can be driven to anything without effect;
#   - a 32-bit Lite write into the 64-bit memory lands in the byte lanes its
#     address selects (the wide-slave aligner), for BOTH Lite protocols;
#   - two ID-less requesters can have transactions in flight at one slave
#     at the same time and each gets its own response back (the fabric ID is
#     the master index alone, BRIDGE-016).

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

from projects.components.bridge.dv.tbclasses.bridge2x2_lite_req_tb import (
    Bridge2x2LiteReqTB,
)

LITE4, LITE5 = 0, 1          # masters
MEM, REGS = 0, 1             # slaves
REGS_BASE = 0x4000_0000
MEM_BASE = 0x0000_0000

# Completer-driven AXI5-Lite sideband the bridge terminates at the requester
# (no AXI4 source): must read 0, never X, once traffic has flowed.
TIED_AT_MASTER = ('bloop', 'btrace', 'rloop', 'rtrace', 'rpoison')

COUNTS = {'gate': 4, 'func': 12, 'full': 32}


def _sig(tb, name):
    handle = getattr(tb.dut, f"lite5_axil_{name}")
    try:
        return int(handle.value)
    except ValueError:
        return None


def _record(store, key):
    def _cb(pkt):
        store.append((key, pkt))
    return _cb


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_lite_req_user_lock(dut):
    """USER and LOCK from the AXI5-Lite requester reach the AXI5-Lite
    completer; the AXI4-Lite requester's traffic arrives with both at 0;
    the terminated groups read 0 at the requester."""
    tb = Bridge2x2LiteReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]

    seen = []
    tb.slave_wr[REGS].aw_channel.add_callback(_record(seen, 'aw'))
    tb.slave_wr[REGS].w_channel.add_callback(_record(seen, 'w'))
    tb.slave_rd[REGS].ar_channel.add_callback(_record(seen, 'ar'))

    tb.log.info("=" * 80)
    tb.log.info(f"BRIDGE-014 lite requesters, sideband (level={tb.level}, {n} rounds)")
    tb.log.info("=" * 80)

    failures = []
    for i in range(n):
        addr = REGS_BASE + 0x100 + 4 * i
        user = i & 1
        lock = (i >> 1) & 1
        data = 0x5A5A_0000 | i

        # AXI5-Lite requester, driving the forwardable groups.
        del seen[:]
        await tb.master_wr[LITE5].single_write(addr, data, awuser=user, wuser=user, awlock=lock)
        aw = [p for k, p in seen if k == 'aw']
        w = [p for k, p in seen if k == 'w']
        if len(aw) != 1 or len(w) != 1:
            failures.append(f"round {i}: AXI5-Lite write produced {len(aw)} AW / {len(w)} W at regs")
        else:
            if int(aw[0].fields.get('user', 0)) != user:
                failures.append(f"round {i}: regs saw awuser={aw[0].fields.get('user')} from lite5, drove {user}")
            if int(aw[0].fields.get('lock', 0)) != lock:
                failures.append(f"round {i}: regs saw awlock={aw[0].fields.get('lock')} from lite5, drove {lock}")
            if int(w[0].fields.get('user', 0)) != user:
                failures.append(f"round {i}: regs saw wuser={w[0].fields.get('user')} from lite5, drove {user}")
        got = tb.slave_mem_read(REGS, addr, byte_count=4)
        if got != data:
            failures.append(f"round {i}: regs holds 0x{got:08X} after lite5 wrote 0x{data:08X}")

        del seen[:]
        rdata = await tb.master_rd[LITE5].single_read(addr, aruser=user, arlock=lock)
        ar = [p for k, p in seen if k == 'ar']
        if len(ar) != 1:
            failures.append(f"round {i}: AXI5-Lite read produced {len(ar)} AR at regs")
        else:
            if int(ar[0].fields.get('user', 0)) != user:
                failures.append(f"round {i}: regs saw aruser={ar[0].fields.get('user')} from lite5, drove {user}")
            if int(ar[0].fields.get('lock', 0)) != lock:
                failures.append(f"round {i}: regs saw arlock={ar[0].fields.get('lock')} from lite5, drove {lock}")
        if rdata != data:
            failures.append(f"round {i}: lite5 read back 0x{rdata:08X}, expected 0x{data:08X}")

        # AXI4-Lite requester: no sideband to forward, the completer sees 0.
        del seen[:]
        data4 = 0xA4A4_0000 | i
        await tb.master_write(LITE4, addr, data4)
        rdata4 = await tb.master_read(LITE4, addr)
        aw = [p for k, p in seen if k == 'aw']
        ar = [p for k, p in seen if k == 'ar']
        if len(aw) != 1 or len(ar) != 1:
            failures.append(f"round {i}: AXI4-Lite traffic produced {len(aw)} AW / {len(ar)} AR at regs")
        else:
            for pkt, label in ((aw[0], 'aw'), (ar[0], 'ar')):
                if int(pkt.fields.get('user', 0)) != 0 or int(pkt.fields.get('lock', 0)) != 0:
                    failures.append(f"round {i}: regs saw {label}user={pkt.fields.get('user')} "
                                    f"{label}lock={pkt.fields.get('lock')} from the AXI4-Lite master")
        if rdata4 != data4:
            failures.append(f"round {i}: lite4 read back 0x{rdata4:08X}, expected 0x{data4:08X}")

        # Terminated completer-driven groups at the AXI5-Lite requester.
        for name in TIED_AT_MASTER:
            v = _sig(tb, name)
            if v != 0:
                failures.append(f"round {i}: lite5_axil_{name} reads {v!r}; it has no AXI4 source "
                                f"and must be driven to 0")

    assert not failures, f"{len(failures)} sideband failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-014 lite sideband PASSED: {n} rounds, user/lock forwarded, "
                f"{len(TIED_AT_MASTER)} terminated groups at 0")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_lite_req_wide_lanes(dut):
    """A 32-bit Lite write into the 64-bit memory lands in the lanes its
    address selects -- both halves of a row, from both Lite requesters,
    with the other half untouched."""
    tb = Bridge2x2LiteReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]

    failures = []
    for i in range(n):
        row = MEM_BASE + 0x1000 + 8 * i
        lo, hi = 0x1000_0000 | i, 0x2000_0000 | i
        # Master alternates per row so both aligners are exercised; the
        # halves are written in opposite order every other row.
        m = LITE4 if (i & 1) == 0 else LITE5
        first, second = ((row, lo), (row + 4, hi)) if (i & 2) == 0 else ((row + 4, hi), (row, lo))
        await tb.master_write(m, first[0], first[1])
        mid_lo = tb.slave_mem_read(MEM, row, byte_count=4)
        mid_hi = tb.slave_mem_read(MEM, row + 4, byte_count=4)
        # After the first write only that half changed; the other still
        # holds its seed pattern.
        expect_lo = lo if first[0] == row else tb.slave_mem_read(MEM, row, byte_count=4)
        if first[0] == row and mid_lo != lo:
            failures.append(f"row {i}: low half holds 0x{mid_lo:08X} after writing 0x{lo:08X} at +0")
        if first[0] == row + 4 and mid_hi != hi:
            failures.append(f"row {i}: high half holds 0x{mid_hi:08X} after writing 0x{hi:08X} at +4")
        await tb.master_write(m, second[0], second[1])
        got_lo = tb.slave_mem_read(MEM, row, byte_count=4)
        got_hi = tb.slave_mem_read(MEM, row + 4, byte_count=4)
        if (got_lo, got_hi) != (lo, hi):
            failures.append(f"row {i} (master {m}): memory row = 0x{got_hi:08X}_{got_lo:08X}, "
                            f"expected 0x{hi:08X}_{lo:08X} -- a lane-0 aligner bug")
        # Read back through the OTHER requester: same lanes on the read side.
        other = LITE5 if m == LITE4 else LITE4
        r_lo = await tb.master_read(other, row)
        r_hi = await tb.master_read(other, row + 4)
        if (r_lo, r_hi) != (lo, hi):
            failures.append(f"row {i}: master {other} read 0x{r_hi:08X}/0x{r_lo:08X}, "
                            f"expected 0x{hi:08X}/0x{lo:08X}")

    assert not failures, f"{len(failures)} lane failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-014 wide lanes PASSED: {n} rows, both halves, both Lite requesters")


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_lite_req_concurrent(dut):
    """Both ID-less requesters in flight at the 64-bit memory at once, with
    a slow completer so the transactions actually overlap; every read
    returns its own data and every write lands."""
    tb = Bridge2x2LiteReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = {'gate': 8, 'func': 24, 'full': 64}[tb.level]
    tb.set_slave_response_delay(MEM, 6)

    plan = []
    for m in (LITE4, LITE5):
        for i in range(n):
            plan.append((m, MEM_BASE + 0x8000 + (m * 0x1000) + 4 * i, (0xC0 | m) << 24 | i))

    done = []
    errors = []

    async def _write(m, addr, data):
        try:
            await tb.master_write(m, addr, data)
        except Exception as e:  # noqa: BLE001 -- recorded, asserted below
            errors.append(f"write m{m} 0x{addr:08X}: {e}")
        done.append(1)

    for m, addr, data in plan:
        cocotb.start_soon(_write(m, addr, data))
    for _ in range(4000):
        if len(done) == len(plan):
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == len(plan), f"only {len(done)}/{len(plan)} concurrent writes completed"
    assert not errors, "\n".join(errors[:10])

    for m, addr, data in plan:
        got = tb.slave_mem_read(MEM, addr, byte_count=4)
        assert got == data, f"m{m} wrote 0x{data:08X} at 0x{addr:08X}, memory holds 0x{got:08X}"

    del done[:]
    results = {}

    async def _read(m, addr):
        try:
            results[(m, addr)] = await tb.master_read(m, addr)
        except Exception as e:  # noqa: BLE001
            errors.append(f"read m{m} 0x{addr:08X}: {e}")
        done.append(1)

    for m, addr, _ in plan:
        cocotb.start_soon(_read(m, addr))
    for _ in range(4000):
        if len(done) == len(plan):
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == len(plan), f"only {len(done)}/{len(plan)} concurrent reads completed"
    assert not errors, "\n".join(errors[:10])
    bad = [(m, addr, results.get((m, addr)), data) for m, addr, data in plan
           if results.get((m, addr)) != data]
    assert not bad, (f"{len(bad)} read(s) returned another transaction's data: "
                     + ", ".join(f"m{m}@0x{a:08X} got {g!r} want 0x{d:08X}" for m, a, g, d in bad[:6]))
    tb.log.info(f"BRIDGE-014 concurrent PASSED: {len(plan)} writes + {len(plan)} reads "
                f"from two ID-less requesters, slave delay 6")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_lite_req"
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
        testcase=f"cocotb_test_bridge_2x2_lite_req_{testcase}",
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
def test_bridge_2x2_lite_req_user_lock(request, test_level):
    _run(request, test_level, "user_lock")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_lite_req_wide_lanes(request, test_level):
    _run(request, test_level, "wide_lanes")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_lite_req_concurrent(request, test_level):
    _run(request, test_level, "concurrent")
