#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-014 sign-off for APB REQUESTER ports.
#
# bridge_2x3_apb_req has an APB4 and an APB5 requester, each converted by
# apb{4,5}_to_axi4 in its master adapter, in front of an AXI4 memory, an
# AXI5-Lite register block (with 'user') and an APB4 peripheral. The
# generated tests prove the plain round trip; this file covers what an APB
# requester port specifically owes:
#
#   - PSLVERR for an unmapped address: the subtractive slave's DECERR has to
#     fold into APB's one error bit, and the port must keep working after
#     (the converter is one-outstanding; an unanswered response wedges it);
#   - PPROT reaches AxPROT at the AXI4 completer;
#   - the APB5 requester's PAUSER/PWUSER reach the AXI5-Lite completer as
#     awuser/wuser/aruser (the fabric's one USER bit), and the APB4
#     requester's traffic arrives there with user=0;
#   - APB in, APB out: both requesters read and write the APB4 peripheral
#     through the whole fabric, interleaved.

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

from projects.components.bridge.dv.tbclasses.bridge2x3_apb_req_tb import (
    Bridge2x3ApbReqTB, AxiResponseError,
)

APB4M, APB5M = 0, 1                 # masters
MEM, LREGS, PERIPH = 0, 1, 2        # slaves
MEM_BASE, LREGS_BASE, PERIPH_BASE = 0x0000_0000, 0x4000_0000, 0x5000_0000
UNMAPPED = 0xC000_0000              # nothing owns this: subtractive slave

COUNTS = {'gate': 4, 'func': 12, 'full': 32}


def _record(store, key):
    def _cb(pkt):
        store.append((key, pkt))
    return _cb


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x3_apb_req_pslverr(dut):
    """Unmapped accesses answer PSLVERR and the port is not wedged after."""
    tb = Bridge2x3ApbReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]

    failures = []
    for i in range(n):
        for m in (APB4M, APB5M):
            bad = UNMAPPED + 0x100 * i + 4 * m
            for op in ('write', 'read'):
                try:
                    if op == 'write':
                        await tb.master_write(m, bad, 0xDEAD_0000 | i)
                    else:
                        await tb.master_read(m, bad)
                    failures.append(f"m{m} {op} to unmapped 0x{bad:08X} answered OKAY")
                except AxiResponseError as e:
                    if e.resp != 2:
                        failures.append(f"m{m} {op} to unmapped 0x{bad:08X}: resp {e.resp}, "
                                        f"expected PSLVERR reported as 2")
            # The port still works: in-range write + read back.
            good = MEM_BASE + 0x2000 + 0x100 * i + 4 * m
            data = 0x600D_0000 | (m << 8) | i
            try:
                await tb.master_write(m, good, data)
                got = await tb.master_read(m, good)
            except AxiResponseError as e:
                failures.append(f"m{m} in-range access after an unmapped one failed: {e}")
                continue
            if got != data:
                failures.append(f"m{m} read back 0x{got:08X} after writing 0x{data:08X} at 0x{good:08X}")
            if tb.slave_mem_read(MEM, good, byte_count=4) != data:
                failures.append(f"m{m}: memory does not hold 0x{data:08X} at 0x{good:08X}")

    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-014 APB PSLVERR PASSED: {2 * n} unmapped accesses per master, "
                f"port recovered every time")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x3_apb_req_prot_user(dut):
    """PPROT reaches AxPROT; the APB5 requester's USER bit reaches the
    AXI5-Lite completer; the APB4 requester's traffic arrives with user 0."""
    tb = Bridge2x3ApbReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = COUNTS[tb.level]

    mem_seen, lregs_seen = [], []
    tb.slave_wr[MEM].aw_channel.add_callback(_record(mem_seen, 'aw'))
    tb.slave_rd[MEM].ar_channel.add_callback(_record(mem_seen, 'ar'))
    tb.slave_wr[LREGS].aw_channel.add_callback(_record(lregs_seen, 'aw'))
    tb.slave_wr[LREGS].w_channel.add_callback(_record(lregs_seen, 'w'))
    tb.slave_rd[LREGS].ar_channel.add_callback(_record(lregs_seen, 'ar'))

    failures = []
    for i in range(n):
        prot = i % 8
        user = i & 1
        # PPROT -> AxPROT at the AXI4 memory, from both requesters.
        for m in (APB4M, APB5M):
            addr = MEM_BASE + 0x3000 + 0x40 * i + 8 * m
            del mem_seen[:]
            apb = tb.master_apb[m]
            wt = await apb.write(addr, 0x9907_0000 | i, pprot=prot)
            rt = await apb.read(addr, pprot=prot)
            if wt.fields.get('pslverr', 0) or rt.fields.get('pslverr', 0):
                failures.append(f"m{m} round {i}: PSLVERR on an in-range access")
            if rt.fields['prdata'] != (0x9907_0000 | i):
                failures.append(f"m{m} round {i}: read 0x{rt.fields['prdata']:08X}, expected 0x{0x9907_0000 | i:08X}")
            aw = [p for k, p in mem_seen if k == 'aw']
            ar = [p for k, p in mem_seen if k == 'ar']
            if len(aw) != 1 or len(ar) != 1:
                failures.append(f"m{m} round {i}: {len(aw)} AW / {len(ar)} AR at mem for one write + one read")
            else:
                if int(aw[0].fields.get('prot', -1)) != prot:
                    failures.append(f"m{m} round {i}: mem saw awprot={aw[0].fields.get('prot')}, drove PPROT={prot}")
                if int(ar[0].fields.get('prot', -1)) != prot:
                    failures.append(f"m{m} round {i}: mem saw arprot={ar[0].fields.get('prot')}, drove PPROT={prot}")

        # USER at the AXI5-Lite completer.
        addr = LREGS_BASE + 0x200 + 4 * i
        del lregs_seen[:]
        await tb.master_apb[APB5M].write(addr, 0x0555_0000 | i, pauser=user, pwuser=user)
        await tb.master_apb[APB5M].read(addr, pauser=user)
        aw = [p for k, p in lregs_seen if k == 'aw']
        w = [p for k, p in lregs_seen if k == 'w']
        ar = [p for k, p in lregs_seen if k == 'ar']
        if len(aw) != 1 or len(w) != 1 or len(ar) != 1:
            failures.append(f"round {i}: APB5 traffic produced {len(aw)} AW / {len(w)} W / {len(ar)} AR at lregs")
        else:
            for pkt, label in ((aw[0], 'aw'), (w[0], 'w'), (ar[0], 'ar')):
                if int(pkt.fields.get('user', 0)) != user:
                    failures.append(f"round {i}: lregs saw {label}user={pkt.fields.get('user')} from apb5m, "
                                    f"drove PAUSER/PWUSER={user}")
        del lregs_seen[:]
        await tb.master_write(APB4M, addr, 0x0444_0000 | i)
        await tb.master_read(APB4M, addr)
        for k, pkt in lregs_seen:
            if int(pkt.fields.get('user', 0)) != 0:
                failures.append(f"round {i}: lregs saw {k}user={pkt.fields.get('user')} from the APB4 requester")

    assert not failures, f"{len(failures)} failure(s):\n  " + "\n  ".join(failures[:20])
    tb.log.info(f"BRIDGE-014 APB prot/user PASSED: {n} rounds")


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x3_apb_req_apb_to_apb(dut):
    """APB in, APB out: both requesters drive the APB4 peripheral (and the
    memory) at the same time; every write lands where it was sent and every
    read returns what it asked for."""
    tb = Bridge2x3ApbReqTB(dut)
    await tb.setup_clocks_and_reset()
    n = {'gate': 8, 'func': 24, 'full': 64}[tb.level]

    plan = []
    for m in (APB4M, APB5M):
        for i in range(n):
            slave = PERIPH if (i & 1) == 0 else MEM
            base = PERIPH_BASE if slave == PERIPH else MEM_BASE + 0x6000
            plan.append((m, slave, base + (m * 0x400) + 4 * i, (0xA0 | m) << 24 | (slave << 16) | i))

    errors, done = [], []

    async def _pair(m, slave, addr, data):
        try:
            await tb.master_write(m, addr, data)
            got = await tb.master_read(m, addr)
            if got != data:
                errors.append(f"m{m} slave {slave} 0x{addr:08X}: read 0x{got:08X}, wrote 0x{data:08X}")
        except Exception as e:  # noqa: BLE001 -- recorded, asserted below
            errors.append(f"m{m} slave {slave} 0x{addr:08X}: {e}")
        done.append(1)

    # One coroutine per requester keeps each APB port strictly one-
    # outstanding (as APB is) while the two ports run against each other.
    async def _stream(m):
        for pm, slave, addr, data in plan:
            if pm == m:
                await _pair(m, slave, addr, data)

    cocotb.start_soon(_stream(APB4M))
    cocotb.start_soon(_stream(APB5M))
    for _ in range(6000):
        if len(done) == len(plan):
            break
        await ClockCycles(tb.clock, 10)
    assert len(done) == len(plan), f"only {len(done)}/{len(plan)} APB transfers completed"
    assert not errors, f"{len(errors)} failure(s):\n  " + "\n  ".join(errors[:10])

    for m, slave, addr, data in plan:
        got = tb.slave_mem_read(slave, addr, byte_count=4)
        assert got == data, f"m{m}: slave {slave} holds 0x{got:08X} at 0x{addr:08X}, expected 0x{data:08X}"
    tb.log.info(f"BRIDGE-014 APB-to-APB PASSED: {len(plan)} write+read pairs across two requesters")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x3_apb_req"
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
        testcase=f"cocotb_test_bridge_2x3_apb_req_{testcase}",
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
def test_bridge_2x3_apb_req_pslverr(request, test_level):
    _run(request, test_level, "pslverr")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x3_apb_req_prot_user(request, test_level):
    _run(request, test_level, "prot_user")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x3_apb_req_apb_to_apb(request, test_level):
    _run(request, test_level, "apb_to_apb")
