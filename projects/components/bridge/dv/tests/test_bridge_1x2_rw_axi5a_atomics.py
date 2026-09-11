#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-3b sign-off test.
#
# Read-return atomics through the fabric, end to end. On this rw fixture the
# master has no boundary filter: AtomicLoad/Swap/Compare ride the AW path
# to the slave, the slave BFM performs the operation on its memory model, the
# location's ORIGINAL data comes back on the R channel with the AW's ID, and
# the master BFM collects it. Every step is checked against an independent
# model of what the memory should hold:
#   - the returned R data is the pre-operation value;
#   - the slave memory holds the post-operation value;
#   - a plain read afterwards agrees with the memory model;
#   - store-class atomics answer on B only and still update memory;
#   - AtomicCompare swaps on match and leaves memory alone on mismatch;
#   - both slaves, so the R routing is by slave and by ID, not by luck;
#   - a concurrency phase where reads and atomics are in flight together,
#     which is the case the AR->R tracker's dual push and the slave-side
#     per-ID tracker exist for;
#   - an OUT-OF-RANGE read-return atomic. Nothing owns 0xC000_0000 and up on
#     this fixture, so the AW lands on the subtractive slave, which answers
#     DECERR on B and knows nothing about R. Without the master adapter's
#     local answer that R beat never comes and, because the port's R-return
#     tracker is holding a slot for it, every later read on the port is
#     blocked behind it (the shape of BRIDGE-009, on the atomic path). The
#     master must see DECERR on BOTH B and R, and the port must still work.
# The AXI5 compliance checker on the master port is armed throughout; it
# knows a read-return atomic is an outstanding read and flags an R beat
# nobody requested, so a misrouted return cannot pass silently.

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

from projects.components.bridge.dv.tbclasses.bridge1x2_rw_axi5a_tb import (
    Bridge1x2RwAxi5aTB,
)

# AWATOP[5:4] class, [3] endianness, [2:0] op (ADD CLR EOR SET SMAX SMIN UMAX UMIN)
ATOP_STORE_ADD = 0b010000
ATOP_LOAD_ADD = 0b100000
ATOP_LOAD_SET = 0b100011
ATOP_LOAD_UMAX = 0b100110
ATOP_SWAP = 0b110000
ATOP_COMPARE = 0b110001

MASK32 = 0xFFFF_FFFF


class AtomicSampler:
    """Slave-side AW atop per handshake (per slave), and every master-side
    B (id, resp) and R (id, resp, data) beat."""

    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.slave_aw = {'ddr': [], 'sram': []}
        self.master_b = []
        self.master_r = []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            for s in ('ddr', 'sram'):
                if int(getattr(d, f"{s}_axi_awvalid").value) and int(getattr(d, f"{s}_axi_awready").value):
                    self.slave_aw[s].append(int(getattr(d, f"{s}_axi_awatop").value))
            if int(d.cpu_axi_bvalid.value) and int(d.cpu_axi_bready.value):
                self.master_b.append((int(d.cpu_axi_bid.value), int(d.cpu_axi_bresp.value)))
            if int(d.cpu_axi_rvalid.value) and int(d.cpu_axi_rready.value):
                self.master_r.append((int(d.cpu_axi_rid.value), int(d.cpu_axi_rresp.value),
                                      int(d.cpu_axi_rdata.value)))


async def _atomic_round(tb, wr, rd, slave_idx, base, expect):
    """One sequence of atomics on one 32-bit word, checked step by step.
    `expect` collects the addresses whose final value is known."""
    addr = base + 0x100
    mem = lambda: tb.slave_mem_read(slave_idx, addr, master_idx=0)

    # Seed the word with a plain write.
    r = await wr.write_transaction(addr, 0x0000_0010, size=2, id=1)
    assert r.get('response') == 0, f"seed write: {r}"
    assert mem() == 0x10

    # AtomicLoad ADD: returns the old value on R, memory becomes old + operand.
    r = await wr.atomic_operation(addr, 5, ATOP_LOAD_ADD, read_channel=rd, size=2, id=2)
    assert r.get('response') == 0, f"AtomicLoad ADD B: {r}"
    assert r.get('read_resp') == 0 and r.get('read_data') == 0x10, (
        f"AtomicLoad ADD must return the ORIGINAL value 0x10 on R: {r}")
    assert mem() == 0x15, f"memory after AtomicLoad ADD: {mem():#x}"

    # AtomicStore ADD: B only, no R return, memory still updated.
    r = await wr.atomic_operation(addr, 3, ATOP_STORE_ADD, read_channel=rd, size=2, id=3)
    assert r.get('response') == 0 and 'read_data' not in r, f"AtomicStore: {r}"
    assert mem() == 0x18, f"memory after AtomicStore ADD: {mem():#x}"

    # AtomicLoad SET and UMAX: bitwise then arithmetic, endianness-neutral
    # and little-endian respectively.
    r = await wr.atomic_operation(addr, 0x0000_0100, ATOP_LOAD_SET, read_channel=rd, size=2, id=4)
    assert r.get('read_data') == 0x18 and mem() == 0x118, f"AtomicLoad SET: {r} mem={mem():#x}"
    r = await wr.atomic_operation(addr, 0x0000_0050, ATOP_LOAD_UMAX, read_channel=rd, size=2, id=5)
    assert r.get('read_data') == 0x118 and mem() == 0x118, f"AtomicLoad UMAX (no change): {r} mem={mem():#x}"

    # AtomicSwap: returns old, memory takes the operand.
    r = await wr.atomic_operation(addr, 0xCAFE_0000, ATOP_SWAP, read_channel=rd, size=2, id=6)
    assert r.get('read_data') == 0x118, f"AtomicSwap must return 0x118: {r}"
    assert mem() == 0xCAFE_0000, f"memory after AtomicSwap: {mem():#x}"

    # AtomicCompare on the low half-word (beat = compare | swap << 16).
    # Match: low half is 0x0000 -> swapped to 0xBEEF.
    r = await wr.atomic_operation(addr, (0xBEEF << 16) | 0x0000, ATOP_COMPARE,
                                  read_channel=rd, size=2, id=7)
    assert (r.get('read_data') & 0xFFFF) == 0x0000, f"AtomicCompare (match) return: {r}"
    assert mem() == 0xCAFE_BEEF, f"memory after matching AtomicCompare: {mem():#x}"
    # Mismatch: compare 0x1234 != 0xBEEF -> memory untouched, old returned.
    r = await wr.atomic_operation(addr, (0x0000 << 16) | 0x1234, ATOP_COMPARE,
                                  read_channel=rd, size=2, id=8)
    assert (r.get('read_data') & 0xFFFF) == 0xBEEF, f"AtomicCompare (mismatch) return: {r}"
    assert mem() == 0xCAFE_BEEF, f"memory after failed AtomicCompare: {mem():#x}"

    # A plain read through the fabric agrees with the memory model.
    got = await tb.master_read(0, addr)
    assert got == 0xCAFE_BEEF, f"plain read after atomics: {got:#x}"
    expect[(slave_idx, addr)] = 0xCAFE_BEEF


async def _concurrency_phase(tb, wr, rd, base_a, base_b, n):
    """Reads and read-return atomics in flight together, across both slaves
    and on the same slave, all with distinct IDs. Each result is checked
    against what the memory model says the value was BEFORE the atomic."""
    # Seed n words on each slave.
    seeds = {}
    for i in range(n):
        for base in (base_a, base_b):
            a = base + 0x200 + 4 * i
            v = (0x5A00_0000 | (i << 8) | (1 if base == base_a else 2)) & MASK32
            r = await wr.write_transaction(a, v, size=2, id=1)
            assert r.get('response') == 0
            seeds[a] = v

    async def atomic(a, operand, txn_id):
        return a, await wr.atomic_operation(a, operand, ATOP_LOAD_ADD, read_channel=rd,
                                             size=2, id=txn_id)

    async def read(a, txn_id):
        resp = await rd.read_transaction(a, burst_len=1, id=txn_id)
        return a, resp[0]['data']

    # AXI5 forbids an atomic from sharing its ID with any outstanding
    # transaction from the same Manager, and the read BFM keys its response
    # queue on ID, so every transaction in flight at once needs a distinct
    # ID. With a 4-bit ID and 4 transactions per word, three words (12 IDs,
    # 2..13) can be in flight together; the phase runs in batches of three
    # and awaits each batch before reusing an ID. The first version of this
    # phase rotated IDs freely and, at full depth, issued a word's four
    # transactions with the IDs a still-outstanding word was using.
    ids = list(range(2, 14))
    results = []
    for first in range(0, n, 3):
        tasks = []
        k = 0
        for i in range(first, min(first + 3, n)):
            a_addr = base_a + 0x200 + 4 * i
            b_addr = base_b + 0x200 + 4 * i
            tasks.append(('atomic', cocotb.start_soon(atomic(a_addr, 1, ids[k])))); k += 1
            tasks.append(('read',   cocotb.start_soon(read(b_addr, ids[k])))); k += 1
            tasks.append(('atomic', cocotb.start_soon(atomic(b_addr, 2, ids[k])))); k += 1
            tasks.append(('read',   cocotb.start_soon(read(a_addr, ids[k])))); k += 1
        results += [(kind, await t) for kind, t in tasks]

    # Each word receives exactly ONE atomic add: +1 on slave A's words, +2 on
    # slave B's. So an atomic must return the seed, a concurrent read may see
    # the seed or the seed plus that one add, and the final memory is exact.
    def delta(a):
        return 1 if a < 0x8000_0000 else 2

    for kind, (a, res) in results:
        if kind == 'atomic':
            assert res.get('response') == 0 and res.get('read_resp') == 0, f"atomic @{a:#x}: {res}"
            assert res['read_data'] == seeds[a], (
                f"atomic @{a:#x} returned {res['read_data']:#x}; the word's original value "
                f"was {seeds[a]:#x} and it received no other write")
        else:
            legal = {seeds[a], (seeds[a] + delta(a)) & MASK32}
            assert res in legal, (
                f"read @{a:#x} saw {res:#x}, not a value the word ever held "
                f"{sorted(hex(v) for v in legal)}")
    for a, v in seeds.items():
        slave_idx = 0 if a < 0x8000_0000 else 1
        want = (v + delta(a)) & MASK32
        got = tb.slave_mem_read(slave_idx, a, master_idx=0)
        assert got == want, f"final @{a:#x}: {got:#x} != {want:#x}"


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rw_axi5a_atomics(dut):
    """Read-return atomics forward natively and their R data routes back."""
    tb = Bridge1x2RwAxi5aTB(dut)
    await tb.setup_clocks_and_reset()

    sampler = AtomicSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    wr, rd = tb.master_wr[0], tb.master_rd[0]
    rounds = max(1, tb.level_cfg['sideband_beats'] // 3)
    tb.log.info("=" * 80)
    tb.log.info(f"A5-3b sign-off: read-return atomics, level={tb.level}, {rounds} round(s)")
    tb.log.info("=" * 80)

    expect = {}
    rr_issued = 0
    for r in range(rounds):
        for slave_idx, base in ((0, 0x0000_0000 + r * 0x1000), (1, 0x8000_0000 + r * 0x1000)):
            await _atomic_round(tb, wr, rd, slave_idx, base, expect)
            rr_issued += 6      # load add, load set, load umax, swap, compare x2

    n = max(2, rounds)
    await _concurrency_phase(tb, wr, rd, 0x0000_0000 + rounds * 0x1000,
                             0x8000_0000 + rounds * 0x1000, n)
    rr_issued += 2 * n

    # Out-of-range read-return atomic: answered, not wedged.
    oor = 0xC000_0000 + rounds * 0x1000
    r = await wr.atomic_operation(oor, 1, ATOP_LOAD_ADD, read_channel=rd, size=2, id=14)
    assert r.get('response') == 3, f"OOR atomic B must be DECERR: {r}"
    assert r.get('read_resp') == 3, (
        f"OOR atomic R must be DECERR (the R beat arrived, so the port is not "
        f"wedged, but it must carry the error): {r}")
    # The port still works afterwards: a plain read and an in-range atomic.
    got = await tb.master_read(0, 0x0000_0100)
    assert got == expect[(0, 0x0000_0100)], f"read after OOR atomic: {got:#x}"
    r = await wr.atomic_operation(0x8000_0100, 0, ATOP_LOAD_ADD, read_channel=rd, size=2, id=15)
    assert r.get('response') == 0 and r.get('read_data') == expect[(1, 0x8000_0100)], (
        f"in-range atomic after the OOR one: {r}")
    # The OOR AW reached no data slave. (It counts as issued but not routed
    # to a slave, so the slave-side tally below excludes it.)

    await ClockCycles(tb.clock, 50)

    # Every in-range read-return atomic reached a slave with AWATOP[5] set
    # (the two after the OOR one included) ...
    rr_issued += 1
    rr_at_slaves = sum(1 for s in sampler.slave_aw.values() for a in s if a & 0x20)
    assert rr_at_slaves == rr_issued, (
        f"{rr_issued} read-return atomics issued, {rr_at_slaves} seen at the slaves' AW; "
        f"ddr={[bin(a) for a in sampler.slave_aw['ddr']]} sram={[bin(a) for a in sampler.slave_aw['sram']]}")
    # ... and exactly one B was non-OKAY at the master: the OOR atomic's DECERR.
    bad_b = [(i, resp) for i, resp in sampler.master_b if resp]
    assert bad_b == [(14, 3)], f"non-OKAY B at the master: {bad_b} (expected only the OOR atomic, id 14)"
    bad_r = [(i, resp) for i, resp, _d in sampler.master_r if resp]
    assert bad_r == [(14, 3)], f"non-OKAY R at the master: {bad_r} (expected only the OOR atomic, id 14)"

    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info(f"A5-3b atomics test PASSED ({rr_issued} read-return atomics routed, "
                f"{len(sampler.master_r)} R beats at the master)")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rw_axi5a_atomics(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rw_axi5a"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rw_axi5a.f'
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
        testcase="cocotb_test_bridge_1x2_rw_axi5a_atomics",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        extra_env=extra_env,
        plus_args=waves['sim_args'],
        keep_files=True,
    )
