#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): transaction-ID remap (bridge_id_remap), on
# bridge_2x2_rw.
#
# cpu and dma have 8-bit IDs and 16 outstanding per direction, so each master
# adapter remaps its IDs to 4-bit slots: the fabric ID at the slaves is
# {master index, slot}, 5 bits, and the slot in a response restores the ID.
# Both masters at once, through both slaves (which interleave R):
#
#   many   every transaction a different ID, three times as many as there
#          are slots, all launched together: slots fill, free and are reused
#          for other IDs, both directions.
#   same   runs of one ID to one slave: one ID must keep one slot while it
#          has requests in flight, so its responses stay in order.
#
# Every word is checked against what was written, the masters' BFMs match
# every response to its request by ID, and a sampler at all four ports checks
# the mapping itself: while a fabric ID is in flight at a slave it belongs to
# exactly one master ID, and a master ID in flight has exactly one fabric ID.

import os
import random
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

from bridge2x2_rw_tb import Bridge2x2RwTB

MASTERS = {0: 'cpu_m_axi_', 1: 'dma_m_axi_'}
SLAVES = {0: 'ddr_s_axi_', 1: 'sram_s_axi_'}
SLOTS = 16                       # max_outstanding: 4-bit slots
SLOT_BITS = 4
ROUNDS = {'gate': 1, 'func': 3, 'full': 8}


class RemapChecker:
    """Follows every request from its master port to its slave port (by
    address: each transaction here has its own) and checks the ID mapping
    while it is in flight, per direction."""

    def __init__(self, tb):
        self.tb, self.dut = tb, tb.dut
        self.errors = []
        self.slots_seen = {m: set() for m in MASTERS}
        self.ids_seen = {m: set() for m in MASTERS}
        # per direction: addr -> (master, master id), issued at a master port
        self.pending = {'ar': {}, 'aw': {}}
        # per direction: fabric id -> [master id, count in flight]
        self.live_f = {'ar': {}, 'aw': {}}
        # per direction: (master, master id) -> [fabric id, count]
        self.live_m = {'ar': {}, 'aw': {}}
        self._task = cocotb.start_soon(self._run())

    def _v(self, p, n):
        return int(getattr(self.dut, f"{p}{n}").value)

    def _issue(self, ch, fid, addr):
        key = self.pending[ch].pop(addr, None)
        if key is None:
            self.errors.append(f"{ch} at a slave for 0x{addr:08X} never left a master")
            return
        m, mid = key
        if (fid >> SLOT_BITS) != m:
            self.errors.append(f"{ch} m{m} id {mid:#x}: fabric id {fid:#x} names master {fid >> SLOT_BITS}")
        self.slots_seen[m].add(fid & (SLOTS - 1))
        self.ids_seen[m].add(mid)
        lf = self.live_f[ch].setdefault(fid, [mid, 0])
        if lf[1] and lf[0] != mid:
            self.errors.append(f"{ch} fabric id {fid:#x} in flight for m{m} id {lf[0]:#x} "
                               f"was given to id {mid:#x}")
        lf[0] = mid
        lf[1] += 1
        lm = self.live_m[ch].setdefault((m, mid), [fid, 0])
        if lm[1] and lm[0] != fid:
            self.errors.append(f"{ch} m{m} id {mid:#x} in flight as {lm[0]:#x} was sent as {fid:#x}")
        lm[0] = fid
        lm[1] += 1

    def _retire(self, ch, fid):
        lf = self.live_f[ch].get(fid)
        if not lf or lf[1] == 0:
            self.errors.append(f"{ch} response for fabric id {fid:#x} with nothing in flight")
            return
        lf[1] -= 1
        m = fid >> SLOT_BITS
        self.live_m[ch][(m, lf[0])][1] -= 1

    async def _run(self):
        while True:
            await RisingEdge(self.tb.clock)
            for m, p in MASTERS.items():
                if self._v(p, 'arvalid') and self._v(p, 'arready'):
                    self.pending['ar'][self._v(p, 'araddr')] = (m, self._v(p, 'arid'))
                if self._v(p, 'awvalid') and self._v(p, 'awready'):
                    self.pending['aw'][self._v(p, 'awaddr')] = (m, self._v(p, 'awid'))
            for p in SLAVES.values():
                if self._v(p, 'arvalid') and self._v(p, 'arready'):
                    self._issue('ar', self._v(p, 'arid'), self._v(p, 'araddr'))
                if self._v(p, 'awvalid') and self._v(p, 'awready'):
                    self._issue('aw', self._v(p, 'awid'), self._v(p, 'awaddr'))
                if self._v(p, 'rvalid') and self._v(p, 'rready') and self._v(p, 'rlast'):
                    self._retire('ar', self._v(p, 'rid'))
                if self._v(p, 'bvalid') and self._v(p, 'bready'):
                    self._retire('aw', self._v(p, 'bid'))

    def stop(self):
        self._task.cancel()


async def _wait(tb, futs, what):
    for _ in range(80000):
        if all(f.done() for f in futs):
            return [f.result() for f in futs]
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"{what}: {sum(f.done() for f in futs)}/{len(futs)} completed")


def _plan(rng, m, region, ids, same_runs):
    """[(addr, slave, id, words)] for master m. `same_runs`: consecutive
    entries share one ID and one slave."""
    plan = []
    for k, mid in enumerate(ids):
        s = (k // same_runs) % 2 if same_runs > 1 else rng.randrange(2)
        addr = 0x8000_0000 * s + region + 0x4000 * m + 0x40 * k
        beats = rng.randint(1, 4)
        plan.append((addr, s, mid, [rng.getrandbits(32) for _ in range(beats)]))
    return plan


async def _run_phase(tb, rng, region, same_runs, n):
    plans = {}
    for m in MASTERS:
        if same_runs > 1:
            run_ids = rng.sample(range(256), n // same_runs)
            ids = [i for i in run_ids for _ in range(same_runs)]
        else:
            ids = rng.sample(range(256), n)
        plans[m] = _plan(rng, m, region, ids, same_runs)
    writes = [cocotb.start_soon(tb.master_wr[m].write_transaction(a, d, id=mid, size=2))
              for m, plan in plans.items() for a, _s, mid, d in plan]
    for r in await _wait(tb, writes, "writes"):
        assert r.get('response') == 0, f"write: {r}"
    reads = [(cocotb.start_soon(tb.master_rd[m].read_transaction(a, burst_len=len(d), id=mid, size=2)), a, d)
             for m, plan in plans.items() for a, _s, mid, d in plan]
    await _wait(tb, [f for f, _a, _d in reads], "reads")
    for f, a, d in reads:
        assert list(f.result()) == d, f"read 0x{a:08X} returned other data"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_id_remap(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    assert tb.XBAR_ID_WIDTH == 1 + SLOT_BITS, \
        f"slave-side IDs are {tb.XBAR_ID_WIDTH} bits; the remap should give {{1 index bit, {SLOT_BITS}-bit slot}}"
    rng = random.Random(int(os.environ.get('SEED', '1')))
    chk = RemapChecker(tb)
    n = 3 * SLOTS
    for r in range(ROUNDS[tb.level]):
        region = 0x8000 * (r % 2)       # the slave memory models hold 64 KB
        await _run_phase(tb, rng, region, 1, n)          # many
        await _run_phase(tb, rng, region + 0x2000, 4, n)  # same
        tb.log.info(f"round {r}: slots used cpu {len(chk.slots_seen[0])} dma {len(chk.slots_seen[1])}, "
                    f"ids cpu {len(chk.ids_seen[0])} dma {len(chk.ids_seen[1])}")
    await ClockCycles(tb.clock, 20)
    chk.stop()
    assert not chk.errors, "\n".join(chk.errors[:20])
    assert not chk.pending['ar'] and not chk.pending['aw'], "requests seen at a master never reached a slave"
    for m in MASTERS:
        assert len(chk.ids_seen[m]) > SLOTS, f"m{m}: only {len(chk.ids_seen[m])} IDs; slots never had to recycle"
        # A miss takes the LOWEST free slot, so the top slots are used only
        # when the table is nearly full; half of them is proof enough that
        # slots were handed out beyond the first few, without tying the test
        # to how far a seed's traffic happens to fill the table.
        assert len(chk.slots_seen[m]) >= SLOTS // 2, \
            f"m{m}: only slots {sorted(chk.slots_seen[m])} were used"
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_id_remap(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}_checkers.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_id_remap_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_rw_id_remap",
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
