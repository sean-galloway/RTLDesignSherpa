#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): the read-return atomic tracker depth is a
# per-slave TOML key, atomic_rr_depth (bridge TASK-020), and the bridge stalls
# the (depth + 1)-th read-return atomic at a slave port until an earlier one's
# last R beat frees a slot.
#
# Measured in the ddr slave adapter on its crossbar-side nets: `atom_full` is the tracker's full flag and
# `aw_rr_blocked` the atomic AW it holds back because of it (the hold is inside
# the adapter, upstream of the slave port's pins, so a held AW never shows
# there). Atomic AW handshakes (AWATOP[5] set) minus R-last handshakes on the
# adapter's crossbar side is the tracker's occupancy. The master holds RREADY off while it issues
# sixteen read-return atomics, so R beats back up through the fabric's three
# R skid entries and the slave-side R handshake stalls; the tracker fills and
# holds the next atomic AW:
#   bridge_1x2_rw_axi5a      atomic_rr_depth 8 (default): full at 8 in flight, the ninth held
#   bridge_1x2_rw_axi5a_rr2  atomic_rr_depth 2:           full at 2, the third held
# The depth each fixture was built with is read from <bridge>_sizing.json. Once
# RREADY is released every atomic completes and returns the word's prior value.
import json
import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb                                                       # noqa: E402
from cocotb.triggers import ClockCycles, RisingEdge                 # noqa: E402
from cocotb_test.simulator import run                               # noqa: E402
from TBClasses.shared.utilities import get_paths, get_wave_config   # noqa: E402
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402
from TBClasses.shared.test_levels import level_env, reg_level_grid  # noqa: E402

from bridge1x2_rw_axi5a_tb import Bridge1x2RwAxi5aTB                # noqa: E402
from bridge1x2_rw_axi5a_rr2_tb import Bridge1x2RwAxi5aRr2TB         # noqa: E402

FIXTURES = {'bridge_1x2_rw_axi5a': Bridge1x2RwAxi5aTB, 'bridge_1x2_rw_axi5a_rr2': Bridge1x2RwAxi5aRr2TB}
FIXTURE = os.environ.get('BRIDGE_RR_FIXTURE', 'bridge_1x2_rw_axi5a')
ATOP_LOAD_ADD = 0b100000
N_ATOMICS = 16                  # the master's outstanding limit: more than the default depth (8) plus the
                                # R beats the fabric buffers between the slave port and the master's
                                # held RREADY (about six: the two adapters' and the crossbar's skids),
                                # so the tracker fills on both fixtures
DDR_BASE = 0x0000_1000


def _depth():
    p = os.path.join(repo_root, 'projects/components/fabric-gen-ip/bridge/rtl/generated',
                     FIXTURE, f'{FIXTURE}_sizing.json')
    with open(p) as fh:
        rows = json.load(fh)['ports']
    return next(r['value'] for r in rows if r['key'] == 'atomic_rr_depth' and r['port'] == 'ddr')


class Occupancy:
    """Atomic AWs accepted minus atomic R-lasts returned at the ddr slave port."""
    def __init__(self, tb):
        a = tb.dut.u_ddr_adapter
        self.tb = tb
        # the tracker allocates at the adapter's crossbar-side AW handshake and
        # releases at its crossbar-side R-last handshake (the pins sit behind the
        # adapter's own skids), so the occupancy is counted on those nets
        self.awv, self.awr, self.atop = a.xbar_ddr_axi_awvalid, a.xbar_ddr_axi_awready, a.xbar_ddr_axi_awatop
        self.rv, self.rr, self.rl = a.xbar_ddr_axi_rvalid, a.xbar_ddr_axi_rready, a.xbar_ddr_axi_rlast
        self.full, self.blocked = a.atom_full, a.aw_rr_blocked
        self.live = self.peak = self.accepted = 0
        self.stalled_full = 0        # cycles the adapter held an atomic AW because the tracker was full
        self.live_at_full = None     # occupancy the first cycle the tracker reported full
        self.depth = None

    async def run(self):
        while True:
            await RisingEdge(self.tb.clock)
            try:
                aw = int(self.awv.value) and int(self.awr.value) and (int(self.atop.value) >> 5) & 1
                aw_wait = int(self.awv.value) and not int(self.awr.value) and (int(self.atop.value) >> 5) & 1
                rl = int(self.rv.value) and int(self.rr.value) and int(self.rl.value)
            except ValueError:
                continue
            try:
                full, blocked = int(self.full.value), int(self.blocked.value)
            except ValueError:
                full = blocked = 0
            if full and self.live_at_full is None:
                self.live_at_full = self.live
            if blocked:
                self.stalled_full += 1
            self.live += int(bool(aw)) - int(bool(rl))
            self.accepted += int(bool(aw))
            self.peak = max(self.peak, self.live)


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_rr_depth(dut):
    tb = FIXTURES[FIXTURE](dut)
    await tb.setup_clocks_and_reset()
    depth = _depth()
    occ = Occupancy(tb)
    occ.depth = depth
    cocotb.start_soon(occ.run())
    wr, rd = tb.master_wr[0], tb.master_rd[0]
    # seed the words and remember them: an AtomicLoad ADD returns the prior value
    words = [DDR_BASE + 4 * k for k in range(N_ATOMICS)]
    for k, a in enumerate(words):
        res = await wr.write_transaction(a, [0x1000 + k], size=2, id=15)
        assert not (isinstance(res, dict) and not res.get('success', True)), res
    # hold the master's RREADY off (the driver's runtime ready policy), then
    # issue every atomic at once; the BFM waits are raised well past the hold
    for bfm in (wr, rd):
        bfm.timeout_cycles = max(getattr(bfm, 'timeout_cycles', 0), 200_000)
        for ch in ('aw_channel', 'w_channel', 'ar_channel'):
            drv = getattr(bfm, ch, None)
            if drv is not None:
                drv.timeout_cycles = max(getattr(drv, 'timeout_cycles', 0), 200_000)
    rd.r_channel.ready_policy = 'stall'
    futs = [cocotb.start_soon(wr.atomic_operation(a, 1, ATOP_LOAD_ADD, read_channel=rd, size=2, id=k))
            for k, a in enumerate(words)]
    # wait until every atomic AW the tracker will take has been accepted
    for _ in range(600):
        await ClockCycles(tb.clock, 5)
        if occ.peak >= depth and occ.stalled_full >= 50:
            break
    peak_held, stalled_held = occ.peak, occ.stalled_full
    live_at_full = occ.live_at_full
    tb.log.info(f"{FIXTURE}: atomic_rr_depth {depth}; with RREADY held: {occ.accepted} atomic AWs accepted, "
                f"peak in flight {peak_held}, tracker full first at {live_at_full} in flight, "
                f"{stalled_held} cycles the adapter held an atomic AW at the full tracker")
    # release R; everything completes with the prior values
    rd.r_channel.ready_policy = 'valid_first'
    for _ in range(4000):
        if all(f.done() for f in futs):
            break
        await ClockCycles(tb.clock, 5)
    assert all(f.done() for f in futs), "atomics did not complete after RREADY was released"
    for k, f in enumerate(futs):
        r = f.result()
        assert r.get('response', 0) == 0 and r.get('read_resp', 0) == 0, f"atomic {k}: {r}"
        got = r.get('read_return', {}).get('data', r.get('read_data'))
        assert got == 0x1000 + k, f"atomic {k} returned {got:#x}, seeded {0x1000 + k:#x}"
    for k, a in enumerate(words):
        v = await rd.read_transaction(a, burst_len=1, size=2, id=14)
        v = v[0]['data'] if isinstance(v[0], dict) else v[0]
        assert v == 0x1000 + k + 1, f"word {k} after the add: {v:#x}"
    # the limit, both ways: the tracker filled to its depth and not past it,
    # and an atomic AW waited at the full tracker when more were offered
    assert live_at_full == depth, (
        f"{FIXTURE}: the tracker reported full at {live_at_full} read-return atomics in flight; "
        f"atomic_rr_depth is {depth}")
    assert peak_held <= depth, f"{FIXTURE}: {peak_held} in flight exceeds atomic_rr_depth {depth}"
    assert stalled_held > 0, f"{FIXTURE}: the tracker filled to {depth} but the adapter never held an atomic AW"
    tb.assert_compliance()


def _run(request, test_level, fixture):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{fixture}.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{fixture}_rr_depth_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=fixture, module=module, testcase="cocotb_test_bridge_rr_depth",
        sim_build=sim_build, waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        extra_env={'COCOTB_LOG_LEVEL': 'INFO', 'LOG_PATH': log_path,
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
                   'BRIDGE_RR_FIXTURE': fixture, **level_env(test_level), **waves['extra_env']},
        plus_args=waves['sim_args'], keep_files=True)


@pytest.mark.parametrize("fixture", sorted(FIXTURES))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_rr_depth(request, test_level, fixture):
    _run(request, test_level, fixture)
