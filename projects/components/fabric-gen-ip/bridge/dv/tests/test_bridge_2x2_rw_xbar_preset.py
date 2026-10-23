#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): [bridge] preset = "xbar" on bridge_2x2_rw_xbar,
# the plain-crossbar configuration. The TOML sets nothing but the preset, so
# every value checked here comes from it:
#
#   latency    no registered stage at any port: VALID-to-VALID is 0 cycles
#              master to slave on AW, B, AR and R, for all four pairs
#              (test_bridge_2x2_rw_lat_modes' cpu -> ddr case, everywhere).
#   id_remap   off: the 8-bit master IDs reach the slaves whole, as
#              {master index, ID} -- 9 bits, not {index, 4-bit slot} -- and
#              no bridge_id_remap is built.
#
# The ID phase launches every transaction at once from both masters, through
# both slaves, with IDs drawn from all 256 (so many share low bits, which a
# slot or the per-ID table's index would fold together). A sampler at all
# four ports matches each request to its master by address and checks the
# slave-side ID bit for bit; the BFMs match each response to its request by
# ID, and every word read back is checked against what was written.
#
# Sampling is MID-CYCLE (falling edge), as in test_bridge_2x2_rw_lat_modes:
# the BFMs drive 200 ps after the rising edge, so a rising-edge sample would
# see a one-stage register's output in the same sample as its input.

import os
import random
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_xbar_tb import Bridge2x2RwXbarTB

MASTERS = {0: 'cpu_m_axi_', 1: 'dma_m_axi_'}
SLAVES = {'ddr': ('ddr_s_axi_', 0x00002000), 'sram': ('sram_s_axi_', 0x80002000)}
ID_BITS = 8                      # master id_width; kept whole by the preset
PER_MASTER = {'gate': 24, 'func': 64, 'full': 160}


def _hi(sig):
    try:
        return int(sig.value) == 1
    except ValueError:
        return False


async def _first_rise(tb, sigs, cycles=60):
    """Mid-cycle sampler: the cycle index at which each signal is first 1."""
    seen = {}
    for c in range(cycles):
        await FallingEdge(tb.clock)
        await ReadOnly()
        for name, s in sigs.items():
            if name not in seen and _hi(s):
                seen[name] = c
        if len(seen) == len(sigs):
            break
    return seen


async def _measure(tb, dut, m, slave):
    """(AW, B, AR, R) VALID-to-VALID cycles for one master/slave pair."""
    mp, (sp, addr) = MASTERS[m], SLAVES[slave]
    g = lambda p, n: getattr(dut, f"{p}{n}")

    async def one(kind):
        if kind == 'w':
            sigs = {'m_req': g(mp, 'awvalid'), 's_req': g(sp, 'awvalid'),
                    's_rsp': g(sp, 'bvalid'), 'm_rsp': g(mp, 'bvalid')}
            op = cocotb.start_soon(tb.master_write(m, addr, 0x5EED0000 | m))
        else:
            sigs = {'m_req': g(mp, 'arvalid'), 's_req': g(sp, 'arvalid'),
                    's_rsp': g(sp, 'rvalid'), 'm_rsp': g(mp, 'rvalid')}
            op = cocotb.start_soon(tb.master_read(m, addr))
        seen = await _first_rise(tb, sigs)
        await op
        await ClockCycles(tb.clock, 10)   # idle between measurements
        missing = set(sigs) - set(seen)
        assert not missing, f"{mp}->{sp} {kind}: never saw {sorted(missing)}"
        return seen['s_req'] - seen['m_req'], seen['m_rsp'] - seen['s_rsp']

    aw, b = await one('w')
    ar, r = await one('r')
    return aw, b, ar, r


class IdChecker:
    """Matches every request at a slave port to the master port it left (by
    address: each transaction here has its own) and checks the slave-side ID
    is {master index, the master's own ID}."""

    def __init__(self, tb):
        self.tb, self.dut = tb, tb.dut
        self.errors = []
        self.pending = {'ar': {}, 'aw': {}}      # addr -> (master, id)
        self.checked = 0
        self._task = cocotb.start_soon(self._run())

    def _v(self, p, n):
        return int(getattr(self.dut, f"{p}{n}").value)

    def _arrive(self, ch, fid, addr):
        key = self.pending[ch].pop(addr, None)
        if key is None:
            self.errors.append(f"{ch} at a slave for 0x{addr:08X} never left a master")
            return
        m, mid = key
        want = (m << ID_BITS) | mid
        if fid != want:
            self.errors.append(f"{ch} m{m} id {mid:#04x}: slave saw {fid:#05x}, want {want:#05x}")
        self.checked += 1

    async def _run(self):
        while True:
            await RisingEdge(self.tb.clock)
            for m, p in MASTERS.items():
                for ch in ('ar', 'aw'):
                    if self._v(p, f'{ch}valid') and self._v(p, f'{ch}ready'):
                        self.pending[ch][self._v(p, f'{ch}addr')] = (m, self._v(p, f'{ch}id'))
            for p, _base in SLAVES.values():
                for ch in ('ar', 'aw'):
                    if self._v(p, f'{ch}valid') and self._v(p, f'{ch}ready'):
                        self._arrive(ch, self._v(p, f'{ch}id'), self._v(p, f'{ch}addr'))

    def stop(self):
        self._task.cancel()


async def _wait(tb, futs, what):
    for _ in range(80000):
        if all(f.done() for f in futs):
            return [f.result() for f in futs]
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"{what}: {sum(f.done() for f in futs)}/{len(futs)} completed")


async def _id_phase(tb, rng, n):
    plans = {}
    for m in MASTERS:
        ids = [rng.randrange(1 << ID_BITS) for _ in range(n)]
        plans[m] = [(0x8000_0000 * rng.randrange(2) + 0x4000 * m + 0x40 * k, mid,
                     [rng.getrandbits(32) for _ in range(rng.randint(1, 4))])
                    for k, mid in enumerate(ids)]
    writes = [cocotb.start_soon(tb.master_wr[m].write_transaction(a, d, id=mid, size=2))
              for m, plan in plans.items() for a, mid, d in plan]
    for r in await _wait(tb, writes, "writes"):
        assert r.get('response') == 0, f"write: {r}"
    reads = [(cocotb.start_soon(tb.master_rd[m].read_transaction(a, burst_len=len(d), id=mid, size=2)), a, d)
             for m, plan in plans.items() for a, mid, d in plan]
    await _wait(tb, [f for f, _a, _d in reads], "reads")
    for f, a, d in reads:
        assert list(f.result()) == d, f"read 0x{a:08X} returned other data"
    return {m: {mid for _a, mid, _d in plan} for m, plan in plans.items()}


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_xbar_preset(dut):
    tb = Bridge2x2RwXbarTB(dut)
    await tb.setup_clocks_and_reset()
    assert tb.XBAR_ID_WIDTH == 1 + ID_BITS, \
        f"slave-side IDs are {tb.XBAR_ID_WIDTH} bits; with no remap they should be {{1 index bit, {ID_BITS}-bit ID}}"

    # Latency: zero registered stages on every path.
    tb.set_slave_response_delay(0, 1)
    tb.set_slave_response_delay(1, 1)
    bad = []
    for m in MASTERS:
        for slave in SLAVES:
            meas = await _measure(tb, dut, m, slave)
            tb.log.info(f"LATENCY {MASTERS[m]} -> {slave}: AW/B/AR/R = {meas} (want (0, 0, 0, 0))")
            if meas != (0, 0, 0, 0):
                bad.append(f"{MASTERS[m]} -> {slave}: measured AW/B/AR/R {meas}")
    assert not bad, "preset xbar left a registered stage:\n  " + "\n  ".join(bad)

    # IDs: whole, at the slaves, under load.
    rng = random.Random(int(os.environ.get('SEED', '1')))
    chk = IdChecker(tb)
    ids = await _id_phase(tb, rng, PER_MASTER[tb.level])
    await ClockCycles(tb.clock, 20)
    chk.stop()
    assert not chk.errors, "\n".join(chk.errors[:20])
    assert not chk.pending['ar'] and not chk.pending['aw'], "requests seen at a master never reached a slave"
    n = 2 * len(MASTERS) * PER_MASTER[tb.level]
    assert chk.checked == n, f"checked {chk.checked} slave-side IDs, launched {n}"
    for m, s in ids.items():
        # A 4-bit slot or table index could carry at most 16 values; IDs above
        # that prove the high bits travelled.
        assert any(i >> 4 for i in s), f"m{m}: no ID above 0xF was exercised"
    tb.log.info(f"IDS checked {chk.checked} slave-side IDs, distinct cpu {len(ids[0])} dma {len(ids[1])}")
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_xbar_preset(request, test_level):
    """Pytest wrapper: preset xbar gives wires at every port and whole IDs"""
    module, repo_root_, tests_dir, log_dir, _ = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_xbar"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}_checkers.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{dut_name}_preset_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_2x2_rw_xbar_preset",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': os.path.join(log_dir, f'{name}.log'),
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
            **level_env(test_level),
            **waves['extra_env'],
        },
        keep_files=True,
    )


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
