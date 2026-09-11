#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-017 performance characterization.
#
# The HAS performance chapter quotes "DATA_WIDTH per cycle" peak throughput
# and "Peak / N" per-master scaling as formulas; until this file nothing in
# the suite measured a beat rate, so those figures described what a crossbar
# ought to do, not what this one does. Each phase here drives SATURATING
# traffic (every BFM channel back-to-back, no randomized gaps -- random
# timing leaves holes and a hole is a measurement of the stimulus, not the
# fabric), measures over ITS OWN WINDOW (first to last beat at the port
# under measurement), and asserts a floor on the figure it logs, so the
# table in the HAS cannot age silently:
#
#   write_stream   one master streaming 16-beat write bursts to one slave:
#                  W beats per cycle at the slave port, and the loaded
#                  AW-accept -> BVALID latency at the master;
#   read_stream    the same for reads: R beats per cycle at the master port;
#   contention     both masters streaming to ONE slave: the slave port stays
#                  saturated and each master gets its share -- asserted per
#                  master, since an aggregate cannot see one master starved;
#   parallel       each master streaming to its own slave: two beats per
#                  cycle across the fabric, neither path slowed by the other.
#
# Fixture: bridge_2x2_rw (two 32-bit AXI4 masters, two 32-bit AXI4 slaves,
# no width or protocol conversion), so the figures are the fabric's own.

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

from projects.components.bridge.dv.tbclasses.bridge2x2_rw_tb import Bridge2x2RwTB
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

CPU, DMA = 0, 1
DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
BEATS = 16                                   # beats per burst
BURSTS = {'gate': 8, 'func': 32, 'full': 128}   # bursts per master per phase

MASTER_PFX = {CPU: 'cpu_m_axi', DMA: 'dma_m_axi'}
SLAVE_PFX = {DDR: 'ddr_s_axi', SRAM: 'sram_s_axi'}

# Floors, from the first measured run (2026-09-11) with a small margin. They
# are ASSERTED so a pipeline change that costs bandwidth fails here rather
# than ageing the HAS table; raise them if the fabric improves, never lower
# them to pass (handbook: measure-over-the-window).
FLOOR = {
    'write_stream_beats_per_cycle': 0.85,      # measured 0.90 (gate) -- see the HAS note
    'read_stream_beats_per_cycle': 0.95,       # measured 1.00
    'contention_total_beats_per_cycle': 0.95,  # measured 1.00
    'contention_min_share': 0.40,              # measured 0.475
    'parallel_total_beats_per_cycle': 1.70,    # measured 1.80
}

BACK_TO_BACK_VALID = {'valid_delay': ([(0, 0)], [1])}
BACK_TO_BACK_READY = {'ready_delay': ([(0, 0)], [1])}


def _hi(sig):
    try:
        return int(sig.value) == 1
    except ValueError:
        return False


def saturate(tb):
    """Every BFM channel back-to-back: masters present VALID immediately,
    slaves answer READY immediately and stream responses without gaps."""
    for bfm in tb.master_wr.values():
        bfm.aw_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.w_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.b_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
    for bfm in tb.master_rd.values():
        bfm.ar_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.r_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
    for bfm in tb.slave_wr.values():
        bfm.aw_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.w_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.b_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.response_delay_cycles = 0
    for bfm in tb.slave_rd.values():
        bfm.ar_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.r_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.response_delay_cycles = 0


class Sampler:
    """One coroutine samples every handshake of interest once per cycle.

    Records, per named channel, the cycle number of each handshake. Windows
    are derived from the record afterwards, never from cumulative counters.
    """

    def __init__(self, tb, channels):
        self.tb = tb
        self.dut = tb.dut
        self.channels = {name: (getattr(self.dut, f"{pfx}_{ch}valid"),
                                getattr(self.dut, f"{pfx}_{ch}ready"))
                         for name, (pfx, ch) in channels.items()}
        self.marks = {name: [] for name in channels}
        # Per channel: cycles VALID was high without READY (the far side
        # stalled) and cycles VALID was low (the near side had nothing to
        # offer). Over a window they say who owns a gap.
        self.stalled = {name: [] for name in channels}
        self.idle = {name: [] for name in channels}
        self.cycle = 0
        self.alive = False

    async def run(self):
        self.alive = True
        while True:
            # Sample AT the edge: the values read here are the ones the flops
            # capture on this edge. Sampling in ReadOnly after it sees the
            # post-edge state and misses every one-cycle handshake -- the
            # first cut lost exactly one W beat per burst that way.
            await RisingEdge(self.tb.clock)
            self.cycle += 1
            for name, (v, r) in self.channels.items():
                hv, hr = _hi(v), _hi(r)
                if hv and hr:
                    self.marks[name].append(self.cycle)
                elif hv:
                    self.stalled[name].append(self.cycle)
                else:
                    self.idle[name].append(self.cycle)

    def window_rate(self, name):
        """(beats, cycles, beats/cycle) from the first to the last handshake."""
        m = self.marks[name]
        if len(m) < 2:
            return len(m), 0, 0.0
        cycles = m[-1] - m[0] + 1
        return len(m), cycles, len(m) / cycles

    def count_in(self, name, lo, hi):
        return sum(1 for c in self.marks[name] if lo <= c <= hi)

    def gaps_in(self, name, lo, hi):
        """(stalled cycles, idle cycles) of a channel inside a window."""
        return (sum(1 for c in self.stalled[name] if lo <= c <= hi),
                sum(1 for c in self.idle[name] if lo <= c <= hi))


def _write_plan(master, slave_base, n, tag):
    # Inside the slave's 64 KB seeded model (SLAVE_MEM_CAP_BYTES): each master
    # owns a 32 KB half; 128 bursts x 64 bytes = 8 KB of it.
    return [(master, slave_base + 0x8000 * master + i * BEATS * 4,
             [(tag << 24) | (master << 16) | (i << 4) | k for k in range(BEATS)])
            for i in range(n)]


async def _stream_writes(tb, plan, errors):
    """Issue every burst of the plan concurrently (ids rotate) and wait."""
    done = []

    async def _one(m, addr, data, txn_id):
        res = await tb.master_wr[m].write_transaction(addr, data, id=txn_id, size=2)
        if isinstance(res, dict) and not res.get('success', True):
            errors.append(f"m{m} write @0x{addr:08X}: {res}")
        done.append(1)

    for i, (m, addr, data) in enumerate(plan):
        cocotb.start_soon(_one(m, addr, data, i % 16))
    for _ in range(20000):
        if len(done) == len(plan):
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"only {len(done)}/{len(plan)} write bursts completed")


async def _stream_reads(tb, plan, errors):
    done = []

    async def _one(m, addr, data, txn_id):
        got = await tb.master_rd[m].read_transaction(addr, burst_len=BEATS, id=txn_id, size=2)
        if list(got) != data:
            errors.append(f"m{m} read @0x{addr:08X}: data mismatch")
        done.append(1)

    for i, (m, addr, data) in enumerate(plan):
        cocotb.start_soon(_one(m, addr, data, i % 16))
    for _ in range(20000):
        if len(done) == len(plan):
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"only {len(done)}/{len(plan)} read bursts completed")


def _report(tb, label, **kv):
    tb.log.info("PERF " + label + ": " + ", ".join(f"{k}={v:.3f}" if isinstance(v, float) else f"{k}={v}"
                                                   for k, v in kv.items()))


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_perf_write_stream(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    s = Sampler(tb, {'m_aw': (MASTER_PFX[CPU], 'aw'), 'm_w': (MASTER_PFX[CPU], 'w'),
                     'm_b': (MASTER_PFX[CPU], 'b'), 's_w': (SLAVE_PFX[DDR], 'w')})
    cocotb.start_soon(s.run())
    errors = []
    await _stream_writes(tb, _write_plan(CPU, DDR_BASE, n, 0xA1), errors)
    assert not errors, errors[:5]
    assert s.alive and s.marks['s_w'], "sampler saw no W handshake -- measured nothing"

    beats, cycles, rate = s.window_rate('s_w')
    assert beats == n * BEATS, f"{beats} W beats at the slave, expected {n * BEATS}"
    # Loaded latency: the k-th AW accepted at the master pairs with the k-th B
    # (one master, in-order slave); the fabric is full for the whole window.
    lat = [b - a for a, b in zip(s.marks['m_aw'], s.marks['m_b'])]
    # Who owns the gaps inside the window: the bridge (WVALID held, WREADY low
    # at the master port) or the stimulus (no WVALID offered)?
    lo, hi = s.marks['m_w'][0], s.marks['m_w'][-1]
    w_stalled, w_idle = s.gaps_in('m_w', lo, hi)
    _report(tb, "write_stream", bursts=n, beats=beats, cycles=cycles, beats_per_cycle=rate,
            master_w_stalled_cycles=w_stalled, master_w_idle_cycles=w_idle,
            aw_to_b_min=min(lat), aw_to_b_avg=sum(lat) / len(lat), aw_to_b_max=max(lat))
    assert rate >= FLOOR['write_stream_beats_per_cycle'], (
        f"write stream: {rate:.3f} W beats/cycle at the slave port, floor "
        f"{FLOOR['write_stream_beats_per_cycle']} (the HAS quotes DATA_WIDTH per cycle)")


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_perf_read_stream(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    plan = _write_plan(CPU, DDR_BASE, n, 0xA2)
    errors = []
    await _stream_writes(tb, plan, errors)          # seed what the reads will fetch
    assert not errors, errors[:5]
    s = Sampler(tb, {'m_ar': (MASTER_PFX[CPU], 'ar'), 'm_r': (MASTER_PFX[CPU], 'r'),
                     's_r': (SLAVE_PFX[DDR], 'r')})
    cocotb.start_soon(s.run())
    await _stream_reads(tb, plan, errors)
    assert not errors, errors[:5]
    assert s.marks['m_r'], "sampler saw no R handshake -- measured nothing"
    beats, cycles, rate = s.window_rate('m_r')
    assert beats == n * BEATS, f"{beats} R beats at the master, expected {n * BEATS}"
    _report(tb, "read_stream", bursts=n, beats=beats, cycles=cycles, beats_per_cycle=rate)
    assert rate >= FLOOR['read_stream_beats_per_cycle'], (
        f"read stream: {rate:.3f} R beats/cycle at the master port, floor "
        f"{FLOOR['read_stream_beats_per_cycle']}")


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_perf_contention(dut):
    """Both masters stream writes to ddr. The slave port must stay saturated
    and EACH master must get its share -- asserted per master."""
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    s = Sampler(tb, {'s_w': (SLAVE_PFX[DDR], 'w'),
                     'cpu_w': (MASTER_PFX[CPU], 'w'), 'dma_w': (MASTER_PFX[DMA], 'w')})
    cocotb.start_soon(s.run())
    errors = []
    plan = _write_plan(CPU, DDR_BASE, n, 0xC1) + _write_plan(DMA, DDR_BASE, n, 0xC2)
    await _stream_writes(tb, plan, errors)
    assert not errors, errors[:5]
    beats, cycles, rate = s.window_rate('s_w')
    assert beats == 2 * n * BEATS, f"{beats} W beats at the slave, expected {2 * n * BEATS}"
    # Shares over the CONTENDED part of the window only: from the moment both
    # masters have started until the first one finishes. Outside it one master
    # has the slave to itself and a share means nothing.
    lo = max(s.marks['cpu_w'][0], s.marks['dma_w'][0])
    hi = min(s.marks['cpu_w'][-1], s.marks['dma_w'][-1])
    cpu_c, dma_c = s.count_in('cpu_w', lo, hi), s.count_in('dma_w', lo, hi)
    total_c = cpu_c + dma_c
    share = min(cpu_c, dma_c) / total_c if total_c else 0.0
    _report(tb, "contention", bursts_per_master=n, beats=beats, cycles=cycles, beats_per_cycle=rate,
            contended_cycles=hi - lo + 1, cpu_beats=cpu_c, dma_beats=dma_c, min_share=share)
    assert total_c >= BEATS * 4, f"contended window too short to judge fairness ({total_c} beats)"
    assert rate >= FLOOR['contention_total_beats_per_cycle'], (
        f"contention: {rate:.3f} W beats/cycle at the shared slave port, floor "
        f"{FLOOR['contention_total_beats_per_cycle']}")
    assert share >= FLOOR['contention_min_share'], (
        f"contention: the smaller master got {share:.3f} of the contended beats "
        f"(cpu {cpu_c}, dma {dma_c}); round-robin owes each about half")
    for m, addr, data in plan:
        for k, d in enumerate(data):
            got = tb.slave_mem_read(DDR, addr + 4 * k, byte_count=4)
            assert got == d, f"m{m} 0x{addr + 4 * k:08X}: memory 0x{got:08X}, wrote 0x{d:08X}"


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_perf_parallel(dut):
    """cpu -> ddr and dma -> sram at the same time: two independent paths,
    two beats per cycle across the fabric."""
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    s = Sampler(tb, {'ddr_w': (SLAVE_PFX[DDR], 'w'), 'sram_w': (SLAVE_PFX[SRAM], 'w')})
    cocotb.start_soon(s.run())
    errors = []
    plan = _write_plan(CPU, DDR_BASE, n, 0xB1) + _write_plan(DMA, SRAM_BASE, n, 0xB2)
    await _stream_writes(tb, plan, errors)
    assert not errors, errors[:5]
    b0, c0, r0 = s.window_rate('ddr_w')
    b1, c1, r1 = s.window_rate('sram_w')
    lo = max(s.marks['ddr_w'][0], s.marks['sram_w'][0])
    hi = min(s.marks['ddr_w'][-1], s.marks['sram_w'][-1])
    both = (s.count_in('ddr_w', lo, hi) + s.count_in('sram_w', lo, hi)) / (hi - lo + 1)
    _report(tb, "parallel", bursts_per_master=n, ddr_beats_per_cycle=r0, sram_beats_per_cycle=r1,
            overlap_cycles=hi - lo + 1, overlap_beats_per_cycle=both)
    assert b0 == n * BEATS and b1 == n * BEATS
    assert hi - lo + 1 >= BEATS * 4, "the two streams barely overlapped; nothing was parallel"
    assert both >= FLOOR['parallel_total_beats_per_cycle'], (
        f"parallel: {both:.3f} W beats/cycle across both slave ports while both streams ran, "
        f"floor {FLOOR['parallel_total_beats_per_cycle']}")


def _run(request, test_level, testcase):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_perf_{testcase}_{test_level}_{reg_level}"
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
        testcase=f"cocotb_test_bridge_2x2_rw_perf_{testcase}",
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
def test_bridge_2x2_rw_perf_write_stream(request, test_level):
    _run(request, test_level, "write_stream")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_perf_read_stream(request, test_level):
    _run(request, test_level, "read_stream")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_perf_contention(request, test_level):
    _run(request, test_level, "contention")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_perf_parallel(request, test_level):
    _run(request, test_level, "parallel")
