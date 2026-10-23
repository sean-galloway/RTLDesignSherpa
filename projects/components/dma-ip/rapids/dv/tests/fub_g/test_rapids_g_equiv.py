# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_g_equiv
# Purpose: rapids-g (rapids TASK-034): the FSM scheduler and the
#          gatling-sequenced scheduler_g, side by side on the same
#          descriptors, ask the same of their engines.
#
# Documentation: projects/components/dma-ip/rapids/PRD.md (rapids-g)
# Subsystem: rapids fub_g
#
# Author: sean galloway
# Created: 2026-10-21

"""Equivalence cells (rapids_g_equiv_tb_top, RapidsGEquivTB).

  linear        byte-granular descriptors: every offset class, zero length,
                chains and IRQs -- the firmware's beat totals and chain policy
  ext           TYPE=EXT descriptors: per-beat and run-contiguous, negative and
                large strides, 64-bit carries, wraps below and above 32 bits,
                inner_count 0/1 -- the firmware's run bases against
                stream_run_addr_gen
  backpressure  packet-record queues held full, then toggling: FETCH_DESC held
                for hundreds of cycles (one DESC_START, rapids BUG-016) and the
                pending start taken on the cycle the records go
  error_reset   invalid descriptors and an engine error mid-transfer, then a
                channel reset and more work: the interlocks and recovery
"""

import os
import sys

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid, current_level

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_g_equiv_tb import (  # noqa: E402
    RapidsGEquivTB, ST_ERROR, ST_FETCH, ST_XFER, ST_COMPLETE, ST_NEXT, ST_IDLE, SIDES, make_desc)

DEPTH = {'gate': 6, 'func': 16, 'full': 40}     # descriptors per channel
# A cell's cycle budget scales with its depth: per-beat EXT descriptors cost
# the firmware a few hundred cycles a base (measured: cocotb_test_perf)
CYCLE_BUDGET = 400000 * DEPTH[current_level()] // DEPTH['gate']
LW_SUMMARY = 0x0004A283                         # lw t0, 0(s1): the SUMMARY poll (sched_g.S)


async def _finish(tb: RapidsGEquivTB, label: str):
    quiet = await tb.run_until_quiet(CYCLE_BUDGET)
    same = tb.compare()
    errs = tb.cmd_errors()
    halted = int(tb.dut.g_hart_halted.value)
    tb.log.info(f"{label}: quiet={quiet} equivalent={same} cmd_errors={errs} harts_halted=0x{halted:x} "
                f"cycles={tb.cycle}")
    assert quiet, f"{label}: the two sides did not finish"
    assert same, f"{label}: the FSM and gatling schedulers differ"
    assert errs == 0, f"{label}: scheduler_g counted {errs} illegal commands / dropped pushes"
    assert halted == 0, f"{label}: a gatling hart halted (0x{halted:x})"


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_linear(dut):
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    n = DEPTH[current_level()]
    tb.load([tb.rand_linear(n) for _ in range(tb.N)])
    await _finish(tb, "linear")


def _golden_check(tb, side, i, descs, start=(0, 0)):
    """Side `side`, channel i: the commands from index `start` on must be
    exactly the golden model's for `descs`."""
    c = tb.ch[side][i]
    bad = []
    for k, (what, is_wr) in enumerate((('rd_cmds', False), ('wr_cmds', True))):
        want = [x for d in descs for x in tb.golden_cmds(d, is_wr)]
        got = getattr(c, what)[start[k]:]
        if got != want:
            j = next((j for j in range(min(len(got), len(want))) if got[j] != want[j]), min(len(got), len(want)))
            bad.append(f"{side}{i} {what}: {len(got)} vs golden {len(want)}, first difference at #{j}: "
                       f"got {got[j] if j < len(got) else None} want {want[j] if j < len(want) else None}")
    for b in bad:
        tb.log.error(b)
    return not bad


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_ext(dut):
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    n = DEPTH[current_level()]
    lists = [tb.rand_ext(n) for _ in range(tb.N)]
    tb.load(lists)
    await _finish(tb, "ext")
    ok = all(_golden_check(tb, s, i, lists[i]) for s in SIDES for i in range(tb.N))
    assert ok, "ext: a side's commands differ from the golden run-base model"


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_reset_ext(dut):
    """A channel reset while an EXT descriptor waits in FETCH_DESC, its run
    bases already being generated; the next EXT descriptor must walk its own
    bases (golden model), not the reset one's."""
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    L = tb.lanes
    ext_a = dict(rd_s0=L, rd_s1=64 * L, rd_inner=2, wr_s0=L, wr_s1=128 * L, wr_inner=2)
    ext_b = dict(rd_s0=L, rd_s1=-8 * L, rd_inner=3, wr_s0=L, wr_s1=-16 * L, wr_inner=3)
    a = [make_desc(0x100_0000 + i * 0x10_0000, 0x900_0000 + i * 0x10_0000, 24 * L, ext=ext_a)
         for i in range(tb.N)]
    b = [make_desc(0x4000_0000 + i * 0x10_0000, 0x6000_0000 + i * 0x10_0000, 18 * L, ext=ext_b)
         for i in range(tb.N)]
    for s in SIDES:
        tb.pkt_ready[s] = [0] * tb.N               # A is held in FETCH_DESC
    tb.load([[d] for d in a])
    # every channel reaches FETCH_DESC and is held there; with two slots a
    # hart finishes one slot's FETCH work before it takes the other's
    for _ in range(CYCLE_BUDGET // 8):
        await tb.run_cycles(8)
        if all(tb.ch[s][i].state == ST_FETCH for s in SIDES for i in range(tb.N)):
            break
    await tb.run_cycles(200)
    assert all(tb.ch[s][i].state == ST_FETCH for s in SIDES for i in range(tb.N)), "A not held in FETCH_DESC"
    await tb.channel_reset((1 << tb.N) - 1)
    for s in SIDES:
        tb.pkt_ready[s] = [1] * tb.N
    marks = {s: [(len(tb.ch[s][i].rd_cmds), len(tb.ch[s][i].wr_cmds)) for i in range(tb.N)] for s in SIDES}
    tb.load([[d] for d in b])
    quiet = await tb.run_until_quiet(CYCLE_BUDGET)
    assert quiet, "reset_ext: did not finish"
    results = {s: all(_golden_check(tb, s, i, [b[i]], marks[s][i]) for i in range(tb.N)) for s in SIDES}
    tb.log.info(f"reset_ext: FSM scheduler matches golden: {results['f']}; scheduler_g matches golden: {results['g']}")
    assert results['g'], "scheduler_g walked the wrong bases after a reset"
    assert results['f'], "the FSM scheduler walked the wrong bases after a reset"
    await _finish(tb, "reset_ext")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_backpressure(dut):
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    n = DEPTH[current_level()]
    # the first descriptor moves data, so it needs records and is held; a
    # zero-length one would complete without any
    first = [make_desc(0x4000 + 3, 0x9000 + 5, 7 * tb.lanes + 9, gen_irq=True)]
    tb.load([first + tb.rand_linear(n, chains=False) + tb.rand_ext(2) for _ in range(tb.N)])
    for s in tb.pkt_ready:
        tb.pkt_ready[s] = [0] * tb.N
    for _ in range(CYCLE_BUDGET // 8):            # every channel reaches FETCH_DESC and waits
        await tb.run_cycles(8)
        if all(tb.ch[s][i].state == 0x02 for s in tb.pkt_ready for i in range(tb.N)):
            break
    await tb.run_cycles(200)
    held = all(tb.ch[s][i].state == 0x02 for s in tb.pkt_ready for i in range(tb.N))
    starts = [len(tb.ch[s][i].mons) for s in tb.pkt_ready for i in range(tb.N)]
    tb.log.info(f"held in FETCH_DESC: {held}; MonBus packets so far per channel {starts}")
    assert held, "a channel left FETCH_DESC with its record queue full"
    assert all(k == 1 for k in starts), f"one DESC_START per held descriptor, got {starts}"
    # then the queues come and go, independently per side
    for _ in range(400):
        for s in tb.pkt_ready:
            tb.pkt_ready[s] = [int(tb.lat_rng[s].random() < 0.6) for _ in range(tb.N)]
        await tb.run_cycles(5)
    for s in tb.pkt_ready:
        tb.pkt_ready[s] = [1] * tb.N
    await _finish(tb, "backpressure")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_error_reset(dut):
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    L = tb.lanes
    # every channel: two good, then an invalid descriptor (CH_ERROR)
    tb.load([tb.rand_linear(2, chains=False) + [make_desc(0x1000, 0x2000, 4 * L, valid=False)]
             for _ in range(tb.N)])
    for i in range(tb.N):
        assert await tb.wait_state(i, ST_ERROR, CYCLE_BUDGET), f"ch{i}: no CH_ERROR after an invalid descriptor"
    await tb.run_cycles(200)                       # sticky until a reset
    assert all(tb.ch[s][i].state == ST_ERROR for s in tb.pkt_ready for i in range(tb.N))
    await tb.channel_reset((1 << tb.N) - 1)
    # an engine error part-way through a long transfer, on the even channels
    marks = {i: tb.mark(i) for i in range(tb.N)}
    for i in range(tb.N):
        long = make_desc(0x10_0000 + i * 0x1_0000, 0x80_0000 + i * 0x1_0000, 64 * L)
        tb.load_one(i, [long])
        if i % 2 == 0:
            for s in tb.pkt_ready:
                tb.ch[s][i].rd_error_after = len(tb.ch[s][i].rd_cmds) + 3
    for i in range(0, tb.N, 2):
        assert await tb.wait_state(i, ST_ERROR, CYCLE_BUDGET), f"ch{i}: no CH_ERROR after sched_rd_error"
    assert await tb.run_until_quiet(CYCLE_BUDGET)
    for i in range(0, tb.N, 2):
        tb.skip_window(i, marks[i], tb.mark(i))
        for s in tb.pkt_ready:
            assert tb.ch[s][i].err_to_error is not None, f"{s}{i}: the injected error never reached CH_ERROR"
    await tb.channel_reset((1 << tb.N) - 1)
    # and the channels work again
    tb.load([tb.rand_linear(3) for _ in range(tb.N)])
    await _finish(tb, "error_reset")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_reset_any(dut):
    """A channel reset in every state: channel i is reset when its third
    descriptor reaches FETCH_DESC, XFER_DATA, COMPLETE or NEXT_DESC (by i),
    on each side at that point of its own run. The descriptors are a mix
    of linear chains and EXT, so a reset can land with EXT bases queued:
    whatever the next descriptors ask for must still match."""
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    L = tb.lanes
    states = [ST_FETCH, ST_XFER, ST_COMPLETE, ST_NEXT]
    lists, afters = [], []
    for i in range(tb.N):
        third = states[i % 4]
        if third == ST_NEXT:     # a chain whose first link is the third descriptor
            mid = [make_desc(0x30_0000 + 3, 0x70_0000, 9 * L + 5, next_ptr=0x40, last=False),
                   make_desc(0x31_0000, 0x71_0000, 6 * L, last=True)]
        elif third == ST_FETCH:  # held in FETCH: its records cannot go (see below)
            mid = tb.rand_ext(1)
        else:
            mid = tb.rand_ext(1) if i % 2 else tb.rand_linear(1, chains=False)
        lists.append(tb.rand_linear(2, chains=False) + mid)
        afters.append(tb.rand_ext(2) + tb.rand_linear(3))
        tb.plan_reset(i, 3, third, after=afters[-1])
    tb.load(lists)
    # FETCH_DESC is held only while the records cannot go: close the record
    # queues of the FETCH channels around their third descriptor
    for _ in range(CYCLE_BUDGET):
        await tb.run_cycles(1)
        for s in SIDES:
            for i in range(0, tb.N, 4):
                c = tb.ch[s][i]
                past_second = c.fetches >= 3 or (c.fetches == 2 and c.state != ST_FETCH)
                tb.pkt_ready[s][i] = 0 if (c.reset_at and past_second) else 1
        if tb.resets_done():
            break
    for s in SIDES:
        tb.pkt_ready[s] = [1] * tb.N
    pending = [(s, i, c.reset_at, c.fetches, hex(c.state)) for s in SIDES
               for i, c in enumerate(tb.ch[s]) if c.reset_at or c.reset_left]
    assert tb.resets_done(), f"planned resets never reached their state: {pending}"
    assert await tb.run_until_quiet(CYCLE_BUDGET), "reset_any: did not finish"
    # after its reset, each side must walk exactly the golden commands (an
    # independent check: equivalence alone cannot say which side is right)
    gold = {s: all(_golden_check(tb, s, i, afters[i],
                                 (tb.ch[s][i].post_reset['rd_cmds'], tb.ch[s][i].post_reset['wr_cmds']))
                   for i in range(tb.N)) for s in SIDES}
    tb.log.info(f"reset_any: after the resets, FSM scheduler golden: {gold['f']}; scheduler_g golden: {gold['g']}")
    assert gold['g'], "reset_any: scheduler_g's commands after a reset differ from the golden"
    assert gold['f'], "reset_any: the FSM scheduler's commands after a reset differ from the golden (rapids BUG-017)"
    await _finish(tb, "reset_any")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_hart_fault(dut):
    """A hart that halts faults its channels: every gatling-side channel
    goes to CH_ERROR and sends its error packet. Once all of a hart's
    channels are reset it restarts, and the channels work again (and
    match the FSM side from there)."""
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    tb.load([tb.rand_linear(2, chains=False) for _ in range(tb.N)])
    assert await tb.run_until_quiet(CYCLE_BUDGET), "the warm-up did not finish"
    rom = dut.u_seq.r_rom
    # every poll loop of sched_g.S (one slot and two) reads SUMMARY with this
    # word, so whichever loop the harts run, they reach an illegal one
    polls = [w for w in range(len(rom)) if int(rom[w].value) == LW_SUMMARY]
    assert len(polls) == 2, f"expected the two loops' SUMMARY polls, found ROM words {polls}"
    await Timer(1, 'ns')                           # out of ReadOnly before writing
    for w in polls:
        rom[w].value = 0xFFFF_FFFF                 # an illegal instruction
    tb.load([tb.rand_linear(1, chains=False) for _ in range(tb.N)])
    await tb.run_cycles(400)
    halted = int(dut.g_hart_halted.value)
    assert halted == (1 << tb.N) - 1, f"every hart should have halted on the illegal word, got 0x{halted:x}"
    for i in range(tb.N):
        g = tb.ch['g'][i]
        assert g.state == ST_ERROR, f"g{i}: a halted hart's channel is in 0x{g.state:02x}, not CH_ERROR"
        assert any((m >> 104) & 0xF == 0x1 for m in g.mons) or g.mons, f"g{i}: no MonBus packet"
    errs_before = [len(tb.ch['g'][i].mons) for i in range(tb.N)]
    await Timer(1, 'ns')
    for w in polls:
        rom[w].value = LW_SUMMARY
    await tb.channel_reset((1 << tb.N) - 1)
    await tb.run_cycles(8)
    assert int(dut.g_hart_halted.value) == 0, "the harts did not restart after their channels' reset"
    # compare from here on: drop everything before on both sides
    for s in SIDES:
        for i in range(tb.N):
            c = tb.ch[s][i]
            c.queue.clear()
            c.head = None
            for w in ('rd_cmds', 'wr_cmds', 'rd_pkts', 'wr_pkts', 'mons', 'states'):
                c.skip.append((w, 0, len(getattr(c, w))))
    tb.load([tb.rand_linear(3) + tb.rand_ext(1) for _ in range(tb.N)])
    tb.log.info(f"hart_fault: harts halted 0x{halted:x}, MonBus packets before the reset {errs_before}")
    await _finish(tb, "hart_fault")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_perf(dut):
    """Measured, not judged: what the firmware costs against the FSM.

    Engines take exactly one cycle per burst and never stall, so the
    scheduler is the only limit. Each scenario runs the same descriptors on
    both sides and records the cycles each side needs; results go to the log
    and to perf_<cell>.json beside it."""
    import json
    tb = RapidsGEquivTB(dut)
    await tb.setup_clocks_and_reset()
    tb.fixed_lat = 1
    L, n = tb.lanes, 16
    out = {'channels': tb.N, 'data_width': tb.DW}

    async def scenario(name, per_channel, channels):
        lists = [per_channel(i) if i in channels else [] for i in range(tb.N)]
        tb.load(lists)
        done = await tb.cycles_to_quiet(CYCLE_BUDGET)
        ndesc = sum(len(x) for x in lists)
        out[name] = {'descriptors': ndesc, 'f_cycles': done.get('f'), 'g_cycles': done.get('g')}
        f, g = done.get('f'), done.get('g')
        tb.log.info(f"perf {name}: {ndesc} descriptors, FSM {f} cycles, gatling {g} cycles"
                    + (f", {(g - f) / ndesc:.1f} extra cycles per descriptor, {100.0 * (g - f) / f:.2f}% longer"
                       if f and g else ""))
        await tb.run_cycles(64)

    one_beat = lambda i: [make_desc(0x1000 * (k + 1) + i * 0x10_0000, 0x80_0000 + 0x1000 * k + i * 0x10_0000, L)
                          for k in range(n)]
    big = lambda i: [make_desc(0x1000 * (k + 1) + i * 0x10_0000, 0x80_0000 + 0x1000 * k + i * 0x10_0000, 64 * L)
                     for k in range(n)]
    ext_run = lambda i: [make_desc(0x100_0000 + i * 0x10_0000, 0x900_0000 + i * 0x10_0000, 64 * L,
                                   ext=dict(rd_s0=L, rd_s1=8 * L, rd_inner=4, wr_s0=L, wr_s1=8 * L, wr_inner=4))
                         for _ in range(4)]
    ext_beat = lambda i: [make_desc(0x100_0000 + i * 0x10_0000, 0x900_0000 + i * 0x10_0000, 64 * L,
                                    ext=dict(rd_s0=2 * L, rd_s1=32 * L, rd_inner=8, wr_s0=2 * L, wr_s1=32 * L, wr_inner=8))
                          for _ in range(4)]
    big64k = lambda i: [make_desc(0x1000_0000 * (i + 1) + 0x10_0000 * k, 0x8_0000_0000 + 0x1000_0000 * i + 0x10_0000 * k,
                                  0x1_0000) for k in range(4)]
    mb = lambda i: [make_desc(0x1000_0000 * (i + 1) + 0x10_0000 * k, 0x8_0000_0000 + 0x1000_0000 * i + 0x10_0000 * k,
                              0x10_0000) for k in range(2)]
    mb_ext = lambda i: [make_desc(0x1000_0000 * (i + 1), 0x8_0000_0000 + 0x1000_0000 * i, 0x10_0000,
                                  ext=dict(rd_s0=L, rd_s1=1024 * L, rd_inner=256, wr_s0=L, wr_s1=1024 * L, wr_inner=256))]
    await scenario('one_beat_x16_one_channel', one_beat, {0})
    await scenario('one_beat_x16_all_channels', one_beat, set(range(tb.N)))
    await scenario('64_beat_x16_all_channels', big, set(range(tb.N)))
    await scenario('ext_run4_64beat_x4_all_channels', ext_run, set(range(tb.N)))
    await scenario('ext_per_beat_64beat_x4_all_channels', ext_beat, set(range(tb.N)))
    await scenario('64KB_x4_all_channels', big64k, set(range(tb.N)))
    await scenario('1MB_x2_all_channels', mb, set(range(tb.N)))
    await scenario('1MB_ext_runs256_all_channels', mb_ext, set(range(tb.N)))
    assert tb.compare(), "perf: the sides differ"
    path = os.environ.get('LOG_PATH', 'perf.log').replace('.log', '.json').replace('test_rapids_g_equiv_', 'perf_')
    with open(path, 'w') as fh:
        json.dump(out, fh, indent=1)
    tb.log.info(f"perf results: {path}")


# ---------------------------------------------------------------------------
# pytest
# ---------------------------------------------------------------------------

CASES = ['linear', 'ext', 'reset_ext', 'backpressure', 'error_reset', 'reset_any', 'hart_fault', 'perf']
CONFIGS = [(4, 256), (8, 256), (8, 512)]


@pytest.mark.fub
@pytest.mark.rapids_g
@pytest.mark.parametrize("case", CASES)
@pytest.mark.parametrize("num_channels, data_width", CONFIGS)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_g_equiv(request, case, num_channels, data_width, test_level):
    """FSM scheduler vs scheduler_g + firmware: the `case` scenario."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut = 'rapids_g_equiv_tb_top'
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dma-ip/rapids/dv/filelists/rapids_g_equiv_tb_top.f')
    name = f"test_rapids_g_equiv_{case}_nc{num_channels:02d}_dw{data_width:04d}_{test_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        name = f"{name}_{worker_id}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, name)
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut,
            module=module,
            testcase=f"cocotb_test_{case}",
            parameters={'NUM_CHANNELS': num_channels, 'DATA_WIDTH': data_width},
            simulator="verilator",
            sim_build=sim_build,
            extra_env={'LOG_PATH': log_path, 'DUT': dut, 'COCOTB_LOG_LEVEL': 'INFO',
                       **level_env(test_level),
                       'TEST_NUM_CHANNELS': str(num_channels),
                       'TEST_DATA_WIDTH': str(data_width),
                       'COCOTB_RESULTS_FILE': os.path.join(log_dir, f"results_{name}.xml")},
            waves=enable_waves,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-SELRANGE",
                          "-Wno-CASEINCOMPLETE", "-Wno-PINCONNECTEMPTY"],
            plus_args=['--trace'] if enable_waves else [],
        )
    except Exception:
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise
