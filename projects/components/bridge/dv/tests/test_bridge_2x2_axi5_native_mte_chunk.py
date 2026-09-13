#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): the native-AXI5 fabric (BRIDGE-018) --
# Memory Tagging and read-data chunking end to end, under contention.
#
# bridge_2x2_axi5_native is two 128-bit AXI5 masters and two 128-bit AXI5
# slaves with mte + chunking on every port. The AXI5 BFMs drive the tag
# operations and chunk enables per transaction (no pin poking); the slave
# BFMs keep a real tag store beside their memory model (RDS-DV
# axi5_tag_store) and answer Match operations from it. Both masters work the
# same slave at once, so every check also covers the arbiter and the b/r
# return mux:
#   - Transfer writes: every AW at the slave port carries TAGOP=Transfer and
#     the W beats carry the issuing master's tags (cpu tags 0..7, dma tags
#     8..15, so a swap is visible); the slave's tag store holds the exact
#     tag per 16-byte granule afterwards -- the tags crossed the fabric;
#   - Transfer reads: RTAG per beat equals the stored tag, RTAGMATCH set;
#   - Match writes: matching tags return BTAGMATCH=1, one wrong tag returns
#     0 -- the result crossed back through the B mux to the right master;
#   - Update writes: WTAGUPDATE low leaves the store alone, high changes it;
#   - Chunked reads: with ARCHUNKEN every R beat has RCHUNKV set and
#     RCHUNKNUM naming the beat; without it RCHUNKV is low; data is right
#     either way and the slave port saw exactly the chunk enables issued;
#   - Out-of-order chunks: the slave BFM is then switched to emit each
#     chunked burst's transfers in REVERSE order (RDS-DV #81), so RLAST
#     rides the first beat and RCHUNKNUM runs backwards on the wire. The
#     fabric must route those beats by ID and free its tracking on RLAST
#     without caring: every burst completes, the data reassembles by
#     RCHUNKNUM, the wire order is provably permuted, and the ordered
#     control reads beside them are untouched;
#   - the AXI5 compliance checkers on both master ports: zero violations.
# Depth (TEST_LEVEL): arb_per_master transactions per master and phase.

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

from CocoTBFramework.components.axi5.axi5_interfaces import (
    axi5_tag_store, TAGOP_TRANSFER, TAGOP_UPDATE, TAGOP_MATCH, TAG_GRANULE)
from projects.components.bridge.dv.tbclasses.bridge2x2_axi5_native_tb import Bridge2x2Axi5NativeTB

CPU, DMA = 0, 1
DDR = 0                     # slave index of the contended AXI5 port
DDR_BASE = 0x0000_0000
BEATS = 4                   # 128-bit beats per burst (one 16-byte tag granule each)
SIZE = 4                    # AxSIZE for 16-byte beats
TAG_BASE = {CPU: 0x0, DMA: 0x8}   # cpu tags 0..7, dma tags 8..15


def _region(m, i):
    """Each master owns half of the slave's seeded window; burst i is 64 B."""
    return DDR_BASE + (0x0000 if m == CPU else 0x8000) + i * (BEATS * 16)


def _tags(m, i):
    return [(TAG_BASE[m] | ((i + k) & 0x7)) for k in range(BEATS)]


class DdrPortSampler:
    """Every handshake at the ddr (AXI5 slave) port: the tag operation and
    tags on AW/W, the chunk enable and tag operation on AR, the chunk valid
    and tags on R."""

    def __init__(self, dut, clock):
        self.dut, self.clock = dut, clock
        self.aw, self.w, self.ar, self.r = [], [], [], []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.ddr_axi_awvalid.value) and int(d.ddr_axi_awready.value):
                self.aw.append((int(d.ddr_axi_awtagop.value), int(d.ddr_axi_awtag.value)))
            if int(d.ddr_axi_wvalid.value) and int(d.ddr_axi_wready.value):
                self.w.append((int(d.ddr_axi_wtag.value), int(d.ddr_axi_wtagupdate.value)))
            if int(d.ddr_axi_arvalid.value) and int(d.ddr_axi_arready.value):
                self.ar.append((int(d.ddr_axi_archunken.value), int(d.ddr_axi_artagop.value)))
            if int(d.ddr_axi_rvalid.value) and int(d.ddr_axi_rready.value):
                self.r.append((int(d.ddr_axi_rchunkv.value), int(d.ddr_axi_rchunknum.value),
                               int(d.ddr_axi_rtag.value)))


async def _run_all(tb, coros, total, label):
    done = []

    async def _wrap(c):
        await c
        done.append(1)

    for c in coros:
        cocotb.start_soon(_wrap(c))
    for _ in range(8000):
        if len(done) == total:
            return
        await ClockCycles(tb.clock, 10)
    raise AssertionError(f"{label}: {len(done)}/{total} transactions completed")


@cocotb.test(timeout_time=12000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_axi5_native_mte_chunk(dut):
    tb = Bridge2x2Axi5NativeTB(dut)
    await tb.setup_clocks_and_reset()
    sampler = DdrPortSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())
    n = tb.level_cfg['arb_per_master']
    store = axi5_tag_store(tb.slave_memory[DDR])
    tb.log.info(f"BRIDGE-018 native AXI5: MTE + chunking, {n} txn/master/phase (level={tb.level})")
    # Slow the slave so the two masters genuinely contend at the arbiter.
    tb.set_slave_response_delay(DDR, 12)

    # ---- phase 1: Transfer writes with per-beat tags, both masters at once
    data = {(m, i): [(0x7A60_0000_0000_0000_0000_0000_0000_0000 | (m << 64) | (i << 8) | k)
                     for k in range(BEATS)] for m in (CPU, DMA) for i in range(n)}
    results = {}

    async def _tw(m, i):
        r = await tb.master_wr[m].write_transaction(
            _region(m, i), data[(m, i)], size=SIZE, id=(m << 3) | (i % 8),
            tagop=TAGOP_TRANSFER, tag=0, wtag=_tags(m, i), tagupdate=1)
        results[(m, i)] = r

    await _run_all(tb, [_tw(m, i) for m in (CPU, DMA) for i in range(n)], 2 * n, "transfer writes")
    for k, r in results.items():
        assert r.get('success'), f"transfer write {k} failed: {r}"
    assert len(sampler.aw) == 2 * n, f"slave saw {len(sampler.aw)} AWs, expected {2 * n}"
    assert all(op == TAGOP_TRANSFER for op, _ in sampler.aw), (
        f"AWTAGOP at the slave: {sorted(set(op for op, _ in sampler.aw))}, expected all Transfer")
    w_tags = [t for t, _ in sampler.w]
    assert len(w_tags) == 2 * n * BEATS, f"slave saw {len(w_tags)} W beats"
    for m in (CPU, DMA):
        issued = sorted(t for i in range(n) for t in _tags(m, i))
        seen = sorted(t for t in w_tags if (t & 0x8) == TAG_BASE[m])
        assert seen == issued, f"master {m}: W tags at the slave {seen[:8]}... != issued {issued[:8]}..."
    for m in (CPU, DMA):
        for i in range(n):
            for k, t in enumerate(_tags(m, i)):
                g = _region(m, i) + k * TAG_GRANULE
                assert store.get(g) == t, (
                    f"tag store @0x{g:08X} = {store.get(g)}, master {m} wrote {t}: tags did not cross the fabric intact")
    tb.log.info(f"phase 1: {2 * n} Transfer writes, {len(w_tags)} tagged beats landed in the slave's tag store")

    # ---- phase 2: Transfer reads return the stored tags, both masters at once
    reads = {}

    async def _tr(m, i):
        reads[(m, i)] = await tb.master_rd[m].read_transaction(
            _region(m, i), burst_len=BEATS, size=SIZE, id=(m << 3) | (i % 8), tagop=TAGOP_TRANSFER)

    await _run_all(tb, [_tr(m, i) for m in (CPU, DMA) for i in range(n)], 2 * n, "transfer reads")
    for (m, i), beats in reads.items():
        assert [b['data'] for b in beats] == data[(m, i)], f"read data mismatch for {(m, i)}"
        assert [b['tag'] for b in beats] == _tags(m, i), (
            f"master {m} burst {i}: RTAG {[b['tag'] for b in beats]} != written {_tags(m, i)}")
        assert all(b['tagmatch'] == 1 for b in beats), f"RTAGMATCH not set on a Transfer read {(m, i)}"
    tb.log.info(f"phase 2: {2 * n} Transfer reads returned every tag")

    # ---- phase 3: Match writes -- right tags pass, one wrong tag fails
    match = {}

    async def _tm(m, i, wrong):
        tags = list(_tags(m, i))
        if wrong:
            tags[1] ^= 0x4
        r = await tb.master_wr[m].write_transaction(
            _region(m, i), data[(m, i)], size=SIZE, id=(m << 3) | (i % 8),
            tagop=TAGOP_MATCH, tag=0, wtag=tags, tagupdate=0)
        match[(m, i)] = (wrong, r)

    await _run_all(tb, [_tm(m, i, wrong=(i % 2 == 1)) for m in (CPU, DMA) for i in range(n)], 2 * n, "match writes")
    for (m, i), (wrong, r) in match.items():
        assert r.get('success'), f"match write {(m, i)} failed: {r}"
        assert r.get('tagmatch') == (0 if wrong else 1), (
            f"master {m} burst {i}: BTAGMATCH={r.get('tagmatch')} for a {'mismatching' if wrong else 'matching'} Match")
    tb.log.info(f"phase 3: {2 * n} Match writes, BTAGMATCH right for every one")

    # ---- phase 4: Update writes honour WTAGUPDATE
    upd = {}

    async def _tu(m, i, update):
        r = await tb.master_wr[m].write_transaction(
            _region(m, i), data[(m, i)], size=SIZE, id=(m << 3) | (i % 8),
            tagop=TAGOP_UPDATE, tag=0, wtag=[(t ^ 0x3) for t in _tags(m, i)], tagupdate=update)
        upd[(m, i)] = r

    await _run_all(tb, [_tu(m, i, update=(1 if i % 2 == 0 else 0)) for m in (CPU, DMA) for i in range(n)], 2 * n, "update writes")
    for (m, i), r in upd.items():
        assert r.get('success'), f"update write {(m, i)} failed: {r}"
        for k, t in enumerate(_tags(m, i)):
            g = _region(m, i) + k * TAG_GRANULE
            want = (t ^ 0x3) if i % 2 == 0 else t
            assert store.get(g) == want, (
                f"tag store @0x{g:08X} = {store.get(g)} after Update(tagupdate={1 if i % 2 == 0 else 0}), expected {want}")
    tb.log.info(f"phase 4: {2 * n} Update writes, the store follows WTAGUPDATE")

    # ---- phase 5: chunked reads from both masters, and unchunked controls
    sampler.ar.clear(); sampler.r.clear()
    chunked, plain = {}, {}

    async def _tc(m, i, chunk):
        beats = await tb.master_rd[m].read_transaction(
            _region(m, i), burst_len=BEATS, size=SIZE, id=(m << 3) | (i % 8), chunken=1 if chunk else 0)
        (chunked if chunk else plain)[(m, i)] = beats

    await _run_all(tb, [_tc(m, i, chunk=(i % 2 == 0)) for m in (CPU, DMA) for i in range(n)], 2 * n, "chunked reads")
    for (m, i), beats in chunked.items():
        assert [b['data'] for b in beats] == data[(m, i)], f"chunked read data mismatch {(m, i)}"
        assert [b['chunkv'] for b in beats] == [1] * BEATS, f"{(m, i)}: RCHUNKV {[b['chunkv'] for b in beats]}"
        assert [b['chunknum'] for b in beats] == list(range(BEATS)), (
            f"{(m, i)}: RCHUNKNUM {[b['chunknum'] for b in beats]}")
    for (m, i), beats in plain.items():
        assert [b['data'] for b in beats] == data[(m, i)], f"plain read data mismatch {(m, i)}"
        assert all(b['chunkv'] == 0 for b in beats), f"{(m, i)}: RCHUNKV set on an unchunked read"
    n_chunk = sum(1 for en, _ in sampler.ar if en)
    assert n_chunk == len(chunked), f"slave saw {n_chunk} ARCHUNKEN, issued {len(chunked)}"
    assert len(sampler.ar) == 2 * n, f"slave saw {len(sampler.ar)} ARs"
    r_chunked = sum(1 for v, _, _ in sampler.r if v)
    assert r_chunked == len(chunked) * BEATS, f"slave port: {r_chunked} chunk-valid R beats, expected {len(chunked) * BEATS}"
    tb.log.info(f"phase 5: {len(chunked)} chunked + {len(plain)} plain reads, chunk fields right on every beat")

    # ---- phase 6: the completer returns chunks out of order; the fabric must not care
    tb.slave_rd[DDR].chunk_order = 'reverse'
    sampler.r.clear()
    rev, ctl = {}, {}

    async def _to(m, i, chunk):
        beats = await tb.master_rd[m].read_transaction(
            _region(m, i), burst_len=BEATS, size=SIZE, id=(m << 3) | (i % 8), chunken=1 if chunk else 0)
        (rev if chunk else ctl)[(m, i)] = beats

    await _run_all(tb, [_to(m, i, chunk=(i % 2 == 0)) for m in (CPU, DMA) for i in range(n)], 2 * n, "reversed-chunk reads")
    permuted = 0
    for (m, i), beats in rev.items():
        assert [b['data'] for b in beats] == data[(m, i)], f"reversed chunks {(m, i)}: data did not reassemble"
        assert [b['chunknum'] for b in beats] == list(range(BEATS)), f"{(m, i)}: RCHUNKNUM after reassembly"
        wire = [b['wire_index'] for b in beats]
        assert wire == list(reversed(range(BEATS))), (
            f"{(m, i)}: expected the wire to carry the beats reversed, saw wire order {wire}")
        assert all(b['chunkstrb'] == 1 for b in beats), f"{(m, i)}: RCHUNKSTRB {[b['chunkstrb'] for b in beats]}"
        permuted += 1
    for (m, i), beats in ctl.items():
        assert [b['data'] for b in beats] == data[(m, i)] and all(b['chunkv'] == 0 for b in beats), f"control read {(m, i)}"
    # at the slave port the chunk numbers ran backwards within every burst
    nums = [num for v, num, _ in sampler.r if v]
    assert len(nums) == permuted * BEATS, f"slave port: {len(nums)} chunk-valid beats, expected {permuted * BEATS}"
    descents = sum(1 for a, b in zip(nums, nums[1:]) if b < a)
    assert descents >= permuted * (BEATS - 1) // 2, (
        f"slave port RCHUNKNUM sequence shows only {descents} descents for {permuted} reversed bursts -- the beats were not permuted")
    tb.slave_rd[DDR].chunk_order = 'in_order'
    tb.log.info(f"phase 6: {permuted} bursts returned with reversed chunks, all reassembled; {len(ctl)} ordered controls beside them")

    tb.assert_compliance()
    tb.log.info("BRIDGE-018 native AXI5 MTE + chunking PASSED")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_axi5_native_mte_chunk(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_axi5_native"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_mte_chunk_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_axi5_native_mte_chunk",
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
