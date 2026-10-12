#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# axi5_atomic_filter (bridge TASK-002 (was BRIDGE-002) A5-3a): store-class atomics and plain
# writes pass through; read-return atomics (AWATOP[5]==1) are swallowed
# — AW not forwarded, W burst discarded, local DECERR B with the AW ID,
# and (IHI 0022L A6.4.7/A6.4.8) the read data transfers the atomic owes on R,
# each DECERR, carrying the AW ID, RLAST on the final one.

import os
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

ATOP_NONE = 0b000000
ATOP_STORE = 0b010000   # AtomicStore: B-only response, forwards
ATOP_LOAD = 0b100000    # AtomicLoad: read-return, swallowed
ATOP_SWAP = 0b110000    # AtomicSwap: read-return, swallowed
ATOP_CMP = 0b110001     # AtomicCompare: read-return, swallowed, half the R beats

TEST_LEVEL = os.environ.get('TEST_LEVEL', 'func').lower()
_ROUNDS = {'gate': 1, 'func': 4, 'full': 16}.get(TEST_LEVEL, 4)


def _expected_r_beats(atop, awlen):
    """Read data transfers a read-return atomic owes, IHI 0022L A6.4.7.

    "The number of read data transfers is determined from both AWLEN and the
    AWATOP signals. For the AtomicCompare operation, if AWLEN indicates a
    transaction length greater than 1, then the number of read data transfers
    is half that specified by AWLEN." Load and Swap return AWLEN+1.
    """
    if atop == ATOP_CMP:
        return (awlen + 1) // 2 if awlen > 0 else 1
    return awlen + 1


async def _downstream_model(dut, fwd_aw, bresp_queue):
    """Always-ready downstream: log forwarded AWs, and after each
    forwarded burst's WLAST return a B (id popped from fwd_aw order)."""
    dut.m_awready.value = 1
    dut.m_wready.value = 1
    dut.m_bvalid.value = 0
    pending_b = []
    inflight = []
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.m_awvalid.value) and int(dut.m_awready.value):
            aw_id = int(dut.s_awid.value)  # payload routes around the DUT
            fwd_aw.append(aw_id)
            inflight.append(aw_id)
        if int(dut.m_wvalid.value) and int(dut.m_wready.value) \
                and int(dut.s_wlast.value):
            pending_b.append(inflight.pop(0))
        if int(dut.m_bvalid.value) and int(dut.m_bready.value):
            dut.m_bvalid.value = 0
        if pending_b and not int(dut.m_bvalid.value):
            bid = pending_b.pop(0)
            dut.m_bid.value = bid
            dut.m_bresp.value = 0  # OKAY
            dut.m_bvalid.value = 1
            bresp_queue.append(bid)


async def _send_write(dut, awid, atop, beats):
    """Drive one AW then its W burst through the upstream side."""
    dut.s_awid.value = awid
    dut.s_awatop.value = atop
    if hasattr(dut, 's_awlen'):
        dut.s_awlen.value = beats - 1
    dut.s_awvalid.value = 1
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.s_awready.value):
            break
    dut.s_awvalid.value = 0
    for i in range(beats):
        dut.s_wlast.value = 1 if i == beats - 1 else 0
        dut.s_wvalid.value = 1
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_wready.value):
                break
    dut.s_wvalid.value = 0
    dut.s_wlast.value = 0


async def _collect_b(dut, out, count):
    while len(out) < count:
        await RisingEdge(dut.aclk)
        if int(dut.s_bvalid.value) and int(dut.s_bready.value):
            out.append((int(dut.s_bid.value), int(dut.s_bresp.value)))


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def atomic_filter_b_after_wlast_test(dut):
    """A swallowed atomic's DECERR must not be presented before its WLAST.

    AXI forbids returning a write response before the write data has been
    received. The filter reserved its response-queue slot at AW ACCEPT and made
    the DECERR visible immediately, so a master still driving W beats could see
    BVALID for that very burst.
    """
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.aresetn.value = 0
    dut.s_awvalid.value = 0
    dut.s_wvalid.value = 0
    dut.s_bready.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)

    fwd_aw, bresp_queue = [], []
    cocotb.start_soon(_downstream_model(dut, fwd_aw, bresp_queue))

    early, wlast_seen = [], []

    async def _watch():
        while True:
            await RisingEdge(dut.aclk)
            await ReadOnly()
            if int(dut.s_wvalid.value) and int(dut.s_wready.value) \
                    and int(dut.s_wlast.value):
                wlast_seen.append(1)
            if int(dut.s_bvalid.value) and not wlast_seen:
                early.append(1)

    cocotb.start_soon(_watch())

    dut.s_awid.value = 5
    dut.s_awatop.value = 0x32
    dut.s_awvalid.value = 1
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.s_awready.value):
            break
    dut.s_awvalid.value = 0

    for i in range(4):
        await ClockCycles(dut.aclk, 3)
        dut.s_wlast.value = 1 if i == 3 else 0
        dut.s_wvalid.value = 1
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_wready.value):
                break
        dut.s_wvalid.value = 0
    dut.s_wlast.value = 0

    await ClockCycles(dut.aclk, 20)

    assert wlast_seen, "the W burst never completed; the test proved nothing"
    assert not early, (
        "BVALID asserted before the swallowed burst's WLAST. AXI requires the "
        "write data to be received before a write response is returned; the "
        "response slot must be COMMITTED at WLAST, not reserved at AW.")


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def atomic_filter_held_decerr_test(dut):
    """A swallowed atomic's DECERR held under backpressure must pop exactly once.

    The filter answers a swallowed (read-returning) atomic locally with DECERR
    from a small response queue, and holds the selection when the master
    backpressures so the presented payload cannot change mid-beat.

    The bug: the queue popped on `!m_bvalid && ... && s_bready` -- keyed on
    downstream being IDLE rather than on which source the master ACCEPTED.
    Hold a local DECERR with s_bready=0, let a downstream B arrive, then
    release: the master takes the DECERR while m_bvalid=1, so the pop
    condition is false and the SAME entry is presented again. The master gets
    a second B with no matching AW.

    Reproducing it needs all three: a swallowed atomic, backpressure across the
    presentation, and a downstream B arriving during that window.
    """
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.aresetn.value = 0
    dut.s_awvalid.value = 0
    dut.s_wvalid.value = 0
    dut.s_bready.value = 0
    for _ in range(5):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)

    fwd_aw, bresp_queue = [], []
    cocotb.start_soon(_downstream_model(dut, fwd_aw, bresp_queue))

    # 1. A swallowed atomic (read-returning ATOP) -> local DECERR queued.
    await _send_write(dut, awid=7, atop=0x32, beats=1)
    # 2. A plain write -> a downstream B will come back.
    await _send_write(dut, awid=9, atop=0x00, beats=1)

    # 3. Hold the master OFF so the DECERR is presented and held while the
    #    downstream B arrives underneath it.
    dut.s_bready.value = 0
    for _ in range(20):
        await RisingEdge(dut.aclk)

    # 4. Release and collect everything that comes out.
    seen = []
    dut.s_bready.value = 1
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if int(dut.s_bvalid.value) and int(dut.s_bready.value):
            seen.append((int(dut.s_bid.value), int(dut.s_bresp.value)))

    decerrs = [b for b in seen if b[1] == 3]
    assert len(decerrs) == 1, (
        f"expected exactly ONE DECERR for one swallowed atomic, saw "
        f"{len(decerrs)}: {seen}. A held local DECERR was accepted while a "
        f"downstream B was present, and the response queue was not popped, so "
        f"the same entry was presented again -- a duplicate B with no AW.")
    assert len(seen) == 2, (
        f"expected exactly two B responses (one DECERR, one downstream OKAY), "
        f"saw {len(seen)}: {seen}")


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def atomic_filter_test(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    for sig in ('s_awvalid', 's_wvalid', 's_wlast', 's_bready',
                'm_awready', 'm_wready', 'm_bvalid', 'm_bid', 'm_bresp',
                's_awid', 's_awatop'):
        getattr(dut, sig).value = 0
    dut.aresetn.value = 0
    await ClockCycles(dut.aclk, 5)
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 2)

    fwd_aw, ds_bresp = [], []
    cocotb.start_soon(_downstream_model(dut, fwd_aw, ds_bresp))
    dut.s_bready.value = 1

    b_seen = []
    cocotb.start_soon(_collect_b(dut, b_seen, 6))

    # 1. plain write (passes), 2. store-class atomic (passes),
    # 3. load-class atomic (swallowed), 4. swap (swallowed),
    # 5. plain write after the swallows (passes),
    # 6. multi-beat load-class (swallowed, 4 W beats discarded).
    await _send_write(dut, 0x1, ATOP_NONE, 1)
    await _send_write(dut, 0x2, ATOP_STORE, 2)
    await _send_write(dut, 0x3, ATOP_LOAD, 1)
    await _send_write(dut, 0x4, ATOP_SWAP, 1)
    await _send_write(dut, 0x5, ATOP_NONE, 1)
    await _send_write(dut, 0x6, ATOP_LOAD, 4)

    await ClockCycles(dut.aclk, 50)

    # ---------------------------------------------------------------------
    # B-channel payload stability under a stalled BVALID (qc round_31).
    #
    # The filter presents either a downstream B or a locally generated DECERR
    # on one set of s_b* wires. Before the selection hold, the mux was driven
    # combinationally by m_bvalid: a DECERR held under s_bready=0 had its
    # payload REPLACED the instant a downstream B arrived, so s_bid/s_bresp
    # changed while s_bvalid stayed high. No beat was lost, but that is the
    # AXI stability rule broken on the response channel, and a master is
    # entitled to sample BRESP on any cycle.
    #
    # The traffic above cannot reach this: it holds s_bready high throughout,
    # so no beat is ever presented-and-unaccepted. This phase stalls the
    # master deliberately, which is the only way the window opens.
    # ---------------------------------------------------------------------
    dut.s_bready.value = 0
    await ClockCycles(dut.aclk, 2)

    # Queue a local DECERR by swallowing a load-class atomic.
    await _send_write(dut, 0x7, ATOP_LOAD, 1)

    # Wait for it to be presented while the master stalls.
    for _ in range(50):
        await RisingEdge(dut.aclk)
        if int(dut.s_bvalid.value):
            break
    assert int(dut.s_bvalid.value), "no B presented to stall on"

    held = (int(dut.s_bid.value), int(dut.s_bresp.value))

    # Now make a downstream B available underneath the held beat. If the mux
    # is combinational this switches s_bid/s_bresp mid-valid.
    dut.m_bid.value = 0xE
    dut.m_bresp.value = 0            # OKAY, distinct from the held DECERR
    dut.m_bvalid.value = 1

    for cycle in range(8):
        await RisingEdge(dut.aclk)
        assert int(dut.s_bvalid.value), "s_bvalid dropped without a handshake"
        now = (int(dut.s_bid.value), int(dut.s_bresp.value))
        assert now == held, (
            f"B payload changed under a held VALID at cycle {cycle}: "
            f"{held} -> {now}. BID/BRESP must be stable from BVALID until "
            f"BREADY."
        )

    # Release: the held beat completes, then the downstream one follows.
    dut.s_bready.value = 1
    await ClockCycles(dut.aclk, 10)
    dut.m_bvalid.value = 0
    await ClockCycles(dut.aclk, 5)

    assert fwd_aw == [0x1, 0x2, 0x5], (
        f"forwarded AW set wrong: {[hex(x) for x in fwd_aw]}")
    assert len(b_seen) == 6, f"expected 6 B responses, saw {b_seen}"

    by_id = dict(b_seen)
    assert len(by_id) == 6, f"duplicate B ids: {b_seen}"
    for bid in (0x1, 0x2, 0x5):
        assert by_id[bid] == 0, f"forwarded id {bid:#x} not OKAY: {by_id[bid]}"
    for bid in (0x3, 0x4, 0x6):
        assert by_id[bid] == 3, f"swallowed id {bid:#x} not DECERR: {by_id[bid]}"

    # Same-ID B ordering within each class is preserved (queue order).
    local_order = [bid for bid, r in b_seen if r == 3]
    assert local_order == [0x3, 0x4, 0x6], f"local DECERR order: {local_order}"

    dut._log.info("axi5_atomic_filter: 3 forwarded / 3 swallowed, "
                  "DECERRs and W routing all correct")


async def _downstream_r_source(dut, queue, gap_rng):
    """Downstream R subordinate: drives each queued (rid, beats) burst toward
    the filter's R merge, holding each beat until m_rready as AXI requires."""
    dut.m_rvalid.value = 0
    while True:
        if not queue:
            await RisingEdge(dut.aclk)
            continue
        rid, beats = queue.pop(0)
        for i in range(beats):
            dut.m_rid.value = rid
            dut.m_rresp.value = 0
            dut.m_rlast.value = 1 if i == beats - 1 else 0
            dut.m_rvalid.value = 1
            while True:
                await RisingEdge(dut.aclk)
                if int(dut.m_rready.value):
                    break
            dut.m_rvalid.value = 0
            for _ in range(gap_rng.randint(0, 2)):
                await RisingEdge(dut.aclk)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def atomic_filter_read_return_r_test(dut):
    """A swallowed read-return atomic must still return its R beats.

    IHI 0022L A6.4.8: "For AtomicLoad, AtomicSwap, and AtomicCompare
    transactions: A Subordinate must send the correct number of read data
    transfers, even if the write response is DECERR or SLVERR", and it is
    highly recommended the error is signalled on the read response too.
    A6.4.7 sets the count: AWLEN+1 for Load/Swap, half that for a
    multi-transfer Compare. A compliant manager waits for those beats; a
    filter that answers on B only hangs it.

    Checks, per swallowed atomic: exact beat count, RID == AWID, RRESP ==
    DECERR on every beat, RLAST on the last beat only. Concurrently a
    downstream R stream shares the merged R channel under random master
    backpressure: its beats must arrive intact and in order, bursts from the
    two sources must not interleave, and the presented R payload must hold
    stable from RVALID to the handshake. B behaviour is re-checked: one
    DECERR per swallowed atomic, OKAY for the forwarded store.
    """
    rng = random.Random(int(os.environ.get('SEED', '1')))
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    for sig in ('s_awvalid', 's_wvalid', 's_wlast', 's_bready', 's_awid',
                's_awatop', 'm_bvalid', 'm_bid', 'm_bresp'):
        getattr(dut, sig).value = 0
    assert hasattr(dut, 's_rvalid'), (
        "axi5_atomic_filter has no R channel: a read-return atomic it "
        "swallows can never receive its read data (IHI 0022L A6.4.8)")
    for sig in ('m_rvalid', 'm_rid', 'm_rresp', 'm_rlast', 's_rready'):
        getattr(dut, sig).value = 0
    dut.aresetn.value = 0
    await ClockCycles(dut.aclk, 5)
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 2)

    fwd_aw, ds_bresp = [], []
    cocotb.start_soon(_downstream_model(dut, fwd_aw, ds_bresp))
    dut.s_bready.value = 1

    r_beats = []          # (rid, rresp, rlast) in accept order
    b_seen = []
    stability_errors = []

    async def _r_master():
        # Drive RREADY at the falling edge, then sample the settled
        # valid/ready/payload in that same timestep: those are the values
        # the next rising edge sees, so v && r there IS the handshake.
        held = None
        while True:
            await FallingEdge(dut.aclk)
            dut.s_rready.value = 1 if rng.random() < 0.6 else 0
            await ReadOnly()
            v = int(dut.s_rvalid.value)
            r = int(dut.s_rready.value)
            now = (int(dut.s_rid.value), int(dut.s_rresp.value),
                   int(dut.s_rlast.value))
            if held is not None and v and now != held:
                stability_errors.append((held, now))
            if v and r:
                r_beats.append(now)
                held = None
            else:
                held = now if v else None
            await RisingEdge(dut.aclk)

    async def _b_master():
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_bvalid.value) and int(dut.s_bready.value):
                b_seen.append((int(dut.s_bid.value), int(dut.s_bresp.value)))

    ds_queue = []
    cocotb.start_soon(_r_master())
    cocotb.start_soon(_b_master())
    cocotb.start_soon(_downstream_r_source(dut, ds_queue, rng))

    expected_local = {}   # id -> beats
    ds_bursts = {}        # id -> beats
    store_ids = []
    for _ in range(_ROUNDS):
        plan = [
            (ATOP_LOAD, 1),   # 8-byte AtomicLoad on a 32-bit bus: 2 W, 2 R
            (ATOP_SWAP, 0),
            (ATOP_CMP, 3),    # 16-byte compare (8+8): 4 W beats -> 2 R beats
            (ATOP_CMP, 0),    # single-transfer compare -> 1 R beat
            (ATOP_CMP, 7),    # 32-byte compare: 8 W beats -> 4 R beats
            (ATOP_LOAD, 0),
            (ATOP_STORE, 0),  # forwarded: no local R
        ]
        rng.shuffle(plan)
        # IDs are unique-in-flight within a round (A6.4.4); each round drains
        # before the next one reuses them.
        # The forwarded store gets a reserved ID so it can never be confused
        # with a swallowed atomic of another round.
        for aid, (atop, awlen) in enumerate(plan, start=1):
            if atop == ATOP_STORE:
                aid = 13
                store_ids.append(aid)
            else:
                expected_local[aid] = expected_local.get(aid, [])
                expected_local[aid].append(_expected_r_beats(atop, awlen))
            await _send_write(dut, aid, atop, awlen + 1)
            # A downstream read burst lands in the middle of local traffic.
            if rng.random() < 0.5:
                dsid = 14 + rng.randint(0, 1)
                nb = rng.randint(1, 4)
                ds_bursts.setdefault(dsid, []).append(nb)
                ds_queue.append((dsid, nb))
        await ClockCycles(dut.aclk, 120)

    await ClockCycles(dut.aclk, 200)

    assert not stability_errors, (
        f"R payload changed under a held RVALID: {stability_errors[:4]}")

    # Split the accepted stream into bursts; a burst must not be interleaved
    # with the other source's beats.
    bursts = []
    cur = []
    for beat in r_beats:
        if cur and beat[0] != cur[0][0]:
            raise AssertionError(
                f"R bursts interleaved: id {beat[0]:#x} beat arrived inside "
                f"an open burst of id {cur[0][0]:#x}. Stream: {r_beats}")
        cur.append(beat)
        if beat[2]:
            bursts.append(cur)
            cur = []
    assert not cur, f"R stream ended mid-burst: {cur}"

    got_local, got_ds = {}, {}
    for b in bursts:
        rid = b[0][0]
        if rid >= 14:
            assert all(x[1] == 0 for x in b), f"downstream burst resp corrupted: {b}"
            got_ds.setdefault(rid, []).append(len(b))
        else:
            assert all(x[1] == 3 for x in b), (
                f"local read-return beat not DECERR (A6.4.8 recommends the "
                f"error on the read response too): {b}")
            got_local.setdefault(rid, []).append(len(b))

    assert got_local == expected_local, (
        f"read-return atomics got the wrong R beats.\n expected {expected_local}"
        f"\n got      {got_local}")
    assert got_ds == ds_bursts, (
        f"downstream R bursts damaged by the merge: expected {ds_bursts}, "
        f"got {got_ds}")
    for sid in set(store_ids):
        assert sid not in got_local, f"forwarded AtomicStore id {sid} got a local R"

    n_swallowed = sum(len(v) for v in expected_local.values())
    decerrs = [b for b in b_seen if b[1] == 3]
    okays = [b for b in b_seen if b[1] == 0]
    assert len(decerrs) == n_swallowed, (
        f"expected {n_swallowed} DECERR B responses, got {len(decerrs)}")
    assert len(okays) == len(store_ids), (
        f"expected {len(store_ids)} forwarded B responses, got {len(okays)}")
    dut._log.info(f"axi5_atomic_filter R path: {n_swallowed} read-return "
                  f"atomics answered with {sum(sum(v) for v in got_local.values())} "
                  f"R beats; {sum(sum(v) for v in got_ds.values())} downstream "
                  f"R beats merged intact")


def test_axi5_atomic_filter(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi5': 'rtl/amba/axi5',
    })

    dut_name = "axi5_atomic_filter"
    # Sources come from the DUT's filelist rather than a private copy of its
    # dependency list -- a hand-list is invisible to filelist_registry --check.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'rtl/amba/filelists/{dut_name}.f')

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}{worker_suffix}"

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
        # No testcase= filter: every cocotb test in this module is wanted. The
        # comma list this used to pass ran ZERO tests under cocotb 2.x (the
        # repo conftest anchors testcase= as one exact name) and still
        # reported PASS.
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'func'),
            'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **waves['extra_env'],
        },
    )
