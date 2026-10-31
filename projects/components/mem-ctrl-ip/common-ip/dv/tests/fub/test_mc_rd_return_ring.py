# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
FUB test: mc_rd_return_ring (common-ip) -- the AR-order read-return ring,
with read combining (pumice TASK-060).

The ring hands out a ticket per admitted read in AR order, takes the issue
notify in whatever order the scheduler picked, fills each DFI return (issue
order) into its ticket's slot, and drains from the head in AR order once the
head's data is complete. A ticket allocated with alloc_merge is a SHADOW of
an older, unissued ticket: it is never issued or filled, becomes ready with
its source's return, and drains the source's beats from the source's slot.
The source slot is PINNED (the tail will not re-allocate it) until every
shadow of it has been fetched.

Two cells:

  * `pin`: the directed hazard. Fill the ring (depth 8) with a source, its
    shadow and six more reads; return everything; drain the source and the
    shadow's first two beats, then stall the drain with a ninth read waiting
    on alloc. The source's slot is free (head moved on) but the shadow's
    last two beats are still unfetched in it, so alloc_ready must stay LOW
    for as long as the drain is stalled -- a ring without the pin hands the
    slot to the ninth read, whose return then overwrites the beats the
    shadow has not fetched yet. Then release the drain: the shadow's tail
    beats carry the source's data, the pin lifts, the ninth read allocates.
  * `random`: a model-driven walk. Random allocs (30% shadows of a random
    unissued source), issues in random order, DFI returns in issue order
    after random delays, a drain that stalls at random (sometimes for 30
    cycles, which is what opens pin windows). Every drained beat is checked
    against the AR-order expectation (a shadow yields its source's data and
    resp), and the walk must finish within the cycle budget (no deadlock
    behind a pin).

Production change that fails `pin`: dropping the pin (alloc_ready goes high
with the shadow unfetched). Production change that fails `random`: a shadow
that fetches its own empty slot, a shadow that never becomes ready, a merge
that pushes the shadow into the issue FIFO, AR order broken by a merge.

Levels: TEST_LEVEL gate = 150 allocs, func = 1500, full = 6000; two
geometries (1 and 4 beats per burst).
"""
import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Timer

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_rd_return_ring_fub.f")

DEPTH = 8
DW = 32


def _bpb():
    return int(os.environ.get("RING_BPB", "4"))


async def _reset(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, unit="ns").start())
    dut.aresetn.value = 0
    dut.alloc_valid_i.value = 0
    dut.alloc_merge_i.value = 0
    dut.alloc_src_i.value = 0
    dut.issue_valid_i.value = 0
    dut.issue_ticket_i.value = 0
    dut.dfi_ret_valid_i.value = 0
    dut.dfi_ret_data_i.value = 0
    dut.dfi_ret_resp_i.value = 0
    dut.dfi_ret_last_i.value = 0
    dut.drain_ready_i.value = 0
    for _ in range(5):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)
    await Timer(1, "ns")


async def _tick(dut):
    """Sample the handshakes that will fire at the coming edge, take the
    edge, step past it so the next drive is clean. Returns the fires."""
    await ReadOnly()
    f = dict(
        alloc=int(dut.alloc_valid_i.value) and int(dut.alloc_ready_o.value),
        ticket=int(dut.alloc_ticket_o.value),
        issue=int(dut.issue_valid_i.value) and int(dut.issue_ready_o.value),
        ret=int(dut.dfi_ret_valid_i.value) and int(dut.dfi_ret_ready_o.value),
        drain=int(dut.drain_valid_o.value) and int(dut.drain_ready_i.value),
        ddata=int(dut.drain_data_o.value), dresp=int(dut.drain_resp_o.value),
        dlast=int(dut.drain_last_o.value),
        aready=int(dut.alloc_ready_o.value),
    )
    await RisingEdge(dut.aclk)
    await Timer(1, "ns")
    return f


class _Entry:
    __slots__ = ("ticket", "shadow", "src", "data", "resp", "issued", "returned")

    def __init__(self, ticket, data, resp, shadow=False, src=None):
        self.ticket, self.data, self.resp = ticket, data, resp
        self.shadow, self.src = shadow, src
        self.issued = self.returned = False

    def beats(self):
        e = self.src if self.shadow else self
        return e.data, e.resp


async def _drain_exact(dut, expect, n, allocs=None):
    """Consume exactly n beats with the drain ready, checking each. An alloc
    that fires meanwhile (alloc_valid left raised by the caller) is recorded
    in `allocs` and the request dropped, so it fires once."""
    got = 0
    guard = 0
    while got < n:
        dut.drain_ready_i.value = 1
        f = await _tick(dut)
        guard += 1
        assert guard < 500, "drain stalled"
        if f["alloc"]:
            assert allocs is not None, "unexpected alloc during a drain"
            allocs.append(f["ticket"])
            dut.alloc_valid_i.value = 0
        if f["drain"]:
            data, resp, last = expect.popleft()
            assert f["ddata"] == data and f["dresp"] == resp and f["dlast"] == last, (
                f"beat {got}: got {f['ddata']:#x}/{f['dresp']}/{f['dlast']} "
                f"expected {data:#x}/{resp}/{last}")
            got += 1
    dut.drain_ready_i.value = 0


def _expect_beats(entry, bpb):
    data, resp = entry.beats()
    return [(data[b], resp, int(b == bpb - 1)) for b in range(bpb)]


async def _alloc(dut, merge=0, src=0):
    dut.alloc_valid_i.value = 1
    dut.alloc_merge_i.value = merge
    dut.alloc_src_i.value = src
    for _ in range(50):
        f = await _tick(dut)
        if f["alloc"]:
            dut.alloc_valid_i.value = 0
            dut.alloc_merge_i.value = 0
            return f["ticket"]
    raise AssertionError("alloc never fired")


async def _issue(dut, ticket):
    dut.issue_valid_i.value = 1
    dut.issue_ticket_i.value = ticket
    for _ in range(50):
        f = await _tick(dut)
        if f["issue"]:
            dut.issue_valid_i.value = 0
            return
    raise AssertionError("issue never fired")


async def _return(dut, data, resp, bpb):
    for b in range(bpb):
        dut.dfi_ret_valid_i.value = 1
        dut.dfi_ret_data_i.value = data[b]
        dut.dfi_ret_resp_i.value = resp
        dut.dfi_ret_last_i.value = int(b == bpb - 1)
        for _ in range(50):
            f = await _tick(dut)
            if f["ret"]:
                break
        else:
            raise AssertionError("DFI return beat never accepted")
    dut.dfi_ret_valid_i.value = 0
    dut.dfi_ret_last_i.value = 0


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_ring_pin(dut):
    bpb = _bpb()
    rng = random.Random(int(os.environ.get("SEED", "3")))
    mk = lambda: [rng.randrange(1 << DW) for _ in range(bpb)]
    await _reset(dut)

    # source A (ticket 0), its shadow A' (ticket 1), six more: the ring is full
    ents = []
    a = _Entry(await _alloc(dut), mk(), 0)
    ents.append(a)
    ash = _Entry(await _alloc(dut, merge=1, src=a.ticket), None, None, shadow=True, src=a)
    ents.append(ash)
    for _ in range(DEPTH - 2):
        ents.append(_Entry(await _alloc(dut), mk(), 0))
    dut.alloc_valid_i.value = 1          # a ninth read waits on alloc from here on
    f = await _tick(dut)
    assert not f["alloc"] and not f["aready"], "ring full but alloc_ready high"

    # issue and return everything except the shadow (which has no burst)
    for e in ents:
        if not e.shadow:
            await _issue(dut, e.ticket)
    for e in ents:
        if not e.shadow:
            await _return(dut, e.data, e.resp, bpb)

    # Drain the source and the first `half` beats of the shadow, then stall.
    # The fetch runs SKID beats ahead of the drain, so after the stall the
    # shadow's beats half .. half+SKID-1 sit in the skid (fetched, safe) and
    # beats from half+SKID on are still unfetched in the source's slot. The
    # pin is observable only when at least one beat is unfetched: bpb > SKID
    # (4-beat geometry); at one beat per burst the shadow is always fetched
    # within a cycle of its source's free and the walk just checks data.
    SKID = 2
    half = max(bpb - SKID - 1, 0)
    unfetched = bpb - half - SKID
    exp = deque(_expect_beats(a, bpb) + _expect_beats(ash, bpb))
    await _drain_exact(dut, exp, bpb + half)
    # The source's slot is free (head moved past it) but the shadow is not
    # fully fetched: the ninth read must NOT be allocated for as long as the
    # drain is stalled.
    if unfetched > 0:
        for cyc in range(40):
            f = await _tick(dut)
            assert not f["alloc"] and not f["aready"], (
                f"cycle {cyc} of the stall: alloc_ready high with the shadow's beats "
                f"{half + SKID}..{bpb - 1} still unfetched in the source's slot (pin lost)")
    # release the drain: the shadow's remaining beats are the source's; the
    # pin lifts as its last beat is fetched and the ninth read allocates into
    # the source's old slot (during the drain, or just after it)
    allocs = []
    await _drain_exact(dut, exp, bpb - half, allocs)
    for _ in range(20):
        if allocs:
            break
        f = await _tick(dut)
        if f["alloc"]:
            allocs.append(f["ticket"])
            dut.alloc_valid_i.value = 0
    dut.alloc_valid_i.value = 0
    assert allocs == [a.ticket], f"ninth read allocated {allocs}, expected the freed slot [{a.ticket}]"
    nth = allocs[0]
    n = _Entry(nth, mk(), 2)
    await _issue(dut, n.ticket)
    await _return(dut, n.data, n.resp, bpb)
    exp = deque(sum((_expect_beats(e, bpb) for e in ents[2:]), []) + _expect_beats(n, bpb))
    await _drain_exact(dut, exp, (DEPTH - 2 + 1) * bpb)
    dut._log.info("PASS pin: shadow drained its source's %d beats across a stall; alloc held", bpb)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_ring_random(dut):
    bpb = _bpb()
    level = os.environ.get("TEST_LEVEL", "gate").lower()
    n_alloc = {"gate": 150, "func": 1500, "full": 6000}.get(level, 150)
    rng = random.Random(int(os.environ.get("SEED", "11")))
    await _reset(dut)

    ring = deque()            # allocated entries, AR order (head first)
    live = []                 # allocated, in the ring, not yet drained (any order)
    issue_q = deque()         # issued, awaiting their DFI return (issue order)
    expect = deque()          # (data, resp, last) in AR order
    allocs = drained = merges = 0
    next_ticket = 0
    ret_cur, ret_beat, ret_delay = None, 0, 0
    stall = 0
    idle = 0
    cycles = 0
    pending_alloc = None      # (merge, src_entry) being presented
    pending_issue = None

    while drained < n_alloc * bpb:
        cycles += 1
        assert cycles < n_alloc * 60 + 5000, (
            f"walk stuck: {allocs} allocs, {drained} beats drained, ring {len(ring)}, "
            f"issue_q {len(issue_q)}")
        # ---- alloc: keep presenting one request until it fires ----
        if pending_alloc is None and allocs < n_alloc and rng.random() < 0.5:
            cands = [e for e in live if not e.shadow and not e.issued]
            # The seed is per run (conftest pins it per node id from a rolled
            # base), and a walk whose sources all issue before the next alloc
            # lands has no candidates when the 30 percent fires: one gate-level
            # run rolled 150 allocs with no shadow at all (2026-10-30) and the
            # final assertion turned a stimulus gap into a red test. Past the
            # half-way point a candidate is taken whenever one exists, so every
            # seed exercises the combiner path at least once.
            force = (merges == 0 and allocs >= n_alloc // 2)
            if cands and (force or rng.random() < 0.3):
                pending_alloc = (1, rng.choice(cands))
            else:
                pending_alloc = (0, None)
        if pending_alloc is not None and pending_alloc[0] and pending_alloc[1].issued:
            # The CAM re-matches every cycle a waiting insert is presented: a
            # source that issued meanwhile is no longer live, so the request
            # becomes a plain read (an issue in the SAME cycle as the alloc
            # still merges -- the match sees the entry before it frees).
            pending_alloc = (0, None)
        if pending_alloc is not None:
            dut.alloc_valid_i.value = 1
            dut.alloc_merge_i.value = pending_alloc[0]
            dut.alloc_src_i.value = pending_alloc[1].ticket if pending_alloc[1] else 0
        else:
            dut.alloc_valid_i.value = 0
            dut.alloc_merge_i.value = 0
        # ---- issue: a random unissued non-shadow entry allocated earlier ----
        if pending_issue is None and rng.random() < 0.5:
            cands = [e for e in live if not e.shadow and not e.issued]
            if cands:
                pending_issue = rng.choice(cands)
        if pending_issue is not None:
            dut.issue_valid_i.value = 1
            dut.issue_ticket_i.value = pending_issue.ticket
        else:
            dut.issue_valid_i.value = 0
        # ---- DFI return: issue order, random start delay, beats back to back ----
        if ret_cur is None and issue_q:
            if ret_delay == 0:
                ret_cur, ret_beat = issue_q.popleft(), 0
                ret_delay = rng.randrange(4)
            else:
                ret_delay -= 1
        if ret_cur is not None:
            dut.dfi_ret_valid_i.value = 1
            dut.dfi_ret_data_i.value = ret_cur.data[ret_beat]
            dut.dfi_ret_resp_i.value = ret_cur.resp
            dut.dfi_ret_last_i.value = int(ret_beat == bpb - 1)
        else:
            dut.dfi_ret_valid_i.value = 0
            dut.dfi_ret_last_i.value = 0
        # ---- drain: random ready with occasional long stalls ----
        if stall:
            stall -= 1
            dut.drain_ready_i.value = 0
        elif rng.random() < 0.04:
            stall = 30
            dut.drain_ready_i.value = 0
        else:
            dut.drain_ready_i.value = int(rng.random() < 0.6)

        f = await _tick(dut)

        if f["alloc"]:
            merge, src = pending_alloc
            assert f["ticket"] == next_ticket % DEPTH, (
                f"ticket {f['ticket']} != expected tail {next_ticket % DEPTH}")
            if merge:
                e = _Entry(f["ticket"], None, None, shadow=True, src=src)
                merges += 1
            else:
                e = _Entry(f["ticket"], [rng.randrange(1 << DW) for _ in range(bpb)],
                           rng.choice((0, 0, 0, 2)))
            ring.append(e); live.append(e)
            expect.extend(_expect_beats(e, bpb))
            next_ticket += 1; allocs += 1
            pending_alloc = None
        if f["issue"]:
            pending_issue.issued = True
            issue_q.append(pending_issue)
            pending_issue = None
        if f["ret"]:
            if ret_beat == bpb - 1:
                ret_cur.returned = True
                ret_cur = None
            else:
                ret_beat += 1
        if f["drain"]:
            data, resp, last = expect.popleft()
            assert (f["ddata"], f["dresp"], f["dlast"]) == (data, resp, last), (
                f"beat {drained}: got {f['ddata']:#x}/{f['dresp']}/{f['dlast']} "
                f"expected {data:#x}/{resp}/{last} (head ticket {ring[0].ticket}, "
                f"shadow={ring[0].shadow})")
            drained += 1
            if last:
                e = ring.popleft(); live.remove(e)
    # a merged source may be chosen while it is being issued the same cycle:
    # allowed (the CAM matches on the live entry), so no assertion on that.
    dut._log.info("PASS random: %d allocs (%d shadows), %d beats drained in %d cycles, bpb=%d",
                  allocs, merges, drained, cycles, bpb)
    assert merges > 0, "the walk produced no shadows; the combiner path was not exercised"


@pytest.mark.parametrize("byp", [0, 1])
@pytest.mark.parametrize("mark", [0, 1])
@pytest.mark.parametrize("bpb", [1, 4])
@pytest.mark.parametrize("cell", ["pin", "random"])
def test_mc_rd_return_ring(request, bpb, cell, mark, byp):
    """MERGE_MARK_REG both states: 1 = a shadow's marking lands the cycle after
    its allocation (granite's merge build, 100 MHz closure, 2026-10-30).
    RET_BYPASS both states: 1 = the next beat in ring order goes from the
    return straight into the output skid (granite TASK-003, 2026-10-31)."""
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_rd_return_ring"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"DEPTH": str(DEPTH), "AXI_DATA_WIDTH": str(DW), "AXI_BEATS_PER_BURST": str(bpb),
              "MERGE_MARK_REG": str(mark), "RET_BYPASS": str(byp)}
    extra_env = {"DUT": dut_name,
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
                 "TEST_LEVEL": os.environ.get("TEST_LEVEL", "gate"),
                 "SEED": os.environ.get("SEED", "11"),
                 "RING_BPB": str(bpb)}
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=f"cocotb_test_ring_{cell}",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
