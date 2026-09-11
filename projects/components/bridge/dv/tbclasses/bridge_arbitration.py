"""Shared multi-master arbitration body for the bridge tests.

Every bridge test file carried an `..._arbitration` cocotb test whose body was
`# TODO: Implement concurrent transaction test` followed by 100 idle clocks and
an unconditional "PASSED" log. Seven of them, each counting toward the suite's
green number while asserting nothing -- and concurrent multi-master traffic to
one slave is exactly the shape that exposes BRIDGE-011, which is why a
16-entry response-tracking FIFO could be overrun for the life of the design
without a single test noticing.

The body below is config-driven rather than per-bridge: it discovers masters
and slaves from the TB attributes every bridge TB already defines
(`num_masters`, `slave_info`, `master_wr` / `master_rd` / `master_apb` / `master_wb`,
`master_data_width`), so one implementation covers 2x2, 4x4, 5x3 and the mixed
configs without hand-writing an address map seven times.

What it actually checks, beyond "did it hang":

  * every concurrently issued transaction COMPLETES -- a response routed to
    the wrong master leaves the right one waiting forever;
  * each master reads back THE DATA IT WROTE. Read data returned to the wrong
    master is invisible to a completion count (misroutes come in pairs, so the
    counts still balance) but shows up immediately as one master seeing
    another's payload;
  * the slave's memory holds each master's value at that master's own address.

The slave is made SLOW on purpose. With the default BFM answering in about a
cycle, outstanding depth never builds and the interesting states are never
reached.
"""

from cocotb.triggers import ClockCycles


def set_slave_response_delay(tb, slave_idx: int, cycles: int) -> None:
    """Hold responses off at `slave_idx` so requests stack up in the bridge.

    Reaches into the slave BFMs directly rather than requiring every one of
    the bridge TB classes to grow the same setter.
    """
    # The generated TB grew its own setter (it also knows the protocol
    # families whose slave BFM has no response_delay_cycles -- WB4Slave takes
    # a randomizer profile); prefer it, fall back to the AXI attribute poke
    # for TB classes without one.
    setter = getattr(tb, 'set_slave_response_delay', None)
    if callable(setter):
        setter(slave_idx, cycles)
        return
    for container in ('slave_wr', 'slave_rd'):
        bfms = getattr(tb, container, None)
        if bfms and slave_idx in bfms:
            try:
                bfms[slave_idx].response_delay_cycles = cycles
            except AttributeError:
                pass


# Single-handle master families (one BFM carries both directions). A family
# missing here is invisible to this helper: the WB4 fixture's arbitration
# test saw ONE master and skipped both phases -- and, to its credit, refused
# to report success on zero work (BRIDGE-019).
_RW_HANDLE_CONTAINERS = ('master_apb', 'master_wb')


def _writable_masters(tb):
    m = set(getattr(tb, 'master_wr', {}) or {})
    for c in _RW_HANDLE_CONTAINERS:
        m |= set(getattr(tb, c, {}) or {})
    return sorted(m)


def _readable_masters(tb):
    m = set(getattr(tb, 'master_rd', {}) or {})
    for c in _RW_HANDLE_CONTAINERS:
        m |= set(getattr(tb, c, {}) or {})
    return sorted(m)


def _connectivity(tb):
    """master_idx -> set of reachable slave_idx, read from the bridge's own
    connectivity CSV.

    The matrix is SPARSE and assuming otherwise is a silent wrong answer, not
    an error: in bridge_4x4_rw, dma1_master cannot reach periph_slave, so a
    write there is absorbed by the subtractive slave (DECERR, write dropped)
    and the target memory simply keeps its seed. That reads exactly like data
    corruption when you compare against what you meant to write.

    Returns None when the CSV cannot be found, and the caller then falls back
    to assuming full connectivity.
    """
    import csv, glob, os, pathlib
    name = getattr(getattr(tb, 'dut', None), '_name', None)
    if not name:
        return None
    gen = (pathlib.Path(__file__).resolve().parents[2] / 'rtl' / 'generated' / name)
    if not gen.is_dir():
        return None
    hits = sorted(glob.glob(os.path.join(str(gen), '*_connectivity.csv')))
    if not hits:
        return None
    reach = {}
    with open(hits[0], newline='') as fh:
        rows = list(csv.reader(fh))
    for m, row in enumerate(rows[1:]):
        reach[m] = {s for s, cell in enumerate(row[1:]) if cell.strip() == '1'}
    return reach


def _pick_slave(tb, candidates):
    """Pick the slave the MOST of `candidates` can actually reach, preferring
    a wide AXI4 port -- APB is narrow and slow and throttles the traffic
    before any interesting depth is reached.

    Returns (slave_idx, masters_that_can_reach_it).
    """
    info = getattr(tb, 'slave_info', {}) or {}
    if not info:
        return 0, list(candidates)
    reach = _connectivity(tb)
    best = None
    for s in sorted(info):
        if reach is None:
            ms = list(candidates)
        else:
            ms = [m for m in candidates if s in reach.get(m, set())]
        # prefer more masters, then AXI4 over APB, then the wider port
        key = (len(ms), 1 if info[s][0].startswith('axi') else 0, info[s][3])
        if best is None or key > best[0]:
            best = (key, s, ms)
    return best[1], best[2]


def _align(tb, master_idx, slave_idx):
    mb = tb.master_data_width[master_idx] // 8
    sb = tb.slave_info[slave_idx][3] // 8
    return max(mb, sb)


async def run_arbitration(tb, per_master: int = 6, resp_delay: int = 40,
                          slave_idx: int = None):
    """Concurrent traffic from every master to ONE slave, then verified reads.

    Returns the number of transactions checked so the caller can log it and so
    a body that silently degenerated to zero work cannot report success.
    """
    import cocotb

    writers = _writable_masters(tb)
    readers = _readable_masters(tb)
    reachable = sorted(set(writers) | set(readers))

    if slave_idx is None:
        slave_idx, can_reach = _pick_slave(tb, reachable)
    else:
        reach = _connectivity(tb)
        can_reach = ([m for m in reachable if slave_idx in reach.get(m, set())]
                     if reach is not None else reachable)

    # Only masters WIRED to this slave take part. One that is not gets a
    # DECERR from the subtractive slave and its write silently does nothing.
    writers = [m for m in writers if m in can_reach]
    readers = [m for m in readers if m in can_reach]

    base = tb.slave_info[slave_idx][1]

    tb.log.info(f"arbitration: slave {slave_idx} @ 0x{base:08x}, "
                f"writers={writers}, readers={readers}, "
                f"{per_master} txn/master, resp_delay={resp_delay}")

    set_slave_response_delay(tb, slave_idx, resp_delay)

    # ---- Phase 1: concurrent writes from every writing master -------------
    plan = []
    for m in writers:
        align = _align(tb, m, slave_idx)
        for i in range(per_master):
            addr = base + (m + 1) * 0x400 + i * align
            plan.append((m, addr, 0xA5000000 | (m << 12) | i))

    checked = 0
    if len(writers) >= 2:
        done = []

        async def _w(m, addr, data):
            await tb.master_write(m, addr, data)
            done.append((m, addr, data))

        for (m, addr, data) in plan:
            cocotb.start_soon(_w(m, addr, data))

        for _ in range(6000):
            if len(done) == len(plan):
                break
            await ClockCycles(tb.clock, 10)

        if len(done) != len(plan):
            per = {}
            for (m, _a, _d) in done:
                per[m] = per.get(m, 0) + 1
            raise AssertionError(
                f"arbitration: only {len(done)}/{len(plan)} concurrent writes "
                f"completed (per master: {per}). A response never reached the "
                f"master that issued it.")

        for (m, addr, data) in plan:
            actual = tb.slave_mem_read(slave_idx, addr, master_idx=m)
            assert actual == data, (
                f"arbitration: slave {slave_idx} memory at 0x{addr:08x} holds "
                f"0x{actual:08x}, master {m} wrote 0x{data:08x} -- concurrent "
                f"writes from other masters corrupted this one.")
        checked += len(plan)
    else:
        tb.log.info(f"arbitration: {len(writers)} writing master(s) -- "
                    f"write phase needs 2+, skipping to reads")

    # ---- Phase 2: concurrent reads, each master verifying its OWN data ----
    # This is the phase that catches a response routed to the wrong master:
    # a completion count cannot see it, but reading another master's payload
    # is unmistakable.
    if len(readers) >= 2:
        read_plan = []
        for m in readers:
            align = _align(tb, m, slave_idx)
            for i in range(per_master):
                addr = base + (m + 1) * 0x400 + i * align
                if len(writers) >= 2 and m in writers:
                    expect = 0xA5000000 | (m << 12) | i
                elif tb.is_seeded(slave_idx, addr):
                    expect = tb.expected_pattern(slave_idx, addr)
                else:
                    continue
                read_plan.append((m, addr, expect))

        mismatches = []
        rdone = []

        async def _r(m, addr, expect):
            got = await tb.master_read(m, addr)
            if got != expect:
                mismatches.append((m, addr, got, expect))
            rdone.append(m)

        for (m, addr, expect) in read_plan:
            cocotb.start_soon(_r(m, addr, expect))

        for _ in range(6000):
            if len(rdone) == len(read_plan):
                break
            await ClockCycles(tb.clock, 10)

        assert len(rdone) == len(read_plan), (
            f"arbitration: only {len(rdone)}/{len(read_plan)} concurrent reads "
            f"completed -- read data never reached the master that asked.")

        if mismatches:
            m, addr, got, expect = mismatches[0]
            raise AssertionError(
                f"arbitration: {len(mismatches)} read(s) returned the wrong "
                f"data. First: master {m} read 0x{addr:08x} and got "
                f"0x{got:08x}, expected 0x{expect:08x} -- read data was "
                f"routed to the wrong master.")
        checked += len(read_plan)
    else:
        tb.log.info(f"arbitration: {len(readers)} reading master(s) -- "
                    f"read phase needs 2+, skipped")

    assert checked > 0, (
        "arbitration checked NOTHING -- fewer than two masters could both "
        "write and read, so this config needs a hand-written body rather "
        "than a test that reports success for doing no work.")

    set_slave_response_delay(tb, slave_idx, 1)
    tb.log.info(f"arbitration: {checked} concurrent transactions verified")
    return checked
