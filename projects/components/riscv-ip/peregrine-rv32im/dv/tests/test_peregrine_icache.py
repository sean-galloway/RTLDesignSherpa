# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_icache
# Purpose: peregrine_icache unit test (PRD P9, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_icache: hits, misses, conflicts, invalidate, random streams.

Directed phases (every level), each with an exact AR-burst count:
  cold sweep    every word of the 4 KiB once: one burst per line (64)
  warm sweep    the same again: no burst
  conflict      two addresses 4 KiB apart, alternating: a burst every fetch
  invalidate    inv_req, then the warm sweep again: one burst per line
  last-beat     a miss on each line's last word (the replay cycle's case)
  inv in refill inv_req raised while a refill is in flight: acked only after
  fetch faults  (TASK-005) a DECERR line: one refill, every fetch from it
                faults; the line is not installed (fetching it later
                refills); a failed refill over a valid line clears the set;
                one SLVERR beat fails the whole line; an invalidate while a
                faulted line is being fetched is taken
Random phase (func: 3000 fetches, full: 20000), slow memory: sequential runs
with random jumps over a 16 KiB working set, invalidates at random points;
every fetched word is checked against the memory model.
"""

import os
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.peregrine.icache_tb import IcacheTB    # noqa: E402

SIZE = 4096
LINE = 64


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_peregrine_icache(dut):
    level = os.environ.get("TEST_LEVEL", "gate")
    seed = int(os.environ.get("RDS_SEED_BASE", "1"))
    tb = IcacheTB(dut, size_bytes=SIZE, line_bytes=LINE, seed=seed)
    tb.set_profile("fast")
    await tb.setup_clocks_and_reset()

    sweep = list(range(4, SIZE, 4))          # pc starts at 0

    async def phase(name, stream, want_ars, inv_at=(), inv_when_busy=False, hold_pct=0):
        before = tb.ars
        await tb.fetch(stream, inv_at=inv_at, inv_when_busy=inv_when_busy,
                       hold_pct=hold_pct)
        got = tb.ars - before
        dut._log.info(f"{name}: {len(stream)} fetches, {got} refills")
        assert got == want_ars, f"{name}: {got} refills, expected {want_ars}"

    await phase("cold sweep", sweep, SIZE // LINE)
    await phase("warm sweep", [0] + sweep, 0)
    alt = [SIZE if i % 2 == 0 else 0 for i in range(16)]
    await phase("conflict", alt, 16)
    # Invalidate at the first fetch, then sweep: every line misses again.
    await phase("invalidate", [0] + sweep, SIZE // LINE, inv_at=(0,))
    assert tb.inv_acks == 1, f"{tb.inv_acks} invalidate acks, expected 1"
    # A miss on the last word of a line: that word arrives on the last
    # beat, the same edge the replay re-reads it, so it needs the replay.
    last = [5 * SIZE + i * LINE + LINE - 4 for i in range(8)]
    await phase("last-beat miss", last, 8)
    # inv_req raised while a refill is in flight: the refill completes,
    # then the invalidate, so the same line misses again (2 refills).
    tb.set_profile("normal")
    await phase("inv in refill", [3 * SIZE, 3 * SIZE + 4], 2, inv_at=(1,),
                inv_when_busy=True)
    assert tb.inv_acks == 2
    # Holds from elsewhere (the D side) on 30% of cycles: the read registers
    # keep the PC's word under a hold the cache did not cause, through
    # misses, replays and hits (TASK-001 stage 7: mem_wait is their enable).
    tb.set_profile("fast")
    # The previous phase leaves the PC at 3*SIZE+4: the invalidate is taken
    # before the PC moves, so that line refills once more (the plain
    # "invalidate" phase starts from PC 0, inside the sweep).
    await phase("held sweep", [0] + sweep, SIZE // LINE + 1, inv_at=(0,), hold_pct=30)
    assert tb.inv_acks == 3
    await phase("held last-beat", [7 * SIZE + i * LINE + LINE - 4 for i in range(8)], 8,
                hold_pct=30)

    # Fetch faults (TASK-005).  The PC is in index 7 here.
    bad = 9 * SIZE                                  # DECERR line, index 0
    tb.bad_lines.add(bad // LINE)
    # One refill, three faulted fetches from the line; then index 0 misses
    # again: the failed refill cleared it (the line it held was overwritten).
    await phase("fault line", [bad, bad + 4, bad + 8, 4], 2)
    assert tb.faults == 3, f"{tb.faults} faulted fetches, expected 3"
    # Not installed: the same line refills (and faults) again.
    await phase("fault refetch", [bad, 8], 2)
    assert tb.faults == 4, f"{tb.faults} faulted fetches, expected 4"
    # One SLVERR beat (beat 3 of 8) fails the whole line.
    bad2 = 10 * SIZE + LINE                         # index 1
    tb.bad_beats.add(bad2 + 24)
    await phase("slverr beat", [bad2 + 40, LINE + 4], 2)
    assert tb.faults == 5, f"{tb.faults} faulted fetches, expected 5"
    # An invalidate raised while the PC sits in a faulted line is taken
    # (S_FAULT is not a refill); the line then refills and faults again.
    await phase("inv in fault", [bad, bad + 4], 2, inv_at=(1,), inv_when_busy=True)
    assert tb.inv_acks == 4, f"{tb.inv_acks} invalidate acks, expected 4"
    assert tb.faults == 7, f"{tb.faults} faulted fetches, expected 7"

    if level != "gate":
        n = 3000     if level == "func" else 20000
        rng = tb.rng
        stream, pc, inv_at = [], 0, []
        for i in range(n):
            pc = rng.randrange(0, 4 * SIZE, 4) if rng.random() < 0.08 else (pc + 4) % (4 * SIZE)
            stream.append(pc)
            if rng.random() < 0.003:
                inv_at.append(i)
        before = tb.ars
        await tb.fetch(stream, inv_at=inv_at, hold_pct=20)
        dut._log.info(f"random: {n} fetches (20% outside holds), {tb.ars - before} refills, "
                      f"{len(inv_at)} invalidates, seed {seed}")
    dut._log.info(f"checked {tb.checked} fetched words against memory")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_icache {lvl}") for lvl in reg_level_grid()])
def test_peregrine_icache(request, test_level, description):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_icache_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/fub/peregrine_icache.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_icache",
        module=module,
        testcase="cocotb_test_peregrine_icache",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_icache",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"SIZE_BYTES": str(SIZE), "LINE_BYTES": str(LINE),
                    "AXI_DW": "64", "AXI_IW": "4"},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
