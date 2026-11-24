# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_amber_latency
# Purpose: PRD P13 measurement: amber's CPU-side latency through its GAXI
#          port, as peregrine's D$ will see it.  Runs amber's own pair rig
#          (two ambers, the fabric, the bench AXI4 memory) and times cache 0
#          from the pins: request accept to response valid, and accept to
#          the next cycle the port can accept again, for read and write hits
#          and misses.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""amber hit latency for peregrine (PRD P13, TASK-001 stage 6).

Every request goes through the pair rig's own transaction path, so the rig's
golden model still scores the response data.  A separate pin monitor samples
cache 0's CPU port once per cycle (mid-cycle, the values the next rising
edge acts on):

* latency  = cycles from the accept cycle (req valid & ready) to the first
  cycle the response is valid; 1 means the response is valid in the cycle
  after the accept, which is what a single-cycle MEM stage needs;
* occupancy = cycles from the accept cycle to the next cycle req ready is
  high again: the shortest issue interval for back-to-back accesses.

The test asserts the measured hit numbers equal the ones PRD P13 records, so
a change to amber's hit path shows here before it shows in peregrine's CPI.
"""

import os
import sys

import cocotb
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.test_levels import level_env, reg_level_grid
import pytest

sys.path.insert(0, get_repo_root())
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_pair_rig_tb import (  # noqa: E402
    AmberPairRigTB,
)

AMBER_FL = "projects/components/cache-ip/amber-mesi-l1/rtl/filelists"
HARNESS = "projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_pair_rig_tb.sv"
GEOM = dict(sets=128, ways=4, line_bytes=64, bus_width=64)   # l1_pkg default

# PRD P13, as measured (latency, occupancy) in cycles, see the module
# docstring.  Before amber TASK-005 (2026-11-24): 4 / 3 for every hit (IDLE
# accept, LOOKUP, HIT_*, IDLE, then the staging FIFO).  After it (the 1-cycle
# hit): the accept cycle classifies the arriving request and reads the data
# array, the response is valid in HIT_RD / HIT_WR the next cycle and skips
# the FIFO, so latency 1; a read hit can be followed by an accept in that
# same cycle (occupancy 1), a write hit holds the port a second cycle while
# its merge lands (occupancy 2).  Misses and the S->M upgrade are reported,
# not asserted: they depend on the rig's fabric and bench memory, not on
# amber alone.
EXPECT = {
    "read_hit": (1, 1),
    "read_hit_m": (1, 1),
    "write_hit": (1, 2),
}


class PortTimer:
    """Pin-level timing of cache 0's CPU port (one record per request)."""

    def __init__(self, dut):
        self.dut = dut
        self.cycle = 0
        self.records = []          # dicts: accept, rsp, ready_again, states
        self._open = None

    async def run(self):
        d = self.dut
        state = d.u_amber0.ctrl_state
        while True:
            # Mid-cycle: the values the next rising edge will act on.
            await FallingEdge(d.clk)
            await ReadOnly()
            self.cycle += 1
            rec = self._open
            if rec is not None:
                rec["states"].append(int(state.value))
                if rec["rsp"] is None and int(d.cpu0_rsp_rd_valid.value):
                    rec["rsp"] = self.cycle
                if rec["ready_again"] is None and int(d.cpu0_req_wr_ready.value):
                    rec["ready_again"] = self.cycle
                if rec["rsp"] is not None and rec["ready_again"] is not None:
                    self.records.append(rec)
                    self._open = None
            if int(d.cpu0_req_wr_valid.value) and int(d.cpu0_req_wr_ready.value):
                assert self._open is None, "accept while a request is open"
                self._open = {"accept": self.cycle, "rsp": None,
                              "ready_again": None, "states": []}

    def last(self):
        r = self.records[-1]
        return r["rsp"] - r["accept"], r["ready_again"] - r["accept"], r["states"]


async def timed(tb, timer, c_label, addr, we):
    n = len(timer.records)
    await tb._txn(0, addr, we, label=c_label)
    for _ in range(50):
        if len(timer.records) > n:
            break
        await RisingEdge(tb.dut.clk)
    assert len(timer.records) == n + 1, f"{c_label}: no timing record"
    return timer.last()


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_peregrine_amber_latency(dut):
    tb = AmberPairRigTB(dut)
    await tb.setup_clocks_and_reset()
    await tb._s_init_walk()
    timer = PortTimer(dut)
    cocotb.start_soon(timer.run())

    results = {}

    def note(kind, lat, occ, states):
        results.setdefault(kind, []).append((lat, occ))
        tb.log.info(f"{kind:<16} latency {lat:>3}  occupancy {occ:>3}  "
                    f"ctrl_state {' '.join(f'{s:x}' for s in states[:12])}")

    # Lines in a set the init walk left alone; tags past the rig's directed range.
    base_tag = tb.WAYS + 2
    lines = [tb._compose_addr(base_tag + i, 5) for i in range(2)]

    # Read miss, then read hits on every beat of the line.  The rig's fabric
    # answers a read miss shared, so the line is installed S, not E.
    note("read_miss", *await timed(tb, timer, "rd_miss", lines[0], 0))
    for beat in range(tb.FILL_BEATS):
        note("read_hit", *await timed(tb, timer, f"rd_hit{beat}",
                                      lines[0] + beat * tb.STRB_W, 0))
    # The first write to the S line is a CLEAN_UNIQUE upgrade through the
    # fabric; then write hits on M (l1_control sends E and M writes down the
    # same HIT_WR path, so an E write hit costs what an M one does).
    note("write_upgrade_s", *await timed(tb, timer, "wr_upgrade_s", lines[0], 1))
    for beat in range(1, tb.FILL_BEATS):
        note("write_hit", *await timed(tb, timer, f"wr_hit{beat}",
                                       lines[0] + beat * tb.STRB_W, 1))
    # Read hit on M, and a write miss (write-allocate).
    note("read_hit_m", *await timed(tb, timer, "rd_hit_m", lines[0], 0))
    note("write_miss", *await timed(tb, timer, "wr_miss", lines[1], 1))

    summary = {k: sorted(set(v)) for k, v in results.items()}
    tb.log.info(f"P13 summary (latency, occupancy): {summary}")
    report = tb.get_test_report()
    assert report["mismatches"] == 0, f"rig data checks: {report}"
    for kind, want in EXPECT.items():
        if want is not None:
            assert summary[kind] == [want], f"{kind}: measured {summary[kind]}, PRD P13 says {want}"


@pytest.mark.parametrize("test_level", reg_level_grid()[:1])
def test_peregrine_amber_latency(request, test_level):
    """Pytest wrapper: amber's pair rig at the l1_pkg default geometry."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_amber_latency_{test_level}"
    verilog_sources, includes = [], []
    for fl in ("amber_top", "amber_pair_fabric"):
        srcs, incs = get_sources_from_filelist(repo_root=repo_root,
                                               filelist_path=f"{AMBER_FL}/{fl}.f")
        verilog_sources += [s for s in srcs if s not in verilog_sources]
        includes += [i for i in incs if i not in includes]
    verilog_sources.append(os.path.join(repo_root, HARNESS))
    sets, lb, bw = GEOM["sets"], GEOM["line_bytes"], GEOM["bus_width"]
    span = min(max(sets * 16, 32 << (sets - 1).bit_length(), 64), 4096)
    mem_depth = span * (lb // (bw // 8))
    os.makedirs(log_dir, exist_ok=True)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="amber_pair_rig_tb",
        module=module,
        testcase="cocotb_test_peregrine_amber_latency",
        parameters={"SETS": str(sets), "WAYS": str(GEOM["ways"]),
                    "LINE_BYTES": str(lb), "BUS_WIDTH": str(bw),
                    "USE_MONITOR": "1", "MEM_DEPTH": str(mem_depth)},
        sim_build=sim_build_path(tests_dir, name),
        extra_env=level_env(test_level, SETS=sets, WAYS=GEOM["ways"],
                            LINE_BYTES=lb, BUS_WIDTH=bw, USE_MONITOR="1",
                            MEM_DEPTH=mem_depth, DUT="amber_pair_rig",
                            LOG_PATH=os.path.join(log_dir, f"{name}.log"),
                            COCOTB_LOG_LEVEL="INFO"),
        keep_files=True,
    )
