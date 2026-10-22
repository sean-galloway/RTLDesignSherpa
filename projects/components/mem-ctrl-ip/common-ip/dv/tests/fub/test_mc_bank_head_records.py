# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""
FUB test: mc_bank_head_records (common-ip) -- the storage -> scheduler
per-bank head-record contract (mem-ctrl recovery Phase 1, 2026-10-21).

The DUT turns a backend's per-entry vectors {valid, pend, bank, row, col,
older matrix, age_exceed} into one REGISTERED record pair per bank: head =
the oldest schedulable entry of that bank, head2 = the one behind it, each
with behind_empty (no younger schedulable entry of this bank behind it),
behind_same_row (a younger same-bank same-row entry -- schedulable OR still
pending -- exists behind it) and the aging flag.

Method: a Python reference holds a slot table with insertion order; every
cycle it drives the DUT's vectors (the age matrix is derived from insertion
order exactly as the CAMs build theirs: older[j][i] = j inserted before i)
and, one cycle later, checks every bank's two records field by field.
The stimulus is a random walk of inserts into free slots (schedulable, or
pending with a later "fill" flip), pops of random valid slots (commit /
issue), fills, and aging-flag flips, with the bank mix skewed so that banks
hold 0, 1, 2 and more candidates often, and rows drawn from a small set so
same-row runs are common. Slot
recycling is exercised by construction (a freed low slot takes a young
entry), which is the case the entry store's fill target once got wrong.

Production change that fails this test: picking by slot index instead of
age, miscounting behind_empty, ignoring pending entries in behind_same_row,
dropping head2, or removing the output register (the check is against the
PREVIOUS cycle's vectors).

Levels: TEST_LEVEL gate = 300 cycles, func = 2000, full = 8000.
"""
import os
import random

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Timer

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_bank_head_records_fub.f")

NUM_ENTRIES = 8
NUM_BANKS = 8
ROW_WIDTH = 14
COL_WIDTH = 10
BKW = 3
HEAD_ROW_W, HEAD_COL_W, HEAD_SLOT_W = 18, 14, 8   # mc_common_pkg MC_HEAD_*


class _Model:
    """Slot table + insertion order; builds the DUT vectors and the expected
    records the same way the CAMs and the RTL define them."""

    def __init__(self, rng):
        self.rng = rng
        self.slots = [None] * NUM_ENTRIES       # slot -> dict or None
        self.order = 0

    def free_slots(self):
        return [i for i, e in enumerate(self.slots) if e is None]

    def valid_slots(self):
        return [i for i, e in enumerate(self.slots) if e is not None]

    def insert(self, bank, row, col, pend=False):
        free = self.free_slots()
        if not free:
            return False
        slot = self.rng.choice(free)            # any free slot, not the lowest
        self.slots[slot] = {"bank": bank, "row": row, "col": col,
                            "order": self.order, "age": 0, "pend": pend}
        self.order += 1
        return True

    def pending_slots(self):
        return [i for i, e in enumerate(self.slots) if e is not None and e["pend"]]

    def fill(self, slot):
        self.slots[slot]["pend"] = False

    def pop(self, slot):
        self.slots[slot] = None

    def vectors(self):
        valid = pend = bank = row = col = older = agex = 0
        for i, e in enumerate(self.slots):
            if e is None:
                continue
            if e["pend"]:
                pend |= 1 << i
            else:
                valid |= 1 << i
            bank |= e["bank"] << (i * BKW)
            row |= e["row"] << (i * ROW_WIDTH)
            col |= e["col"] << (i * COL_WIDTH)
            agex |= e["age"] << i
            for j, f in enumerate(self.slots):
                # older[i][j] (bit i*N+j) = i inserted strictly before j
                if f is not None and i != j and e["order"] < f["order"]:
                    older |= 1 << (i * NUM_ENTRIES + j)
        return dict(valid=valid, pend=pend, bank=bank, row=row, col=col,
                    older=older, agex=agex)

    def behind_same_row(self, i):
        e = self.slots[i]
        return int(any(f is not None and j != i and f["order"] > e["order"]
                       and f["bank"] == e["bank"] and f["row"] == e["row"]
                       for j, f in enumerate(self.slots)))

    def expected(self):
        out = {}
        for b in range(NUM_BANKS):
            cands = sorted((i for i, e in enumerate(self.slots)
                            if e is not None and e["bank"] == b and not e["pend"]),
                           key=lambda i: self.slots[i]["order"])
            n = len(cands)
            recs = []
            for k in range(2):
                if k < n:
                    i = cands[k]; e = self.slots[i]
                    recs.append(dict(vld=1, row=e["row"], col=e["col"], slot=i,
                                     behind_empty=int(n == k + 1),
                                     bsr=self.behind_same_row(i), age=e["age"]))
                else:
                    recs.append(dict(vld=0, row=0, col=0, slot=0, behind_empty=0,
                                     bsr=0, age=0))
            out[b] = recs
        return out


def _field(vec, idx, width):
    return (int(vec) >> (idx * width)) & ((1 << width) - 1)


def _read_records(dut):
    got = {}
    for b in range(NUM_BANKS):
        recs = []
        for pfx in ("head", "head2"):
            vld = _field(getattr(dut, f"{pfx}_vld").value, b, 1)
            recs.append(dict(
                vld=vld,
                row=_field(getattr(dut, f"{pfx}_row").value, b, HEAD_ROW_W) if vld else 0,
                col=_field(getattr(dut, f"{pfx}_col").value, b, HEAD_COL_W) if vld else 0,
                slot=_field(getattr(dut, f"{pfx}_slot").value, b, HEAD_SLOT_W) if vld else 0,
                behind_empty=_field(getattr(dut, f"{pfx}_behind_empty").value, b, 1) if vld else 0,
                bsr=_field(getattr(dut, f"{pfx}_behind_same_row").value, b, 1) if vld else 0,
                age=_field(getattr(dut, f"{pfx}_age_exceed").value, b, 1) if vld else 0,
            ))
        got[b] = recs
    return got


def _drive(dut, v):
    dut.sch_valid.value = v["valid"]
    dut.sch_pend.value = v["pend"]
    dut.sch_bank.value = v["bank"]
    dut.sch_row.value = v["row"]
    dut.sch_col.value = v["col"]
    dut.sch_older.value = v["older"]
    dut.sch_age_exceed.value = v["agex"]


async def _reset(dut):
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.rst_n.value = 0
    _drive(dut, dict(valid=0, pend=0, bank=0, row=0, col=0, older=0, agex=0))
    for _ in range(5):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bank_head_records(dut):
    level = os.environ.get("TEST_LEVEL", "gate").lower()
    cycles = {"gate": 300, "func": 2000, "full": 8000}.get(level, 300)
    rng = random.Random(int(os.environ.get("SEED", "7")))
    m = _Model(rng)
    await _reset(dut)

    # After reset with no entries every record is empty.
    await ReadOnly()
    got = _read_records(dut)
    for b in range(NUM_BANKS):
        assert got[b][0]["vld"] == 0 and got[b][1]["vld"] == 0, f"bank {b} not empty after reset"
    await RisingEdge(dut.clk)
    await Timer(1, "ns")          # leave the read-only phase before driving

    # Hot-bank mix: 60% of inserts go to two banks so 2+ candidates per
    # bank are common, the rest spread so 0/1 are common too.
    hot = rng.sample(range(NUM_BANKS), 2)
    # Rows from a 3-entry set per bank so same-row runs (behind_same_row=1)
    # and row switches (=0) both happen; ~30% of inserts land pending.
    rows = [rng.randrange(1 << ROW_WIDTH) for _ in range(3)]
    checked = 0
    prev_expected = None
    for cyc in range(cycles):
        # ---- stimulus for this cycle ----
        r = rng.random()
        if r < 0.40:
            bank = rng.choice(hot) if rng.random() < 0.6 else rng.randrange(NUM_BANKS)
            m.insert(bank, rng.choice(rows), rng.randrange(1 << COL_WIDTH),
                     pend=(rng.random() < 0.3))
        elif r < 0.52:
            ps = m.pending_slots()
            if ps:
                m.fill(rng.choice(ps))
        elif r < 0.82:
            vs = m.valid_slots()
            if vs:
                m.pop(rng.choice(vs))
        elif r < 0.90:
            vs = m.valid_slots()
            if vs:
                e = m.slots[rng.choice(vs)]
                e["age"] ^= 1
        # else: hold (records must not change)
        v = m.vectors()
        exp_now = m.expected()
        _drive(dut, v)
        await RisingEdge(dut.clk)
        await ReadOnly()
        # The registered records now reflect the vectors driven BEFORE this
        # edge, i.e. exp_now (one-cycle latency by contract).
        got = _read_records(dut)
        for b in range(NUM_BANKS):
            for k, name in enumerate(("head", "head2")):
                assert got[b][k] == exp_now[b][k], (
                    f"cycle {cyc} bank {b} {name}: got {got[b][k]} expected {exp_now[b][k]}; "
                    f"slots={[(i, e['bank'], e['row'], e['order'], e['pend']) for i, e in enumerate(m.slots) if e]}")
        checked += 1
        prev_expected = exp_now
        await RisingEdge(dut.clk)
        await ReadOnly()
        # With the vectors held, the records must be stable (no comb leakage).
        got2 = _read_records(dut)
        assert got2 == got, f"cycle {cyc}: records changed while the vectors were held"
        await Timer(1, "ns")      # leave the read-only phase before the next drive
    dut._log.info("bank head records: %d cycles checked at level %s", checked, level)


def test_mc_bank_head_records(request):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_bank_head_records_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_ENTRIES": str(NUM_ENTRIES), "NUM_BANKS": str(NUM_BANKS),
              "ROW_WIDTH": str(ROW_WIDTH), "COL_WIDTH": str(COL_WIDTH)}
    extra_env = {"DUT": dut_name,
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
                 "TEST_LEVEL": os.environ.get("TEST_LEVEL", "gate"),
                 "SEED": os.environ.get("SEED", "7")}
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_bank_head_records",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", FIELD_COMBO_VLT,
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
