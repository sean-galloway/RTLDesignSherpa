#!/usr/bin/env python3
"""Replay the DDR2 characterization scenarios through Ramulator 2 (MC-012).

The board host program (projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/
build-perf/host/pumice_char.py and perf_mixed_family.py) drives granite and
LiteDRAM with named address-walk families. This tool builds the SAME request
streams -- one 8-byte BL4 transaction per MC cycle, the AXI beat rate of the
board's 64-bit port -- as timed traces, runs each through Ramulator's
GenericDDR controller on the DDR2 device class, and writes a CSV whose
bandwidth columns are defined exactly as the board's (bytes moved over the
cycles from the first beat in to the last response out, times the MC clock).
The companion `compare` subcommand puts those cells beside the measured
granite and LiteDRAM columns of an existing char_results CSV set.

Geometry is the Nexys A7 part as the board host sees it (Geometry in
pumice_char.py): x16 MT47H64M16, 10 column bits, 8 banks, 13 row bits, 2 KB
page, ROW_MAJOR address map (row | bank | column | byte), the same order
Ramulator's RoBaRaCoCh mapper gives at one rank and one channel.

Families reproduced (strides from pumice_char.strides_for and
perf_mixed_family.family_programs / programs):
  incremental, row_major, col_major, col_major_interleaved   (one injector)
  row_thrash, random                                         (4 injectors)
  mixed (4 writers + 4 readers concurrent, rows 8 apart)      (4 + 4)
Not reproduced: the half-burst families (half_pair / half_oct), which issue
AXI transactions narrower than a DRAM burst and exist to exercise the read
combiner; Ramulator requests are whole transactions.

The `random` family's LFSR is a stand-in for the injector's (same shape: a
16-bit maximal LFSR indexing bursts inside a two-row-by-all-banks region);
the per-burst order differs from the board, the hit/miss statistics do not.

Run from the repo root with env_python sourced; the vendor build must be in
place (references/ramulator2/fetch.sh):

  python3 projects/components/mem-ctrl-ip/references/ramulator2/bin/char_model.py run \\
      --config open32 --out <dir>/model_ramulator2_ddr2_open32_<date>.csv
  python3 .../char_model.py compare --model <that csv> \\
      --measured projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/char_results \\
      --granite sku100_2026-11-09 --litedram hx100_2026-10-31 --out <md>

MC-013 added the controller-side axes the configs below sweep (write-drain
watermarks, refresh scatter, the per-bank FIFO + round-robin scheduler
`BankFIFO-RR` from the overlay) and `run-trace`, which replays a request stream
CAPTURED from a cocotb sim (perf_axi_trace.py in the ddr2_char_framework
tests writes it off the controller's AXI port) instead of one rebuilt here:

  python3 .../char_model.py run-trace --config open32 --name col_ilv_bl8 \\
      --wr <dir>/col_ilv_wr.trace --rd <dir>/col_ilv_rd.trace --out <csv>

MC-018 added the SKU itself: `granite_sku100` runs the overlay's GraniteSKU
controller (granite_sku_controller.cpp: the bank-FIFO store, the pick core's
select, the direction register, the row lane, close-on-drain, one slot per MC
cycle) on the DDR2_GRANITE_SKU100_PX preset (the host's phase-exact MC-cycle
timings in CK, the host default since 2026-11-22; DDR2_GRANITE_SKU100 is the
one-CK-margin set the host derived before, `sku_margin`);
`_bi` / `_close` are the board's bank_interleave (bank_lsb 2 AND close page, as
the host preset programs it) / close_page presets on it, and the `sku_*` configs
each change ONE term. `board-compare` puts the SKU model
beside a board CSV set cell by cell with a per-family tolerance; `sweep` runs a
list of configs over a suite and writes the pattern x variant table. The MC-018
patterns (`patterns` suite): read / write mixes, mixed at 2 / 8 threads and
AxLEN 4 / 16, row-locality sweeps, two- and four-bank interleaves.

MC-021 gave the GraniteSKU controller mc_bank_pick's pipeline (the request
register, the winner register with hold / speculation / fresh pick, the
self-stale mask, the next-op hint, the lane as a second winner register, the
registered rank ok): `pick_la`, `rank_ok_lag`, and the two RTL questions as
knobs (`ap_act_la`, `ap_stale`). `sku_la0/la1/la3`, `sku_rankok1`, `sku_apactla`,
`sku_apstale` are the one-term variants (model_mc021_pick_pipeline_2026-11-17.md).
The admission is three terms since MC-021 step 7: a pop frees its pool slot to
the host `pool_gate_lag` (2) slots later and its bank-cap room `cap_gate_lag`
(1) slot later, and an accepted beat lands `admit_lag` (1) slot after; the pool
path is the 3 ISSUE-004 measured, the cap path 2, and that one slot is where the
close-page mixed turns fall (`sku_admit3` = one three-slot stage on both paths,
the model before). `close_lag` (2, step 8) is the record's hit flag on the way
down: a head whose row a PRE closed requests its ACT two slots after the PRE
(`sku_closelag0` = before); with it, and the GO swept against the model's
refresh phase (`GRANITE_GO_OFFSET=<ticks>`, the trace frontend's `start_tick`),
the open-page mixed cell shows the board's two modes; `board-compare` reads
such a cell by mode (`--board-also` for the board's reruns, one `--model` CSV
per model phase, each with its `GO offset` in the notes).
The page policy is the RTL's since ISSUE-006 (2026-11-20): `page_mode` 4 is the
hybrid the board's `defaults` preset runs (the drain auto-precharge on a known
conflict, on a drained queue only where the bank's history arms it, else the
idle timeout `tr_init` 2 closes the row as the pick's lowest-priority PRE);
`granite_sku100_open` is mode 0, the flat close-on-drain the board's open_page
preset writes -- and the only policy the model had before, which issued no
demand PRE where the RTL's `defaults` issues ~700 per col_ilv run (MC-019).
`hit_lag` (2) is the record's hit flag: a bank's heads read as row hits two
slots after its ACT, so the column request shows at ACT + 3 where the hinted
column fires at ACT + 2 (MC-021 step 4; `sku_hitlag1` reads the hit live);
`ap_fire_stale` (True) is the step-4 RTL change, the fired auto-precharging
column's pair masked the slot after its fire (`sku_noapfirestale` = the RTL
before it). `wr_fill_lag` (2) is the store's write record: it needs the entry's
data fill and the fill-done register where the read record needs only the
queue, so a write beat entering an empty bank queue is the pick's request two
slots later than a read beat; it sets a new bank's phase against the banks
already cycling under close page, where the ACT collisions under tRRD that
discard the next-op hint come from (MC-021 step 6; `sku_wrfill0` = before).
The auto-precharge self-close is the bank timer's since MC-020 decision 2
(2026-11-22): `ap_seq` (True) fires it the MC cycle both its counters reach
zero -- tRAS from the ACT, tRTP / tWR from the column -- and reloads a tRP of
its own, `t_rp_ap_rd` / `t_rp_ap_wr` (the TIMINGS_RP_AP fields the host
derives: 1 / 2 at the SKU's point, where the shared tRP was 2 / 2 and made the
one-bank chain ACT -> RDA -> ACT 7 MC against the CK-exact 6). `sku_rpshared`
is the RTL before the fields, `sku_noapseq` the model before the term (the
CK-exact DRAM terms alone, 51 / 6 against the board on 2026-11-22).
`GRANITE_SKU_PARAMS="k=v,..."` overrides any GraniteSKU knob on any config
for a run, as `GRANITE_TIMING_PRESET` does the preset.
"""
from __future__ import annotations

import argparse
import csv
import os
import sys
import tempfile
import time
from dataclasses import dataclass, replace
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

def _repo_root() -> str:
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(10):
        if os.path.isdir(os.path.join(d, ".git")) or os.path.isdir(os.path.join(d, "vendor", "ramulator2")):
            return d
        d = os.path.dirname(d)
    raise RuntimeError("repo root not found above " + __file__)


REPO_ROOT = _repo_root()
VENDOR_PY = os.path.join(REPO_ROOT, "vendor", "ramulator2", "python")
if VENDOR_PY not in sys.path:
    sys.path.insert(0, VENDOR_PY)

# ---------------------------------------------------------------------------
# Geometry (pumice_char.Geometry defaults) and the board's injection shape
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Geometry:
    col_width: int = 10
    bank_width: int = 3
    row_width: int = 13
    byte_offset: int = 1      # x16 -> 2 bytes per column
    beat_bytes: int = 8       # 64-bit AXI data bus

    @property
    def device_bytes(self) -> int:
        return (1 << (self.col_width + self.bank_width + self.row_width)) << self.byte_offset

    @property
    def page_bytes(self) -> int:
        return (1 << self.col_width) << self.byte_offset

    @property
    def bank_stride(self) -> int:
        return self.page_bytes

    @property
    def row_stride_same_bank(self) -> int:
        return self.page_bytes << self.bank_width


GEOM = Geometry()
TX_BYTES = 8                 # one DDR2 BL4 burst on x16 = one AXI beat
MC_CLK_MHZ = 100.0           # the sku100 board point: MC 100 MHz, CK 200 MHz
ROW_THRASH_ROW = 0x11        # perf_mixed_family.ROW_THRASH_ROW
RANDOM_ROWS = 2              # perf_mixed_family.RANDOM_ROWS
REGION_ROWS = 8              # perf_mixed_family.REGION_ROWS
WINDOW_GENS = 4              # injectors per direction in the board's window runs


@dataclass(frozen=True)
class Scenario:
    name: str
    family: str
    burst_len: int = 8       # AXI beats of 8 bytes
    txn_count: int = 65535   # AXI bursts per injector (the board's "every" count)
    threads: int = 1
    # family knobs (MC-018 patterns): write fraction of a one-stream mix (rw_mix), the row-hit
    # probability of a locality walk (locality), the bank step of an interleave (bank_step)
    param: float = 0.0
    # two independent in-order streams (writers and readers from one GO, as the AXI port's two
    # channels carry them) rather than one stream: the mixed family
    split: bool = False

    @property
    def burst_bytes(self) -> int:
        return self.burst_len * GEOM.beat_bytes


EVERY = [
    Scenario(f"{fam}_bl{bl}", fam, burst_len=bl)
    for fam in ("incremental", "row_major", "col_major", "col_major_interleaved")
    for bl in (4, 8, 16)
]
WINDOWS = [
    Scenario("mixed_bl8", "mixed", burst_len=8, txn_count=32000, threads=WINDOW_GENS, split=True),
    Scenario("row_thrash_bl8", "row_thrash", burst_len=8, txn_count=32000, threads=WINDOW_GENS),
    Scenario("random_bl8", "random", burst_len=8, txn_count=32000, threads=WINDOW_GENS),
]
# MC-018 item 3: the patterns the char profiles do not cover. txn_count is per injector; the
# mixes and the locality walks run four injectors so the bank parallelism is the window's.
PATTERNS = [
    # the mixed window at 2 and 8 threads (1 + 1 / 4 + 4 injectors) and at AxLEN 4 / 16
    Scenario("mixed_bl8_t2", "mixed", burst_len=8, txn_count=32000, threads=2, split=True),
    Scenario("mixed_bl8_t8", "mixed", burst_len=8, txn_count=32000, threads=8, split=True),
    Scenario("mixed_bl4", "mixed", burst_len=4, txn_count=32000, threads=WINDOW_GENS, split=True),
    Scenario("mixed_bl16", "mixed", burst_len=16, txn_count=32000, threads=WINDOW_GENS, split=True),
    # one in-order stream per injector, each burst a write with probability `param` (70 / 30, 30 / 70),
    # row-hit walks in the injector's own bank: the direction register's turnarounds alone
    Scenario("rw70_bl8", "rw_mix", burst_len=8, txn_count=32000, threads=WINDOW_GENS, param=0.7),
    Scenario("rw30_bl8", "rw_mix", burst_len=8, txn_count=32000, threads=WINDOW_GENS, param=0.3),
    # row locality: each burst stays in the open row with probability `param`, else moves to another
    # of the injector's 8 rows (4 injectors, one bank each)
    *[Scenario(f"locality_h{int(h * 100):02d}_bl8", "locality", burst_len=8, txn_count=32000,
               threads=WINDOW_GENS, param=h) for h in (0.1, 0.3, 0.5, 0.7, 0.9)],
    # interleaves that defeat the rotor: every burst a miss, stepping 2 / 4 banks (4 / 2 banks in play)
    Scenario("col_ilv_s2_bl8", "bank_step", burst_len=8, txn_count=65535, param=2),
    Scenario("col_ilv_s4_bl8", "bank_step", burst_len=8, txn_count=65535, param=4),
]
# memory-controllers MC-024 (the read-priority direction register): one direction outlasting the other, so the
# shorter direction's MB/s is its share while the longer one keeps the bus contended. Not a board suite.
SUSTAINED = [
    Scenario("mixed_rd4_bl8", "mixed", burst_len=8, txn_count=8000, threads=WINDOW_GENS, split=True, param=4),
    # reads 16x: long enough that the writes' share while the reads hold the bus is a steady state
    Scenario("mixed_rd16_bl8", "mixed", burst_len=8, txn_count=8000, threads=WINDOW_GENS, split=True, param=16),
    Scenario("mixed_wr4_bl8", "mixed", burst_len=8, txn_count=8000, threads=WINDOW_GENS, split=True, param=-4),
]
SUITES = {"every": EVERY, "windows": WINDOWS, "sustained": SUSTAINED, "all": EVERY + WINDOWS, "patterns": PATTERNS,
          "everything": EVERY + WINDOWS + PATTERNS}


# ---------------------------------------------------------------------------
# Address walks -- one list of AXI burst base addresses per injector
# ---------------------------------------------------------------------------


def _walk(start: int, stride: int, wrap_mask: int, count: int) -> Iterator[int]:
    """addr[i] = start + (i*stride & wrap) -- the injector's one-dimensional walk."""
    for i in range(count):
        off = i * stride
        yield start + (off & wrap_mask if wrap_mask else off)


def _lfsr16(seed: int) -> Iterator[int]:
    """Maximal 16-bit Fibonacci LFSR (taps 16, 14, 13, 11); a stand-in for the injector's."""
    s = seed & 0xFFFF or 0xACE1
    while True:
        bit = ((s >> 0) ^ (s >> 2) ^ (s >> 3) ^ (s >> 5)) & 1
        s = (s >> 1) | (bit << 15)
        yield s


def injector_walks(sc: Scenario) -> Tuple[List[List[int]], List[List[int]]]:
    """(write walks, read walks): per injector the AXI burst base addresses, in
    issue order. For all but `mixed` the read walk is the write walk."""
    bb, n = sc.burst_bytes, sc.txn_count
    if sc.family == "incremental":
        w = [list(_walk(0, bb, 0, n))]
    elif sc.family == "row_major":
        w = [list(_walk(0, bb, GEOM.page_bytes - 1, n))]
    elif sc.family == "col_major":
        w = [list(_walk(0, GEOM.row_stride_same_bank, GEOM.device_bytes - 1, n))]
    elif sc.family == "col_major_interleaved":
        w = [list(_walk(0, GEOM.bank_stride, GEOM.device_bytes - 1, n))]
    elif sc.family == "row_thrash":
        # idx bit 0 picks the row (stride one row, two rows), the rest walks bursts in the page
        w = []
        for g in range(sc.threads):
            bank = g % (1 << GEOM.bank_width)
            base = bank * GEOM.bank_stride + ROW_THRASH_ROW * GEOM.row_stride_same_bank
            w.append([base + (i & 1) * GEOM.row_stride_same_bank + (((i >> 1) * bb) & (GEOM.page_bytes - 1))
                      for i in range(n)])
    elif sc.family == "random":
        region = RANDOM_ROWS * GEOM.row_stride_same_bank
        w = []
        for g in range(sc.threads):
            lf = _lfsr16(0xABCD1234 ^ (g * 0x9E37))
            w.append([g * region + ((next(lf) * bb) & (region - 1)) for _ in range(n)])
    elif sc.family == "mixed":
        pairs = max(1, sc.threads // 2)
        layout = [(g % pairs, g // pairs) for g in range(sc.threads)]
        # param (the sustained suite): > 0 lengthens the READ streams by that factor, < 0 the WRITE streams by
        # its magnitude, so one direction runs on after the other's last burst and a share under sustained
        # load shows in the shorter direction's window; 0 = equal streams (the board's cell)
        def region(r: int, k: int) -> List[List[int]]:
            out = []
            for bank, rowgrp in layout:
                row = rowgrp + r * REGION_ROWS
                start = bank * GEOM.bank_stride + row * GEOM.row_stride_same_bank
                out.append(list(_walk(start, bb, GEOM.page_bytes - 1, n * k)))
            return out
        kr = int(sc.param) if sc.param > 0 else 1
        kw = int(-sc.param) if sc.param < 0 else 1
        return region(0, kw), region(1, kr)
    elif sc.family == "rw_mix":
        # one stream per injector in its own bank, a row-hit walk; which bursts are writes is
        # decided below (interleave_mixed_bursts) from the same LFSR, so the walk is shared
        w = []
        for g in range(sc.threads):
            bank = g % (1 << GEOM.bank_width)
            start = bank * GEOM.bank_stride + ROW_THRASH_ROW * GEOM.row_stride_same_bank
            w.append(list(_walk(start, bb, GEOM.page_bytes - 1, n)))
    elif sc.family == "locality":
        # per injector one bank, REGION_ROWS rows; a burst stays in the current row with probability
        # param (sequential inside the page, wrapping) or jumps to another of the rows
        w = []
        per_row = GEOM.page_bytes // bb
        for g in range(sc.threads):
            bank = g % (1 << GEOM.bank_width)
            lf = _lfsr16(0x5EED ^ (g * 0x9E37))
            row, col = 0, 0
            walk = []
            for _ in range(n):
                r = next(lf)
                if (r & 0xFFFF) >= int(sc.param * 65536):
                    row = (row + 1 + ((r >> 4) % (REGION_ROWS - 1))) % REGION_ROWS
                    col = (r >> 8) % per_row
                walk.append(bank * GEOM.bank_stride + (ROW_THRASH_ROW + row) * GEOM.row_stride_same_bank + col * bb)
                col = (col + 1) % per_row
            w.append(walk)
    elif sc.family == "bank_step":
        # col_major_interleaved stepping `param` banks: with 8 banks only 8 / param of them are in play
        step = int(sc.param)
        w = [list(_walk(0, step * GEOM.bank_stride, GEOM.device_bytes - 1, n))]
    else:
        raise ValueError(f"unknown family {sc.family!r}")
    return w, w


def interleave_bursts(walks: Sequence[Sequence[int]], burst_len: int, op: str) -> Iterator[Tuple[str, int]]:
    """Round-robin the injectors one AXI burst at a time, each burst expanded to
    its 8-byte beats: the stream the board's single AXI port carries."""
    idx = [0] * len(walks)
    live = True
    while live:
        live = False
        for g, walk in enumerate(walks):
            if idx[g] < len(walk):
                live = True
                base = walk[idx[g]]
                idx[g] += 1
                for beat in range(burst_len):
                    yield op, base + beat * GEOM.beat_bytes


def interleave_mixed_bursts(walks: Sequence[Sequence[int]], burst_len: int, write_frac: float,
                            seed: int = 0x3A5C) -> Iterator[Tuple[str, int]]:
    """interleave_bursts with each burst a write with probability write_frac (one LFSR for the
    whole stream): the rw_mix family, one in-order stream carrying both directions."""
    lf = _lfsr16(seed)
    thresh = int(write_frac * 65536)
    idx = [0] * len(walks)
    live = True
    while live:
        live = False
        for g, walk in enumerate(walks):
            if idx[g] < len(walk):
                live = True
                base = walk[idx[g]]
                idx[g] += 1
                op = "ST" if next(lf) < thresh else "LD"
                for beat in range(burst_len):
                    yield op, base + beat * GEOM.beat_bytes


# ---------------------------------------------------------------------------
# Address maps (the board's ADDR_MAP.bank_lsb presets)
# ---------------------------------------------------------------------------
# The model's mapper is RoBaRaCoCh = the RTL's ROW_MAJOR (bank_lsb = COL_WIDTH).
# The board's `bank_interleave` preset is bank_lsb = log2(burst_cols) = 2 on the
# x16 BL4 build: in device-word units [col_lo(2) | bank(3) | col_hi(8) | row(13)],
# one BL4 burst per bank before the bank field steps. A trace address under that
# map is re-encoded here to the ROW_MAJOR address of the same DRAM location, so
# the model's mapper stays one and the board's preset is a property of the stream.
BI_BANK_LSB = 2


def remap_bank_interleave(addr: int, bank_lsb: int = BI_BANK_LSB) -> int:
    word = addr >> GEOM.byte_offset
    col_lo = word & ((1 << bank_lsb) - 1)
    bank = (word >> bank_lsb) & ((1 << GEOM.bank_width) - 1)
    col_hi = (word >> (bank_lsb + GEOM.bank_width)) & ((1 << (GEOM.col_width - bank_lsb)) - 1)
    row = word >> (GEOM.col_width + GEOM.bank_width)
    col = (col_hi << bank_lsb) | col_lo
    out = (((row << GEOM.bank_width) | bank) << GEOM.col_width) | col
    return (out << GEOM.byte_offset) | (addr & ((1 << GEOM.byte_offset) - 1))


ADDR_MAPS = {"row_major": lambda a: a, "bank_interleave": remap_bank_interleave}


def write_trace(path: str, streams: Iterable[Iterator[Tuple[str, int]]], *, addr_map: str = "row_major",
                split: bool = False) -> int:
    """One request per tick; several streams (write + read for `mixed`) are
    interleaved beat by beat. Returns the request count. `split` stamps the
    streams with the SAME ticks (one beat per tick per stream: the frontend's
    split_directions mode offers each direction independently); `addr_map`
    re-encodes every address from that board preset's map (ADDR_MAPS)."""
    n = 0
    remap = ADDR_MAPS[addr_map]
    with open(path, "w") as f:
        its = [iter(s) for s in streams]
        tick = 0
        while its:
            nxt = []
            for it in its:
                try:
                    op, addr = next(it)
                except StopIteration:
                    continue
                f.write(f"{tick} {op} {remap(addr)}\n")
                if not split:
                    tick += 1
                n += 1
                nxt.append(it)
            if split:
                tick += 1
            its = nxt
    return n


# ---------------------------------------------------------------------------
# Model configurations (the controller-side axis)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ModelConfig:
    name: str
    timing_preset: str = "DDR2_MT47H64M16_400_CL3"
    org_preset: str = "DDR2_1Gb_x16"
    row_policy: str = "open"           # open | closed_cap
    cap: int = 1
    read_buffer: int = 32
    write_buffer: int = 32
    refresh: bool = True
    scheduler: str = "FRFCFS"          # FRFCFS | FRFCFS-RowHit | BankFIFO-RR (overlay: per-bank FIFOs, rotor across banks)
    column_first: bool = False         # BankFIFO-RR: a ready column command beats a ready row command
    peek_depth: int = 1                # BankFIFO-RR: a bank offers a younger row hit from its first peek_depth entries when its
                                       #   head is a row conflict (1 = the strict FIFO; MC-016's two-head store is 2)
    mc_granular: bool = False          # round every constraint up to 2 CK (the RTL's MC-cycle counters)
    wr_low_wm: float = 0.2             # GenericDDR write-drain hysteresis, fractions of the write queue:
    wr_high_wm: float = 0.8            #   drain writes above high (or when no read waits), back to reads below low
    scatter_interval: int = 0          # AllBank refresh: stagger the scope nodes by this many cycles (0 = all at once)
    ref_burst: int = 1                 # n > 1: n REFs issued back to back every n tREFI (nRFC and nREFI both x n), the
                                       #   JEDEC postpone / pull-in credit (DDR2: up to 8) spent as one burst
    # ---- MC-018: the SKU controller (overlay granite_sku_controller.cpp) ----
    controller: str = "GenericDDR"     # GenericDDR | GraniteSKU
    slot_ticks: int = 2                # GraniteSKU: CK per main command slot (2 = one per MC cycle at DFI 1:2)
    bank_cap_mixed: int = 6            # GraniteSKU: BANK_CAP_MIXED (0 = off)
    cap_per_beat: bool = True          # GraniteSKU: the cap checked on every beat at the store's push (w_rd_cap_ok / w_wr_cap_ok)
    admit_lag: int = 1                 # GraniteSKU: MC cycles from a beat's ACCEPTANCE to its landing in its bank queue (the hold -> FIFO push)
    pool_gate_lag: int = 2             # GraniteSKU: slots after a pop before the freed pool slot is offered to the host (pool path: 2 + 1 = the 3
                                       #   ISSUE-004 measured)
    cap_gate_lag: int = 1              # GraniteSKU: slots after a pop before the bank queue count the BANK_CAP_MIXED check reads shows it (cap
                                       #   path: 1 + 1; MC-021 step 7 -- the one slot that decides which way the mixed close-page turns fall)
    req_bank_timing: bool = True       # GraniteSKU: a request needs the bank's timers only; the rank-level terms hold the fire (ISSUE-004)
    pick_la: int = 2                   # GraniteSKU: the pick pipeline's lookahead / hint reach in slots (LA; 0 = every hop pays the pipe) (MC-021)
    rank_ok_lag: int = 0               # GraniteSKU: the ACT's rank ok seen this many slots late (1 = the N+1 global timers before BUG-004)
    ap_act_la: bool = False            # GraniteSKU: the lookahead reaches the ACT after an auto-precharge (the RTL question; measured: no)
    ap_stale: bool = False             # GraniteSKU: an auto-precharging column's pair is self-stale after its pick (the RTL question)
    hit_lag: int = 2                   # GraniteSKU: slots after a bank's ACT before the decode sees its heads as row hits (the bank
                                       #   timers' registered row image -> the record's hit flag -> the request register; MC-021 step 4)
    ap_fire_stale: bool = True         # GraniteSKU: the pair of a column that fired with auto-precharge is masked the slot after its fire
                                       #   (the RTL since MC-021 step 4; False = the RTL before, whose leftover column request won the select)
    ap_seq: bool = True                # GraniteSKU: the auto-precharge self-close sequenced as the bank timer does -- fire = max(ACT + tRAS,
    rfc_block: bool = True             # GraniteSKU: the pick core's tRFC demand block -- no demand request or fire until the
                                       #   counter the REF grant loads with the CSR tRFC reads zero, the first ACT at grant + 1 +
                                       #   tRFC + 2 (16 at the SKU's 13; the proxy probe 2026-11-24); False = the ACT at the
                                       #   device's tRFC with the lookahead (grant + 13), the model before MC-023 item 4
    dir_mode: int = 0                  # GraniteSKU: 0 = the symmetric direction register (the RTL); 1 = the read-priority register
                                       #   priced for memory-controllers MC-024 (no read cap, writes capped at wr_burst, a write
                                       #   turn forced after wr_starve slots of a starved write head)
    wr_starve: int = 512               # GraniteSKU dir_mode 1: write-starvation bound, MC cycles
    wr_burst: int = 16                 # GraniteSKU dir_mode 1: write hold cap, columns
                                       #   column + tRTP / tWR) in MC cycles, the ACT at fire + t_rp_ap of the column's path (MC-020 decision 2;
                                       #   False = the CK-exact DRAM terms alone, the model before 2026-11-22)
    t_rp_ap_rd: int = 1                # GraniteSKU: TIMINGS_RP_AP.tRP_AP_RD -- the tRP the self-close reloads after an RDA, MC cycles (the host's
                                       #   phase-exact derivation at 100 MHz; -1 = the shared tRP, the RTL before the field)
    t_rp_ap_wr: int = 2                # GraniteSKU: TIMINGS_RP_AP.tRP_AP_WR -- after a WRA (the write's close is WL + BL/2 + tWR after the WR)
    close_lag: int = 2                 # GraniteSKU: slots after a PRE before a head that was hitting the closed row requests its ACT (the record's
                                       #   hit flag against the registered row image, the chain hit_lag counts on the way up; MC-021 item 3)
    wr_fill_lag: int = 2               # GraniteSKU: slots after a WRITE beat lands in its bank queue before it is a head record -- the store's
                                       #   write record needs the entry's data fill and the fill-done register, the read record only the
                                       #   queue (a beat entering an empty write queue is the pick's request 3 cycles after it lands, a read
                                       #   beat 1; MC-021 step 6)
    dir_batch_max: int = 255           # GraniteSKU: DIR_BATCH_MAX (0 = no cap)
    dir_hold_idle: int = 8             # GraniteSKU: DIR_HOLD_IDLE (0 = off)
    dir_owns_rows: bool = True         # GraniteSKU: DIR_OWNS_ROWS
    lane: int = 3                      # GraniteSKU: row lane 0 off / 1 PRE only / 2 ACT only / 3 either (DUAL_ISSUE)
    lane_idle: int = 0                 # GraniteSKU: the lane fires into an idle main slot too -- 1 live (the alone-firing lane
                                       #   MC-014 cut for the 100 MHz cone), 2 one slot after a registered idle, the main's row
                                       #   winner yielding that slot (MC-020's candidate form)
    close_on_drain: bool = True        # GraniteSKU: CLOSE_ON_DRAIN auto-precharge
    alternate: bool = True             # GraniteSKU: the row / column alternation of the select
    page_close: bool = False           # GraniteSKU: every column auto-precharges (the board's close_page preset)
    page_mode: int = 4                 # GraniteSKU: PAGE_POLICY_CFG.policy_mode -- 4 the hybrid (the board's `defaults`, the RDL reset:
                                       #   the drain auto-precharge on a known conflict always, on a drained queue only where the bank's
                                       #   history arms it, else the idle timeout closes the row), 0 the legacy flat rule (close-on-drain
                                       #   everywhere: the board's open_page preset writes mode 0), 1 static_open, 2 static_close,
                                       #   3 fixed_open (ISSUE-006, 2026-11-20)
    tr_init: int = 2                   # GraniteSKU: PAGE_TIMEOUT_CFG.tr_init, idle slots before the background close (the RDL reset 2)
    addr_map: str = "row_major"        # the board's ADDR_MAP preset the stream is encoded under (ADDR_MAPS)
    note: str = ""


CONFIGS = {
    # the ideal FR-FCFS open-page controller with Ramulator's default queues
    "open32": ModelConfig("open32", note="FR-FCFS, open page, 32-deep read and write queues, AllBank refresh"),
    # queues the depth of granite's storage-lite seam (GRANITE_SEAM_N = 8 per direction)
    "open8": ModelConfig("open8", read_buffer=8, write_buffer=8,
                         note="as open32 with 8-deep queues (granite's seam depth)"),
    # the MC-015 pool (GRANITE_NUM_ENTRIES=16 on the board build)
    "open16": ModelConfig("open16", read_buffer=16, write_buffer=16,
                          note="as open32 with 16-deep queues (granite's pool at 16, MC-015)"),
    # close the page after every column access: the board's close_page preset
    "closed32": ModelConfig("closed32", row_policy="closed_cap", cap=1,
                            note="FR-FCFS, close after one column access (auto-precharge), 32-deep queues"),
    # refresh off: how much of a gap is refresh
    "open32_noref": ModelConfig("open32_noref", refresh=False, note="as open32 without refresh"),
    # every constraint rounded up to 2 CK: the granularity of the RTL's MC-cycle timers
    "open32_mc2": ModelConfig("open32_mc2", mc_granular=True,
                              note="as open32 with every timing constraint rounded up to 2 CK (MC-cycle granular, as the RTL counts)"),
}


def _wm(base: str, lo: float, hi: float) -> ModelConfig:
    """MC-013 item 2: the write-drain hysteresis at (lo, hi) on an existing config."""
    b = CONFIGS[base]
    name = f"{base}_wm{int(round(lo * 100)):02d}_{int(round(hi * 100)):02d}"
    return replace(b, name=name, wr_low_wm=lo, wr_high_wm=hi,
                   note=f"as {base} with the write drain entered above {hi:.2f} and left below {lo:.2f} of the write queue")


CONFIGS.update({c.name: c for c in [
    # item 2: write drain -- shallow / deep / late / near-full hysteresis on both queue depths
    _wm("open32", 0.05, 0.25), _wm("open32", 0.40, 0.90), _wm("open32", 0.70, 0.95), _wm("open32", 0.03, 0.97),
    _wm("open8", 0.05, 0.25), _wm("open8", 0.40, 0.90), _wm("open8", 0.70, 0.95), _wm("open8", 0.03, 0.97),
    # item 3: refresh placement -- AllBank refresh staggered across the scope nodes by nREFI / 8 (1560 / 8 CK at
    # 200 MHz CK); one rank is one scope node, so this must reproduce open32 exactly (the check that it does)
    replace(CONFIGS["open32"], name="open32_scatter", scatter_interval=195,
            note="as open32 with AllBank refresh scattered across the refresh-scope nodes (one rank: inert by construction)"),
    # the row-hit-first FR-FCFS upstream ships (a pooled queue that will not preempt an open row's hits)
    replace(CONFIGS["open32"], name="open32_rowhit", scheduler="FRFCFS-RowHit",
            note="as open32 with upstream's FRFCFS-RowHit scheduler (a row hit is never preempted by a row miss)"),
    # item 3: eight refreshes as one burst every 8 tREFI -- what REF_CTRL.refresh_burst would buy if it were live:
    # the same tRFC per tREFI, one row close / reopen per eight refreshes instead of per refresh
    replace(CONFIGS["open32"], name="open32_refburst8", ref_burst=8,
            note="as open32 with the refreshes issued eight at a time every 8 tREFI (the DDR2 postpone credit as one burst)"),
    # item 4: per-bank FIFOs with a round-robin pick (granite's store + pick shape) against the pooled FR-FCFS CAM
    replace(CONFIGS["open32"], name="open32_bankrr", scheduler="BankFIFO-RR",
            note="as open32 with per-bank FIFO queues and a round-robin pick across the ready bank heads (BankFIFO-RR)"),
    replace(CONFIGS["open32"], name="open32_bankrr_col", scheduler="BankFIFO-RR", column_first=True,
            note="as open32_bankrr with a ready column command preferred over a ready row command"),
    replace(CONFIGS["open8"], name="open8_bankrr", scheduler="BankFIFO-RR",
            note="as open8 with per-bank FIFO queues and a round-robin pick across the ready bank heads (BankFIFO-RR)"),
    replace(CONFIGS["open8"], name="open8_bankrr_col", scheduler="BankFIFO-RR", column_first=True,
            note="as open8_bankrr with a ready column command preferred over a ready row command"),
]})


def _peek(base: str, depth: int) -> ModelConfig:
    """MC-016: BankFIFO-RR with column_first and a bank head that yields to a younger row hit within its
    first `depth` entries when the head is a row conflict. depth 0 = the whole queue (an upper bound:
    a per-bank pooled hit-first pick); the name carries the depth (`_2h`, `_4h`, `_allh`)."""
    b = CONFIGS[base]
    d = b.read_buffer if depth == 0 else depth
    tag = "allh" if depth == 0 else f"{depth}h"
    what = ("any younger row hit in the queue" if depth == 0
            else f"a younger row hit among its first {depth} entries")
    return replace(b, name=f"{base}_bankrr_{tag}", scheduler="BankFIFO-RR", column_first=True, peek_depth=d,
                   note=f"as {base}_bankrr_col with a bank head that is a row conflict yielding to {what}")


CONFIGS.update({c.name: c for c in [
    # MC-016: the row-hit-first pooled queue and the strict per-bank FIFO at the 16-deep pool too
    replace(CONFIGS["open8"], name="open8_rowhit", scheduler="FRFCFS-RowHit",
            note="as open8 with upstream's FRFCFS-RowHit scheduler"),
    replace(CONFIGS["open16"], name="open16_rowhit", scheduler="FRFCFS-RowHit",
            note="as open16 with upstream's FRFCFS-RowHit scheduler"),
    replace(CONFIGS["open16"], name="open16_bankrr_col", scheduler="BankFIFO-RR", column_first=True,
            note="as open16 with per-bank FIFO queues, a round-robin pick and a ready column preferred over a ready row"),
    # MC-016: the two-head store (a bank's second entry fires when the head is a row conflict and it is a hit),
    # a four-deep peek, and the whole queue as the per-bank upper bound, at every pool depth
    # 8 and 16 bracket the AXI burst: the trace is one request per beat, so at AxLEN 8 the seven entries
    # behind a head are its own burst's beats (the same row); a hit behind a conflict is at least 8 deep
    _peek("open32", 2), _peek("open32", 4), _peek("open32", 8), _peek("open32", 16), _peek("open32", 0),
    _peek("open16", 2), _peek("open16", 4), _peek("open16", 8), _peek("open16", 0),
    _peek("open8", 2), _peek("open8", 4), _peek("open8", 0),
]})


# ---- MC-018: the SKU and its one-term variants -------------------------------
SKU = ModelConfig("granite_sku100", timing_preset="DDR2_GRANITE_SKU100_PX", controller="GraniteSKU",
                  read_buffer=16, write_buffer=16, scheduler="FRFCFS",
                  note="THE SKU: GraniteSKU controller (bank-FIFO store, pick-core select, direction register, "
                       "row lane, the hybrid page policy -- conflict / history-armed drain auto-precharge, idle "
                       "timeout 2 -- one slot per MC cycle) at pool 16, BANK_CAP_MIXED 6, cap 255, hold-idle 8, on "
                       "the host's phase-exact MC-cycle timings (DDR2_GRANITE_SKU100_PX, the default since "
                       "2026-11-22, MC-020): the board's `defaults` preset")


def _sku(tag: str, note: str, **kw) -> ModelConfig:
    return replace(SKU, name=f"sku_{tag}", note=f"as granite_sku100 with {note}", **kw)


CONFIGS.update({c.name: c for c in [
    SKU,
    # the board's other two presets on the SKU
    # The board's `bank_interleave` preset is the map AND close page: pumice_char.py's ControllerConfig programs
    # SCHEME_BANK_INTERLEAVE with PAGE_POLICY_CLOSE (the open-page interleave is its `open_interleave`, which the
    # SKU campaign did not run). Until 2026-11-17 this config was open page and ISSUE-002's factor of three was
    # that configuration error, not the RTL.
    replace(SKU, name="granite_sku100_bi", addr_map="bank_interleave", page_close=True, page_mode=0,
            note="the SKU with the stream encoded under the board's bank_interleave map (bank_lsb 2) and every "
                 "column auto-precharging (the preset programs PAGE_POLICY_CLOSE, policy_mode 0)"),
    replace(SKU, name="granite_sku100_close", page_close=True, page_mode=0,
            note="the SKU with every column auto-precharging (the board's close_page preset, policy_mode 0)"),
    # the board's open_page preset: pumice_char's ControllerConfig writes PAGE_POLICY_OPEN and policy_mode 0, the
    # legacy flat rule -- close-on-drain everywhere, no history gate, no timeout. Until 2026-11-20 this WAS the
    # model's granite_sku100, standing in for `defaults` too (ISSUE-006)
    replace(SKU, name="granite_sku100_open", page_mode=0,
            note="the SKU under the board's open_page preset: policy_mode 0, the flat close-on-drain auto-precharge "
                 "(the model's only page policy before ISSUE-006)"),
    # the ideal at the SKU's timings: what the timing set alone costs (GenericDDR row-hit-first, pool 16)
    replace(SKU, name="sku_ideal16", controller="GenericDDR", scheduler="FRFCFS-RowHit",
            note="GenericDDR FRFCFS-RowHit at pool 16 on the SKU timing preset: the ideal with the SKU's counters"),
    # one-term variants
    _sku("pool8", "pool 8", read_buffer=8, write_buffer=8),
    _sku("pool24", "pool 24", read_buffer=24, write_buffer=24),
    _sku("pool32", "pool 32", read_buffer=32, write_buffer=32),
    _sku("cap0", "BANK_CAP_MIXED off", bank_cap_mixed=0),
    _sku("cap4", "BANK_CAP_MIXED 4", bank_cap_mixed=4),
    _sku("cap8", "BANK_CAP_MIXED 8", bank_cap_mixed=8),
    _sku("capburst", "BANK_CAP_MIXED once per AXI burst, the burst's other beats exempt (the MC-018 form)", cap_per_beat=False),
    _sku("lag0", "a beat is a schedulable head the slot after its acceptance (the MC-018 form)", admit_lag=0),
    _sku("lag2", "admission lag 2 MC cycles", admit_lag=2),
    _sku("lag6", "admission lag 6 MC cycles", admit_lag=6),
    _sku("reqfull", "a request needs every timer, rank-level too (the MC-018 form: no cap flip to a turnaround-blocked column)",
         req_bank_timing=False),
    # MC-021: the pick pipeline's terms, each changed in turn; the two RTL questions priced in the model
    _sku("la0", "no lookahead and no hint: every hop pays the decode and winner registers", pick_la=0),
    _sku("la1", "lookahead / hint reach of one slot", pick_la=1),
    _sku("la3", "lookahead / hint reach of three slots", pick_la=3),
    _sku("rankok1", "the N+1 global timers before memory-controllers BUG-004 (ACT -> ACT at t_rrd + 1)", rank_ok_lag=1),
    _sku("apactla", "the lookahead arms the ACT after an auto-precharge (RTL question 1)", ap_act_la=True),
    _sku("apstale", "an auto-precharging column's pair is stale after its pick (RTL question 2)", ap_stale=True),
    _sku("hitlag1", "the decode reads the row hit live, the slot after the ACT (the step-3 model)", hit_lag=1),
    _sku("noapfirestale", "the stale mask's fire term before MC-021 step 4: a fired pair masked only when its queue emptied", ap_fire_stale=False),
    _sku("wrfill0", "a write beat is a head record the slot it lands, like a read (the model before MC-021 step 6)", wr_fill_lag=0),
    _sku("closelag0", "a head whose row a PRE closed requests its ACT off the live row image (the model before MC-021 step 8)", close_lag=0),
    _sku("admit3", "one three-slot admission stage on every path (the model before MC-021 step 7: the cap path a slot slow)",
         admit_lag=3, pool_gate_lag=0, cap_gate_lag=0),
    _sku("batch64", "DIR_BATCH_MAX 64", dir_batch_max=64),
    _sku("batch128", "DIR_BATCH_MAX 128", dir_batch_max=128),
    _sku("batch0", "no batch cap", dir_batch_max=0),
    _sku("hold0", "DIR_HOLD_IDLE off", dir_hold_idle=0),
    _sku("hold16", "DIR_HOLD_IDLE 16", dir_hold_idle=16),
    _sku("noown", "DIR_OWNS_ROWS off", dir_owns_rows=False),
    _sku("laneoff", "the row lane off (DUAL_ISSUE 0)", lane=0),
    _sku("lanepre", "the row lane carrying PRE only", lane=1),
    _sku("laneact", "the row lane carrying ACT only", lane=2),
    _sku("laneidle", "the row lane also firing into an idle main slot, live (the alone-firing lane MC-014 cut)", lane_idle=1),
    _sku("rpshared", "the auto-precharge self-close reloading the shared tRP (2 / 2): the RTL before the TIMINGS_RP_AP "
         "fields (MC-020 decision 2)", t_rp_ap_rd=2, t_rp_ap_wr=2),
    _sku("rdprio", "the read-priority direction register (memory-controllers MC-024: no read cap, write holds of 16 "
         "columns, a write turn after 512 starved cycles)", dir_mode=1),
    _sku("norfcblock", "the first ACT after a refresh at the device's tRFC with the lookahead, no tRFC demand block: "
         "the model before memory-controllers MC-023 item 4", rfc_block=False),
    _sku("noapseq", "the auto-precharge path at the CK-exact DRAM terms alone: the model before the sequenced self-close "
         "(MC-020 decision 2)", ap_seq=False),
    _sku("margin", "the SKU's counters under the one-CK phase margin the host derived until 2026-11-22 (tRC 7, tWR 4, "
         "tWTR 4, tRRD 2, tRFC 14: DDR2_GRANITE_SKU100; the board's JEDEC_PHASE_EXACT=0; MC-020), the self-close "
         "reloading the shared tRP as the margin's host programs it",
         timing_preset="DDR2_GRANITE_SKU100", t_rp_ap_rd=2, t_rp_ap_wr=2),
    _sku("laneidle_reg", "the row lane firing alone one slot after a registered idle main slot, the main's row winner yielding (MC-020)", lane_idle=2),
    _sku("noalt", "no row / column alternation (columns first always)", alternate=False),
    _sku("peek16_pool32", "pool 32 and a 16-deep row-hit peek past a conflicting head", read_buffer=32,
         write_buffer=32, peek_depth=16),
    _sku("peek2", "a two-entry peek (the two-head record as a real lookahead)", peek_depth=2),
    _sku("refburst8", "eight refreshes per burst every 8 tREFI", ref_burst=8),
    _sku("slot1", "a command slot every CK (the one-slot-per-MC-cycle cost; the lane is then moot)", slot_ticks=1),
    _sku("jedec", "the JEDEC CK timings (DDR2_MT47H64M16_400_CL3) instead of the host's MC-cycle counters",
         timing_preset="DDR2_MT47H64M16_400_CL3"),
]})

SKU_VARIANTS = [c for c in CONFIGS if c.startswith("sku_")]


def _mc_granular_class(base):
    """A DDR2 variant whose constraint latencies round up to 2 CK (Ramulator's
    command_slot_cycles). It keeps the base class's name because the C++ side
    is keyed by it and nothing here is codegen'd; it is the RTL's MC-cycle
    counter granularity (DFI 1:2), not a different device."""
    attrs = {"name": base.name, "command_slot_cycles": 2, "__doc__": "DDR2 at 2 CK constraint granularity"}
    cls = type(base.__name__ + "_MC2", (base,), attrs)
    cls.org_presets = base.org_presets
    cls.timing_presets = base.timing_presets
    return cls


def _ref_burst_class(base, n: int):
    """A DDR2 variant whose refresh is n REFab back to back every n tREFI: nRFC and nREFI
    both scaled by n (the class resolves them from the density, so the override lands after
    that). The REF->ACT->RD reopen then happens once per n refreshes; the bus time in REF is
    unchanged. It is the DDR2 postpone credit (JESD79-2F: up to 8 REFs) spent as one burst."""
    def resolve_secondary_timings(cls, timing_dict, org_dict):
        base.resolve_secondary_timings.__func__(cls, timing_dict, org_dict)
        timing_dict["nRFC"] *= n
        timing_dict["nREFI"] *= n
    attrs = {"name": base.name, "resolve_secondary_timings": classmethod(resolve_secondary_timings),
             "__doc__": f"DDR2 with {n} refreshes per burst"}
    cls = type(base.__name__ + f"_REFx{n}", (base,), attrs)
    cls.org_presets = base.org_presets
    cls.timing_presets = base.timing_presets
    return cls


def _sku_param_overrides() -> dict:
    """GRANITE_SKU_PARAMS="t_rp_ap_rd=2,t_rp_ap_wr=2": GraniteSKU controller knobs overridden for this run on
    whatever config is named (MC-020 decision 2 priced the RTL before the TIMINGS_RP_AP fields on the four
    SKU configs this way). Values are ints, or true / false for a bool knob; unset = the config's own."""
    spec = os.environ.get("GRANITE_SKU_PARAMS", "")
    out: dict = {}
    for kv in filter(None, (x.strip() for x in spec.split(","))):
        k, v = (x.strip() for x in kv.split("=", 1))
        out[k] = (v.lower() == "true") if v.lower() in ("true", "false") else int(v, 0)
    return out


def _sku_debug_params() -> dict:
    """GRANITE_SKU_DEBUG=<from_ck>:<to_ck> prints the GraniteSKU controller's slot state, picks, lane
    loads and holds between those CK, and every direction flip of the run, on stdout; unset = silent."""
    spec = os.environ.get("GRANITE_SKU_DEBUG", "")
    if not spec:
        return {}
    lo, hi = (int(x, 0) for x in spec.split(":"))
    return {"debug": True, "debug_from": lo, "debug_to": hi}


def build_sim(cfg: ModelConfig, trace_path: str, *, bl8: bool = False, split: bool = False):
    import ramulator  # noqa: WPS433  (vendor module)

    dram_cls = ramulator.dram.DDR2_BL8 if bl8 else ramulator.dram.DDR2
    if cfg.mc_granular:
        dram_cls = _mc_granular_class(dram_cls)
    if cfg.ref_burst > 1:
        dram_cls = _ref_burst_class(dram_cls, cfg.ref_burst)
    # GRANITE_TIMING_PRESET=<name>: run a config on another timing preset (MC-020 priced the phase-exact
    # counters this way before they became the SKU's; DDR2_GRANITE_SKU100 is the margin set, a board run
    # made with JEDEC_PHASE_EXACT=0)
    dram = dram_cls(org_preset=cfg.org_preset,
                    timing_preset=os.environ.get("GRANITE_TIMING_PRESET", "") or cfg.timing_preset)
    if cfg.row_policy == "open":
        row_policy = ramulator.row_policy.Open()
    elif cfg.row_policy == "closed_cap":
        row_policy = ramulator.row_policy.ClosedCAP(cap=cfg.cap)
    else:
        raise ValueError(cfg.row_policy)
    refresh = (ramulator.refresh_manager.AllBank(scope="Rank", scatter_interval=cfg.scatter_interval)
               if cfg.refresh else ramulator.refresh_manager.NoRefresh())
    if cfg.scheduler == "BankFIFO-RR":
        # the overlay's scheduler (overlay/src/.../scheduler/impl/bank_fifo_rr.cpp); codegen names the class
        scheduler = ramulator.scheduler.BankFIFORR(column_first=cfg.column_first, peek_depth=cfg.peek_depth)
    else:
        scheduler = {"FRFCFS": ramulator.scheduler.FRFCFS,
                     "FRFCFS-RowHit": ramulator.scheduler.FRFCFSRowHit}[cfg.scheduler]()
    if cfg.controller == "GraniteSKU":
        # the overlay's SKU controller (granite_sku_controller.cpp); it picks for itself, so the scheduler and
        # row policy children are the required placeholders and inert
        # the config's knobs, then GRANITE_SKU_PARAMS over them (a run of any config with a knob overridden)
        sku_kw = dict(
            dram=dram, scheduler=scheduler, refresh_manager=refresh, row_policy=row_policy,
            addr_mapper=ramulator.addr_mapper.RoBaRaCoCh(),
            read_buffer_size=cfg.read_buffer, write_buffer_size=cfg.write_buffer,
            slot_ticks=cfg.slot_ticks, bank_cap_mixed=cfg.bank_cap_mixed, cap_per_beat=cfg.cap_per_beat,
            admit_lag=cfg.admit_lag, pool_gate_lag=cfg.pool_gate_lag, cap_gate_lag=cfg.cap_gate_lag,
            dir_batch_max=cfg.dir_batch_max,
            dir_hold_idle=cfg.dir_hold_idle, dir_owns_rows=cfg.dir_owns_rows, lane=cfg.lane, lane_idle=cfg.lane_idle,
            close_on_drain=cfg.close_on_drain, alternate=cfg.alternate, page_close=cfg.page_close,
            page_mode=cfg.page_mode, tr_init=cfg.tr_init,
            peek_depth=cfg.peek_depth, req_bank_timing=cfg.req_bank_timing,
            pick_la=cfg.pick_la, rank_ok_lag=cfg.rank_ok_lag, ap_act_la=cfg.ap_act_la, ap_stale=cfg.ap_stale,
            hit_lag=cfg.hit_lag, ap_fire_stale=cfg.ap_fire_stale, wr_fill_lag=cfg.wr_fill_lag, close_lag=cfg.close_lag,
            ap_seq=cfg.ap_seq, t_rp_ap_rd=cfg.t_rp_ap_rd, t_rp_ap_wr=cfg.t_rp_ap_wr, rfc_block=cfg.rfc_block,
            dir_mode=cfg.dir_mode, wr_starve=cfg.wr_starve, wr_burst=cfg.wr_burst,
            **_sku_debug_params(),
        )
        sku_kw.update(_sku_param_overrides())
        ctrl = ramulator.controller.GraniteSKU(**sku_kw)
    else:
        ctrl = ramulator.controller.GenericDDR(
            dram=dram, scheduler=scheduler, refresh_manager=refresh, row_policy=row_policy,
            addr_mapper=ramulator.addr_mapper.RoBaRaCoCh(),
            read_buffer_size=cfg.read_buffer, write_buffer_size=cfg.write_buffer,
            wr_low_watermark=cfg.wr_low_wm, wr_high_watermark=cfg.wr_high_wm,
        )
    # frontend = the MC clock (one AXI beat per tick), memory system = CK at 2x
    # GRANITE_GO_OFFSET=<ticks>: the GO against the model's refresh phase (MC-021 item 3; 0 = the run starts at GO)
    frontend = ramulator.frontend.TimedLoadStoreTrace(clock_ratio=1, path=trace_path, split_directions=split,
                                                      start_tick=int(os.environ.get("GRANITE_GO_OFFSET", "0"), 0))
    mem = ramulator.memory_system.GenericDRAM(
        clock_ratio=2, controllers=[ctrl],
        channel_mapper=ramulator.channel_mapper.CacheLineInterleave())
    return ramulator.Simulation(frontend, mem)


# ---------------------------------------------------------------------------
# Running one scenario: a write pass and a read pass (concurrent for `mixed`)
# ---------------------------------------------------------------------------

CSV_FIELDS = [
    "config", "scenario", "family", "burst_len", "txn_count", "threads", "bytes_moved", "clk_mhz",
    "wr_cycles", "wr_bw_mb_s", "rd_cycles", "rd_bw_mb_s", "rd_avg_latency_cyc",
    "wr_row_hits", "wr_row_misses", "wr_row_conflicts",
    "rd_row_hits", "rd_row_misses", "rd_row_conflicts",
    "wr_coalesced", "rd_forwarded", "wr_stall_ticks", "rd_stall_ticks",
    # MC-018: the SKU controller's own counters (0 / empty on GenericDDR). Latencies are MC cycles.
    "rd_lat_max", "wr_wait_max", "dir_flips", "zero_col_turns", "lane_act", "lane_pre", "to_pre", "cap_refused",
    "slot_col_pct", "slot_row_pct",
    # MC-024: the write MB/s while the reads hold the bus (mixed only): the writes completed by the last
    # read completion over the window up to it. wr_bw_mb_s is the write window, which includes any
    # writes-only tail after the reads end.
    "wr_bw_rd_live_mb_s", "elapsed_s", "notes",
]


def _sku_cols(c: dict, tag: str = "") -> dict:
    """The GraniteSKU counters of one pass (empty strings on a controller without them)."""
    if "sku_slots" not in c:
        return dict(rd_lat_max="", wr_wait_max="", dir_flips="", zero_col_turns="", lane_act="", lane_pre="",
                    to_pre="", cap_refused="", slot_col_pct="", slot_row_pct="")
    slots = max(int(c["sku_slots"]), 1)
    return dict(rd_lat_max=round(c["sku_max_read_latency"] / 2, 1), wr_wait_max=round(c["sku_max_write_wait"] / 2, 1),
                dir_flips=c["sku_dir_flips"], zero_col_turns=c["sku_zero_col_turns"],
                lane_act=c["sku_lane_act"], lane_pre=c["sku_lane_pre"], to_pre=c.get("sku_to_pre", 0),
                cap_refused=c["sku_cap_refused"],
                slot_col_pct=round(100.0 * c["sku_main_col"] / slots, 1),
                slot_row_pct=round(100.0 * c["sku_main_row"] / slots, 1))


def _window(fe: dict, kind: str) -> int:
    first, last = fe[f"{kind}_first_send_tick"], fe[f"{kind}_last_complete_tick"]
    return max(int(last) - int(first), 0)


def _wr_bw_rd_live(fe: dict, wr_bytes: int) -> float:
    """MC-024: the write MB/s up to the last read completion (the share the writes get while reads hold
    the bus), from the frontend's writes_at_read_last; the window starts at the first write sent. When
    the writes finish first they were never held behind live reads, and it is their own window."""
    done = int(fe.get("num_writes_completed", 0))
    if not done or "writes_at_read_last" not in fe:
        return 0.0
    if int(fe["write_last_complete_tick"]) <= int(fe["read_last_complete_tick"]):
        return _bw(wr_bytes, _window(fe, "write"))      # the writes finished first: their own window
    live_bytes = wr_bytes * int(fe["writes_at_read_last"]) // done
    return _bw(live_bytes, max(int(fe["read_last_complete_tick"]) - int(fe["write_first_send_tick"]), 0))


def _bw(bytes_moved: int, cycles: int) -> float:
    return round(bytes_moved / cycles * MC_CLK_MHZ, 2) if cycles else 0.0


def run_pass(cfg: ModelConfig, trace_path: str, *, split: bool = False) -> Tuple[dict, dict]:
    sim = build_sim(cfg, trace_path, split=split)
    sim.run()
    st = sim.stats
    return st["frontend"], st["memory_system"]["controller"]


def _both_dirs_row(fe: dict, c: dict) -> dict:
    """The CSV columns of ONE pass that carried both directions (the mixed family, a captured trace)."""
    return dict(wr_cycles=_window(fe, "write"), rd_cycles=_window(fe, "read"),
                rd_avg_latency_cyc=round(c["avg_read_latency"] / 2, 2),
                wr_row_hits=c["write_row_hits"], wr_row_misses=c["write_row_misses"],
                wr_row_conflicts=c["write_row_conflicts"],
                rd_row_hits=c["read_row_hits"], rd_row_misses=c["read_row_misses"],
                rd_row_conflicts=c["read_row_conflicts"],
                wr_coalesced=c["num_write_reqs_coalesced"], rd_forwarded=c["num_read_reqs_forwarded"],
                wr_stall_ticks=fe["stall_ticks"], rd_stall_ticks=fe["stall_ticks"], **_sku_cols(c))


def _two_pass_row(wr: Tuple[dict, dict], rd: Tuple[dict, dict]) -> dict:
    """The CSV columns of a write pass and a read pass run separately (the stride families)."""
    (wfe, wc), (rfe, rc) = wr, rd
    return dict(wr_cycles=_window(wfe, "write"), rd_cycles=_window(rfe, "read"),
                rd_avg_latency_cyc=round(rc["avg_read_latency"] / 2, 2),
                wr_row_hits=wc["write_row_hits"], wr_row_misses=wc["write_row_misses"],
                wr_row_conflicts=wc["write_row_conflicts"],
                rd_row_hits=rc["read_row_hits"], rd_row_misses=rc["read_row_misses"],
                rd_row_conflicts=rc["read_row_conflicts"],
                wr_coalesced=wc["num_write_reqs_coalesced"], rd_forwarded=rc["num_read_reqs_forwarded"],
                wr_stall_ticks=wfe["stall_ticks"], rd_stall_ticks=rfe["stall_ticks"], **_two_pass_sku(wc, rc))


def _two_pass_sku(wc: dict, rc: dict) -> dict:
    """SKU counters of two single-direction passes: the read pass's latency and slot shares (the pass the
    rd_* columns describe), the write pass's wait, the two passes' lane and flip counts summed."""
    w, r = _sku_cols(wc), _sku_cols(rc)
    if r["rd_lat_max"] == "":
        return r
    return dict(rd_lat_max=r["rd_lat_max"], wr_wait_max=w["wr_wait_max"],
                dir_flips=w["dir_flips"] + r["dir_flips"], zero_col_turns=w["zero_col_turns"] + r["zero_col_turns"],
                lane_act=w["lane_act"] + r["lane_act"], lane_pre=w["lane_pre"] + r["lane_pre"],
                to_pre=w["to_pre"] + r["to_pre"], cap_refused=w["cap_refused"] + r["cap_refused"],
                slot_col_pct=r["slot_col_pct"], slot_row_pct=r["slot_row_pct"])


def trace_bytes(path: str) -> Tuple[int, int]:
    """(store bytes, load bytes) a TimedLoadStoreTrace file moves: one TX_BYTES transaction per line."""
    st = ld = 0
    with open(path) as f:
        for ln in f:
            parts = ln.split()
            if len(parts) != 3:
                continue
            if parts[1] == "ST":
                st += 1
            elif parts[1] == "LD":
                ld += 1
    return st * TX_BYTES, ld * TX_BYTES


def run_trace_files(cfg: ModelConfig, name: str, *, wr: Optional[str] = None, rd: Optional[str] = None,
                    both: Optional[str] = None, split: bool = False) -> dict:
    """One CSV row from CAPTURED traces (MC-013 item 5): either a write trace and a read trace run as two
    passes, or one trace carrying both directions. The bandwidth definition is unchanged: bytes the trace
    moves per direction over that direction's first-send to last-complete window."""
    t0 = time.time()
    row = dict(config=cfg.name, scenario=name, family="trace", burst_len=0, threads=0, clk_mhz=MC_CLK_MHZ)
    if both:
        wb, rb = trace_bytes(both)
        fe, c = run_pass(cfg, both, split=split)
        row.update(_both_dirs_row(fe, c), txn_count=(wb + rb) // TX_BYTES, bytes_moved=max(wb, rb))
        notes = [f"captured trace {os.path.basename(both)}: {wb // TX_BYTES} ST + {rb // TX_BYTES} LD beats, union "
                 f"{_bw(wb + rb, fe['cycles'])} MB/s over {fe['cycles']} cycles"]
    else:
        if not (wr and rd):
            raise ValueError("run_trace_files needs --both, or --wr and --rd")
        wb, _ = trace_bytes(wr)
        _, rb = trace_bytes(rd)
        row.update(_two_pass_row(run_pass(cfg, wr), run_pass(cfg, rd)),
                   txn_count=(wb + rb) // TX_BYTES, bytes_moved=max(wb, rb))
        notes = [f"captured traces {os.path.basename(wr)} ({wb // TX_BYTES} ST beats) and "
                 f"{os.path.basename(rd)} ({rb // TX_BYTES} LD beats)"]
    row["wr_bw_mb_s"] = _bw(wb, row["wr_cycles"])
    row["rd_bw_mb_s"] = _bw(rb, row["rd_cycles"])
    if row["wr_coalesced"] or row["rd_forwarded"]:
        notes.append(f"controller coalesced {row['wr_coalesced']} writes / forwarded "
                     f"{row['rd_forwarded']} reads (the board does neither)")
    row["elapsed_s"] = round(time.time() - t0, 1)
    row["notes"] = "; ".join(notes)
    return row


def run_scenario(cfg: ModelConfig, sc: Scenario, tmpdir: str) -> dict:
    t0 = time.time()
    w_walks, r_walks = injector_walks(sc)
    per_dir_bytes = sum(len(w) for w in w_walks) * sc.burst_bytes
    notes: List[str] = []
    row = dict(config=cfg.name, scenario=sc.name, family=sc.family, burst_len=sc.burst_len,
               txn_count=sc.txn_count, threads=sc.threads, bytes_moved=per_dir_bytes, clk_mhz=MC_CLK_MHZ)
    am = cfg.addr_map
    if sc.family == "mixed":
        path = os.path.join(tmpdir, f"{sc.name}.trace")
        write_trace(path, [interleave_bursts(w_walks, sc.burst_len, "ST"),
                           interleave_bursts(r_walks, sc.burst_len, "LD")], addr_map=am, split=sc.split)
        fe, c = run_pass(cfg, path, split=sc.split)
        row.update(_both_dirs_row(fe, c))
        rd_bytes = sum(len(r) for r in r_walks) * sc.burst_bytes   # = per_dir_bytes unless the sustained suite's param
        notes.append(f"{sc.threads} writers + {sc.threads} readers from one GO, union "
                     f"{_bw(per_dir_bytes + rd_bytes, fe['cycles'])} MB/s over {fe['cycles']} cycles"
                     + ("; two independent streams (split_directions)" if sc.split else "")
                     + (f"; streams {per_dir_bytes} / {rd_bytes} bytes" if rd_bytes != per_dir_bytes else ""))
        row["wr_bw_mb_s"] = _bw(per_dir_bytes, row["wr_cycles"])
        row["rd_bw_mb_s"] = _bw(rd_bytes, row["rd_cycles"])
        row["wr_bw_rd_live_mb_s"] = _wr_bw_rd_live(fe, per_dir_bytes)
    elif sc.family == "rw_mix":
        path = os.path.join(tmpdir, f"{sc.name}.trace")
        write_trace(path, [interleave_mixed_bursts(w_walks, sc.burst_len, sc.param)], addr_map=am)
        wb, rb = trace_bytes(path)
        fe, c = run_pass(cfg, path)
        row.update(_both_dirs_row(fe, c), bytes_moved=wb + rb)
        row["wr_bw_mb_s"] = _bw(wb, row["wr_cycles"])
        row["rd_bw_mb_s"] = _bw(rb, row["rd_cycles"])
        notes.append(f"{sc.threads} injectors, {int(sc.param * 100)} percent writes per burst, union "
                     f"{_bw(wb + rb, fe['cycles'])} MB/s over {fe['cycles']} cycles")
    else:
        wpath = os.path.join(tmpdir, f"{sc.name}_wr.trace")
        rpath = os.path.join(tmpdir, f"{sc.name}_rd.trace")
        write_trace(wpath, [interleave_bursts(w_walks, sc.burst_len, "ST")], addr_map=am)
        write_trace(rpath, [interleave_bursts(r_walks, sc.burst_len, "LD")], addr_map=am)
        row.update(_two_pass_row(run_pass(cfg, wpath), run_pass(cfg, rpath)))
        row["wr_bw_mb_s"] = _bw(per_dir_bytes, row["wr_cycles"])
        row["rd_bw_mb_s"] = _bw(per_dir_bytes, row["rd_cycles"])
        if sc.family == "locality":
            notes.append(f"{sc.threads} injectors, one bank each, row-hit probability {sc.param:.1f} over "
                         f"{REGION_ROWS} rows")
        elif sc.family == "bank_step":
            notes.append(f"every burst a miss, stepping {int(sc.param)} banks ({8 // int(sc.param)} banks in play)")
    if row["wr_coalesced"] or row["rd_forwarded"]:
        notes.append(f"controller coalesced {row['wr_coalesced']} writes / forwarded "
                     f"{row['rd_forwarded']} reads (the board does neither)")
    go = int(os.environ.get("GRANITE_GO_OFFSET", "0"), 0)
    if go:
        notes.append(f"GO offset {go} ticks against the refresh phase")
    row["elapsed_s"] = round(time.time() - t0, 1)
    row["notes"] = "; ".join(notes)
    return row


def cmd_run(args: argparse.Namespace) -> int:
    cfg = CONFIGS[args.config]
    scenarios = SUITES[args.suite]
    if args.only:
        scenarios = [s for s in scenarios if s.name in set(args.only)]
    if args.scale != 1.0:
        scenarios = [replace(s, txn_count=max(1, int(s.txn_count * args.scale))) for s in scenarios]
    if args.txn:
        scenarios = [replace(s, txn_count=args.txn) for s in scenarios]
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="char_model_") as tmp, open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        w.writeheader()
        for i, sc in enumerate(scenarios, 1):
            print(f"[{i}/{len(scenarios)}] {cfg.name} {sc.name} ...", flush=True)
            row = run_scenario(cfg, sc, tmp)
            w.writerow(row)
            f.flush()
            extra = (f", rd_lat_max {row['rd_lat_max']} flips {row['dir_flips']} lane {row['lane_act']}+{row['lane_pre']}"
                     if row["dir_flips"] != "" else "")
            print(f"    wr {row['wr_bw_mb_s']} / rd {row['rd_bw_mb_s']} MB/s  "
                  f"(rd hits/miss/conf {row['rd_row_hits']}/{row['rd_row_misses']}/{row['rd_row_conflicts']}"
                  f"{extra}, {row['elapsed_s']} s)", flush=True)
    print(f"wrote {args.out}")
    return 0


def cmd_run_trace(args: argparse.Namespace) -> int:
    cfg = CONFIGS[args.config]
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    print(f"{cfg.name} {args.name} ...", flush=True)
    row = run_trace_files(cfg, args.name, wr=args.wr, rd=args.rd, both=args.both, split=args.split)
    new = not os.path.exists(args.out) or args.overwrite
    with open(args.out, "w" if new else "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        if new:
            w.writeheader()
        w.writerow(row)
    print(f"    wr {row['wr_bw_mb_s']} / rd {row['rd_bw_mb_s']} MB/s  "
          f"(rd hits/miss/conf {row['rd_row_hits']}/{row['rd_row_misses']}/{row['rd_row_conflicts']}, "
          f"{row['elapsed_s']} s)  -> {args.out}", flush=True)
    return 0


# ---------------------------------------------------------------------------
# compare: model cells beside the measured granite / LiteDRAM cells
# ---------------------------------------------------------------------------


def _load_measured(dirpath: str, controller: str, tag: str) -> Dict[Tuple[str, str], dict]:
    """{(config, scenario): row} from char_<controller>_<tag-with-suite>.csv for every suite."""
    out: Dict[Tuple[str, str], dict] = {}
    point, date = tag.rsplit("_", 1)
    for suite in ("every", "windows"):
        path = os.path.join(dirpath, f"char_{controller}_{point}_{suite}_{date}.csv")
        if not os.path.exists(path):
            continue
        with open(path, newline="") as f:
            for r in csv.DictReader(f):
                out[(r["config"], r["scenario"])] = r
    return out


def _cell(r: Optional[dict]) -> str:
    if not r:
        return "-"
    return f"{float(r['wr_bw_mb_s']):.0f} / {float(r['rd_bw_mb_s']):.0f}"


def cmd_compare(args: argparse.Namespace) -> int:
    model: Dict[str, List[dict]] = {}
    for path in args.model:
        with open(path, newline="") as f:
            for r in csv.DictReader(f):
                model.setdefault(r["scenario"], []).append(r)
    granite = _load_measured(args.measured, "granite", args.granite)
    litedram = _load_measured(args.measured, "litedram", args.litedram) if args.litedram else {}
    configs = sorted({r["config"] for rows in model.values() for r in rows})
    gcfgs = [c for c in ("defaults", "open_page", "close_page") if any(k[0] == c for k in granite)]
    lines = [f"# Ramulator 2 DDR2 model beside the measured granite {args.granite} and LiteDRAM {args.litedram or '-'} cells",
             "",
             "Cells are write / read MB/s at the 100 MHz MC clock (DDR2-400 x16 peak 800 MB/s), bandwidth = bytes moved over the",
             "cycles from the first beat in to the last response out, the board host's definition. Model columns are the",
             "Ramulator GenericDDR controller (FR-FCFS) on the DDR2 class at the part's timings (DDR2_MT47H64M16_400_CL3):",
             ""]
    for c in configs:
        lines.append(f"- `{c}`: {CONFIGS[c].note if c in CONFIGS else ''}")
    lines += ["", "| scenario | " + " | ".join(f"model {c}" for c in configs) + " | "
              + " | ".join(f"granite {c}" for c in gcfgs) + (" | LiteDRAM" if litedram else "")
              + " | granite best / model best |",
              "|---|" + "---|" * (len(configs) + len(gcfgs) + (1 if litedram else 0) + 1)]
    for sc in EVERY + WINDOWS:
        if sc.name not in model:
            continue
        mrows = {r["config"]: r for r in model[sc.name]}
        mcells = [_cell(mrows.get(c)) for c in configs]
        gcells = [_cell(granite.get((c, sc.name))) for c in gcfgs]
        lcell = [_cell(litedram.get(("litedram", sc.name)))] if litedram else []
        mbest = max((max(float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"])) for r in mrows.values()), default=0.0)
        gbest = max((max(float(granite[(c, sc.name)]["wr_bw_mb_s"]), float(granite[(c, sc.name)]["rd_bw_mb_s"]))
                     for c in gcfgs if (c, sc.name) in granite), default=0.0)
        ratio = f"{gbest:.0f} / {mbest:.0f} = {gbest / mbest:.2f}x" if mbest and gbest else "-"
        lines.append(f"| {sc.name} | " + " | ".join(mcells + gcells + lcell) + f" | {ratio} |")
    lines += ["", "Model row statistics (read pass, per scenario): hits / misses / conflicts, and the read latency the",
              "controller saw (MC cycles, command accept to data return; the board's rd_avg_latency_cyc includes the",
              "AXI and host path).", "",
              "| scenario | " + " | ".join(f"{c} rd hits/miss/conf" for c in configs) + " | "
              + " | ".join(f"{c} rd lat" for c in configs) + " |",
              "|---|" + "---|" * (2 * len(configs))]
    for sc in EVERY + WINDOWS:
        if sc.name not in model:
            continue
        mrows = {r["config"]: r for r in model[sc.name]}
        hm = [f"{r['rd_row_hits']}/{r['rd_row_misses']}/{r['rd_row_conflicts']}" if (r := mrows.get(c)) else "-"
              for c in configs]
        lat = [f"{float(r['rd_avg_latency_cyc']):.1f}" if (r := mrows.get(c)) else "-" for c in configs]
        lines.append(f"| {sc.name} | " + " | ".join(hm + lat) + " |")
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print(f"wrote {args.out}")
    else:
        sys.stdout.write(text)
    return 0


# ---------------------------------------------------------------------------
# board-compare: the SKU model beside a board CSV set, cell by cell, with a tolerance per family (MC-018 item 2)
# ---------------------------------------------------------------------------

# model config -> the board preset it stands for
BOARD_PRESET_OF = {"granite_sku100": ("defaults",), "granite_sku100_open": ("open_page",),
                   "granite_sku100_bi": ("bank_interleave",), "granite_sku100_close": ("close_page",)}
# percent of the board cell the model must land within, per family. The single-direction row-hit families
# are where the DRAM alone sets the number; random / col_major / mixed are where the SKU terms matter and
# where the match is the test (the task's wording); close_page is timer-bound and host-path heavy.
TOLERANCE_PCT = {"incremental": 2.0, "row_major": 2.0, "col_major_interleaved": 3.0, "row_thrash": 3.0,
                 "col_major": 5.0, "random": 5.0, "mixed": 10.0}
TOLERANCE_PRESET_PCT = {"close_page": 15.0, "bank_interleave": 10.0}


def _pct(model: float, board: float) -> float:
    return (model - board) / board * 100.0 if board else 0.0


def cmd_board_compare(args: argparse.Namespace) -> int:
    model = _load_runs(args.model)
    board = _load_runs(_board_paths(args.measured, "granite", args.granite) + list(args.board_also or []))
    lines = [f"# The SKU model beside the board: granite {args.granite}", "",
             "Cells are write / read MB/s at 100 MHz (bandwidth = bytes over first-beat-in to last-response-out);",
             "delta = (model - board) / board per direction, and the cell is IN when both directions land within",
             "the family's tolerance. `mixed` compares the union (both directions' bytes over the longer window).",
             "A cell with several board runs (`--board-also`) is read BY MODE: runs within the tolerance of each",
             "other are one mode (`xN` = runs in it), every board mode needs a model run within tolerance (several",
             "`--model` CSVs are the model's GO phases, labelled by their `GO offset`), and a model run in a mode",
             "the board never showed is OUT; the delta column then carries one delta per board mode.",
             "", "| board preset | scenario | board wr / rd | model wr / rd | delta wr / rd | tol | verdict |",
             "|---|---|---|---|---|---|---|"]
    n_in = n_out = 0
    worst: List[Tuple[float, str]] = []
    for mcfg, presets in BOARD_PRESET_OF.items():
        for preset in presets:
            for sc in EVERY + WINDOWS:
                b_rows = board.get((preset, sc.name))
                m_rows = model.get((mcfg, sc.name))
                if not b_rows or not m_rows:
                    continue
                tol = TOLERANCE_PRESET_PCT.get(preset, TOLERANCE_PCT.get(sc.family, 5.0))
                mixed = sc.family == "mixed"
                b_obs = [_board_obs(r) for r in b_rows]
                m_obs = [_model_obs(r) for r in m_rows]
                modes = _modes(b_obs, tol, mixed)
                nearest = [min(m_obs, key=lambda o: _dist(o, mode[0], mixed)) for mode in modes]
                deltas = [_dist(o, mode[0], mixed) for o, mode in zip(nearest, modes)]
                every_mode_met = all(d <= tol for d in deltas)
                no_model_mode_unseen = all(any(_dist(o, mode[0], mixed) <= tol for mode in modes) for o in m_obs)
                verdict = "IN" if every_mode_met and no_model_mode_unseen else "OUT"
                worst.append((max(deltas), f"{preset} {sc.name}"))
                if len(b_obs) == 1 and len(m_obs) == 1:
                    cell = _one_run_cell(preset, sc.name, b_obs[0], m_obs[0], mixed, tol, verdict)
                else:
                    cell = _by_mode_cell(preset, sc.name, modes, m_obs, nearest, mixed, tol, verdict)
                lines.append(cell)
                if verdict == "IN":
                    n_in += 1
                else:
                    n_out += 1
    worst.sort(reverse=True)
    lines += ["", f"{n_in} cells in tolerance, {n_out} out. Largest deltas: "
              + ", ".join(f"{name} ({d:.1f} %)" for d, name in worst[:6]) + "."]
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print(f"wrote {args.out}  ({n_in} in / {n_out} out)")
    else:
        sys.stdout.write(text)
    return 0 if n_out == 0 or not args.strict else 1


# One run of a cell: (write MB/s, read MB/s, union MB/s, label). The union is the board CSV's note for the board
# and both directions' bytes over the longer window for the model; the label is the model's GO phase when set.
Obs = Tuple[float, float, float, str]


def _board_paths(dirpath: str, controller: str, tag: str) -> List[str]:
    point, date = tag.rsplit("_", 1)
    paths = [os.path.join(dirpath, f"char_{controller}_{point}_{suite}_{date}.csv") for suite in ("every", "windows")]
    return [p for p in paths if os.path.exists(p)]


def _load_runs(paths: Sequence[str]) -> Dict[Tuple[str, str], List[dict]]:
    """{(config, scenario): [row, ...]} over every CSV, one row per run of the cell."""
    out: Dict[Tuple[str, str], List[dict]] = {}
    for path in paths:
        with open(path, newline="") as f:
            for r in csv.DictReader(f):
                out.setdefault((r["config"], r["scenario"]), []).append(r)
    return out


def _board_obs(r: dict) -> Obs:
    return float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"]), _union_from_notes(r["notes"]), ""


def _model_obs(r: dict) -> Obs:
    import re
    cyc = max(int(r["wr_cycles"]), int(r["rd_cycles"]))
    union = 2 * float(r["bytes_moved"]) / cyc * MC_CLK_MHZ if cyc else 0.0
    m = re.search(r"GO offset (\d+)", r.get("notes", "") or "")
    return float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"]), union, (f"GO {m.group(1)}" if m else "")


def _dist(a: Obs, b: Obs, mixed: bool) -> float:
    """The cell's delta of run a against run b in percent: the union for mixed, else the worse direction."""
    if mixed:
        return abs(_pct(a[2], b[2])) if b[2] else 0.0
    return max(abs(_pct(a[0], b[0])), abs(_pct(a[1], b[1])))


def _modes(obs: List[Obs], tol: float, mixed: bool) -> List[List[Obs]]:
    """Board runs grouped by mode: a run joins the first mode whose first run it is within the tolerance of."""
    modes: List[List[Obs]] = []
    for o in obs:
        for mode in modes:
            if _dist(o, mode[0], mixed) <= tol:
                mode.append(o)
                break
        else:
            modes.append([o])
    return modes


def _fmt_obs(o: Obs, mixed: bool) -> str:
    txt = f"{o[0]:.0f} / {o[1]:.0f}" + (f" (union {o[2]:.0f})" if mixed else "")
    return txt + (f" [{o[3]}]" if o[3] else "")


def _one_run_cell(preset: str, name: str, b: Obs, m: Obs, mixed: bool, tol: float, verdict: str) -> str:
    if mixed:
        delta = f"{_pct(m[2], b[2]) if b[2] else 0.0:+.1f} % (union)"
    else:
        delta = f"{_pct(m[0], b[0]):+.1f} / {_pct(m[1], b[1]):+.1f} %"
    return f"| {preset} | {name} | {_fmt_obs(b, mixed)} | {_fmt_obs(m, mixed)} | {delta} | {tol:.0f} % | {verdict} |"


def _by_mode_cell(preset: str, name: str, modes: List[List[Obs]], m_obs: List[Obs], nearest: List[Obs],
                  mixed: bool, tol: float, verdict: str) -> str:
    board = "; ".join(_fmt_obs(mode[0], mixed) + f" x{len(mode)}" for mode in modes)
    model = "; ".join(_fmt_obs(o, mixed) for o in m_obs)
    if mixed:
        delta = "; ".join(f"{_pct(m[2], mode[0][2]) if mode[0][2] else 0.0:+.1f}" for m, mode in zip(nearest, modes))
        delta += " % (union, by mode)"
    else:
        delta = "; ".join(f"{_pct(m[0], mode[0][0]):+.1f} / {_pct(m[1], mode[0][1]):+.1f}"
                          for m, mode in zip(nearest, modes)) + " % (by mode)"
    return f"| {preset} | {name} | {board} | {model} | {delta} | {tol:.0f} % | {verdict} |"


def _union_from_notes(notes: str) -> float:
    """The board CSV's `union NNN.N MB/s` for the mixed family."""
    import re
    m = re.search(r"union ([0-9.]+) MB/s", notes or "")
    return float(m.group(1)) if m else 0.0


# ---------------------------------------------------------------------------
# sweep: the pattern x variant table (MC-018 item 3)
# ---------------------------------------------------------------------------


def cmd_sweep(args: argparse.Namespace) -> int:
    configs = [CONFIGS[c] for c in args.configs]
    scenarios = SUITES[args.suite]
    if args.only:
        scenarios = [s for s in scenarios if s.name in set(args.only)]
    if args.txn:
        scenarios = [replace(s, txn_count=args.txn) for s in scenarios]
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    rows: Dict[Tuple[str, str], dict] = {}
    if args.resume and os.path.exists(args.out):
        with open(args.out, newline="") as f:
            for r in csv.DictReader(f):
                rows[(r["config"], r["scenario"])] = r
    with tempfile.TemporaryDirectory(prefix="char_model_") as tmp:
        total = len(configs) * len(scenarios)
        i = 0
        for cfg in configs:
            for sc in scenarios:
                i += 1
                if (cfg.name, sc.name) in rows:
                    continue
                print(f"[{i}/{total}] {cfg.name} {sc.name} ...", flush=True)
                row = run_scenario(cfg, sc, tmp)
                rows[(cfg.name, sc.name)] = row
                print(f"    wr {row['wr_bw_mb_s']} / rd {row['rd_bw_mb_s']} MB/s  rd_lat_max {row['rd_lat_max']} "
                      f"flips {row['dir_flips']} ({row['elapsed_s']} s)", flush=True)
                with open(args.out, "w", newline="") as f:
                    w = csv.DictWriter(f, fieldnames=CSV_FIELDS)
                    w.writeheader()
                    for r in rows.values():
                        w.writerow(r)
    print(f"wrote {args.out}")
    if args.table:
        write_sweep_table(rows, [c.name for c in configs], scenarios, args.table, base=args.base)
        print(f"wrote {args.table}")
    return 0


def _row_cells(r: dict) -> Tuple[float, float, float]:
    """(write MB/s, read MB/s, the window's union MB/s for two-direction rows else the max)."""
    w, rd = float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"])
    if r["family"] in ("mixed", "rw_mix", "trace") and int(r["wr_cycles"]) and int(r["rd_cycles"]):
        bytes_total = float(r["bytes_moved"]) * (2 if r["family"] == "mixed" else 1)
        return w, rd, bytes_total / max(int(r["wr_cycles"]), int(r["rd_cycles"])) * MC_CLK_MHZ
    return w, rd, max(w, rd)


def write_sweep_table(rows: Dict[Tuple[str, str], dict], configs: List[str], scenarios: List[Scenario],
                      path: str, *, base: str = "granite_sku100") -> None:
    """pattern x variant: MB/s (write / read, union for two-direction rows) and the worst read wait, each
    variant's delta against the base column."""
    lines = [f"# Pattern x variant on the SKU model (base `{base}`)", "",
             "Each cell: write / read MB/s (two-direction rows add the union over the longer window) and, on the",
             "second line, the delta of the headline number against the base column with the worst read wait in",
             "MC cycles. Headline = the union for two-direction rows, else the larger direction.", ""]
    for c in configs:
        lines.append(f"- `{c}`: {CONFIGS[c].note}")
    lines += ["", "| pattern | " + " | ".join(configs) + " |", "|---|" + "---|" * len(configs)]
    for sc in scenarios:
        cells = []
        b = rows.get((base, sc.name))
        bh = _row_cells(b)[2] if b else 0.0
        for c in configs:
            r = rows.get((c, sc.name))
            if not r:
                cells.append("-")
                continue
            w, rd, head = _row_cells(r)
            txt = f"{w:.0f} / {rd:.0f}" + (f" (u {head:.0f})" if r["family"] in ("mixed", "rw_mix") else "")
            if b and c != base and bh:
                txt += f"<br>{_pct(head, bh):+.1f} %"
            if r.get("rd_lat_max", "") != "":
                txt += f"<br>wait {float(r['rd_lat_max']):.0f}"
            cells.append(txt)
        lines.append(f"| {sc.name} | " + " | ".join(cells) + " |")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="run a suite through one model configuration, write a CSV")
    r.add_argument("--config", choices=sorted(CONFIGS), default="open32")
    r.add_argument("--suite", choices=sorted(SUITES), default="all")
    r.add_argument("--only", nargs="*", help="scenario names to run (default all in the suite)")
    r.add_argument("--scale", type=float, default=1.0, help="multiply every txn_count (1.0 = the board's counts)")
    r.add_argument("--txn", type=int, default=0, help="set every txn_count (e.g. a sim's TEST_TXN); wins over --scale")
    r.add_argument("--out", required=True)
    r.set_defaults(func=cmd_run)
    t = sub.add_parser("run-trace", help="run CAPTURED TimedLoadStoreTrace file(s) through one model configuration")
    t.add_argument("--config", choices=sorted(CONFIGS), default="open32")
    t.add_argument("--name", required=True, help="the scenario name for the CSV row")
    t.add_argument("--wr", help="write-pass trace (with --rd)")
    t.add_argument("--rd", help="read-pass trace (with --wr)")
    t.add_argument("--both", help="one trace carrying both directions (the mixed family)")
    t.add_argument("--split", action="store_true",
                   help="with --both: offer the two directions as independent streams (split_directions)")
    t.add_argument("--out", required=True, help="CSV to append to (created with a header if absent)")
    t.add_argument("--overwrite", action="store_true", help="start the CSV afresh")
    t.set_defaults(func=cmd_run_trace)
    c = sub.add_parser("compare", help="model CSV(s) beside measured granite / LiteDRAM CSVs as markdown")
    c.add_argument("--model", nargs="+", required=True)
    c.add_argument("--measured", required=True, help="the char_results directory")
    c.add_argument("--granite", required=True, help="<point>_<date>, e.g. sku100_2026-11-09")
    c.add_argument("--litedram", default="", help="<point>_<date>, e.g. hx100_2026-10-31")
    c.add_argument("--out", default="")
    c.set_defaults(func=cmd_compare)
    bc = sub.add_parser("board-compare", help="the SKU model CSV(s) beside a board CSV set, cell by cell, with tolerances")
    bc.add_argument("--model", nargs="+", required=True)
    bc.add_argument("--measured", required=True, help="the char_results directory")
    bc.add_argument("--granite", required=True, help="<point>_<date>, e.g. sku100def_2026-11-16")
    bc.add_argument("--board-also", nargs="*", default=[],
                    help="more board CSVs of the same point (reruns); a cell with several runs is read by mode")
    bc.add_argument("--out", default="")
    bc.add_argument("--strict", action="store_true", help="exit 1 when any cell is out of tolerance")
    bc.set_defaults(func=cmd_board_compare)
    sw = sub.add_parser("sweep", help="run several configs over a suite; one CSV, optionally the pattern x variant table")
    sw.add_argument("--configs", nargs="+", required=True, help="config names (see run --config)")
    sw.add_argument("--suite", choices=sorted(SUITES), default="everything")
    sw.add_argument("--only", nargs="*")
    sw.add_argument("--txn", type=int, default=0)
    sw.add_argument("--out", required=True, help="the CSV (rewritten after every cell; --resume skips cells it has)")
    sw.add_argument("--resume", action="store_true")
    sw.add_argument("--table", default="", help="write the pattern x variant markdown table here")
    sw.add_argument("--base", default="granite_sku100", help="the column the deltas are against")
    sw.set_defaults(func=cmd_sweep)
    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
