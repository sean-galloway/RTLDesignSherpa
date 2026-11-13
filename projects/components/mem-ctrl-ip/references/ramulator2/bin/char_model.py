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
"""
from __future__ import annotations

import argparse
import csv
import os
import sys
import tempfile
import time
from dataclasses import dataclass, field, replace
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

    @property
    def burst_bytes(self) -> int:
        return self.burst_len * GEOM.beat_bytes


EVERY = [
    Scenario(f"{fam}_bl{bl}", fam, burst_len=bl)
    for fam in ("incremental", "row_major", "col_major", "col_major_interleaved")
    for bl in (4, 8, 16)
]
WINDOWS = [
    Scenario("mixed_bl8", "mixed", burst_len=8, txn_count=32000, threads=WINDOW_GENS),
    Scenario("row_thrash_bl8", "row_thrash", burst_len=8, txn_count=32000, threads=WINDOW_GENS),
    Scenario("random_bl8", "random", burst_len=8, txn_count=32000, threads=WINDOW_GENS),
]
SUITES = {"every": EVERY, "windows": WINDOWS, "all": EVERY + WINDOWS}


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
        def region(r: int) -> List[List[int]]:
            out = []
            for bank, rowgrp in layout:
                row = rowgrp + r * REGION_ROWS
                start = bank * GEOM.bank_stride + row * GEOM.row_stride_same_bank
                out.append(list(_walk(start, bb, GEOM.page_bytes - 1, n)))
            return out
        return region(0), region(1)
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


def write_trace(path: str, streams: Iterable[Iterator[Tuple[str, int]]]) -> int:
    """One request per tick; several streams (write + read for `mixed`) are
    interleaved beat by beat. Returns the request count."""
    n = 0
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
                f.write(f"{tick} {op} {addr}\n")
                tick += 1
                n += 1
                nxt.append(it)
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
    mc_granular: bool = False          # round every constraint up to 2 CK (the RTL's MC-cycle counters)
    wr_low_wm: float = 0.2             # GenericDDR write-drain hysteresis, fractions of the write queue:
    wr_high_wm: float = 0.8            #   drain writes above high (or when no read waits), back to reads below low
    scatter_interval: int = 0          # AllBank refresh: stagger the scope nodes by this many cycles (0 = all at once)
    ref_burst: int = 1                 # n > 1: n REFs issued back to back every n tREFI (nRFC and nREFI both x n), the
                                       #   JEDEC postpone / pull-in credit (DDR2: up to 8) spent as one burst
    note: str = ""


CONFIGS = {
    # the ideal FR-FCFS open-page controller with Ramulator's default queues
    "open32": ModelConfig("open32", note="FR-FCFS, open page, 32-deep read and write queues, AllBank refresh"),
    # queues the depth of granite's storage-lite seam (GRANITE_SEAM_N = 8 per direction)
    "open8": ModelConfig("open8", read_buffer=8, write_buffer=8,
                         note="as open32 with 8-deep queues (granite's seam depth)"),
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


def build_sim(cfg: ModelConfig, trace_path: str, *, bl8: bool = False):
    import ramulator  # noqa: WPS433  (vendor module)

    dram_cls = ramulator.dram.DDR2_BL8 if bl8 else ramulator.dram.DDR2
    if cfg.mc_granular:
        dram_cls = _mc_granular_class(dram_cls)
    if cfg.ref_burst > 1:
        dram_cls = _ref_burst_class(dram_cls, cfg.ref_burst)
    dram = dram_cls(org_preset=cfg.org_preset, timing_preset=cfg.timing_preset)
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
        scheduler = ramulator.scheduler.BankFIFORR(column_first=cfg.column_first)
    else:
        scheduler = {"FRFCFS": ramulator.scheduler.FRFCFS,
                     "FRFCFS-RowHit": ramulator.scheduler.FRFCFSRowHit}[cfg.scheduler]()
    ctrl = ramulator.controller.GenericDDR(
        dram=dram, scheduler=scheduler, refresh_manager=refresh, row_policy=row_policy,
        addr_mapper=ramulator.addr_mapper.RoBaRaCoCh(),
        read_buffer_size=cfg.read_buffer, write_buffer_size=cfg.write_buffer,
        wr_low_watermark=cfg.wr_low_wm, wr_high_watermark=cfg.wr_high_wm,
    )
    # frontend = the MC clock (one AXI beat per tick), memory system = CK at 2x
    frontend = ramulator.frontend.TimedLoadStoreTrace(clock_ratio=1, path=trace_path)
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
    "wr_coalesced", "rd_forwarded", "wr_stall_ticks", "rd_stall_ticks", "elapsed_s", "notes",
]


def _window(fe: dict, kind: str) -> int:
    first, last = fe[f"{kind}_first_send_tick"], fe[f"{kind}_last_complete_tick"]
    return max(int(last) - int(first), 0)


def _bw(bytes_moved: int, cycles: int) -> float:
    return round(bytes_moved / cycles * MC_CLK_MHZ, 2) if cycles else 0.0


def run_pass(cfg: ModelConfig, trace_path: str) -> Tuple[dict, dict]:
    sim = build_sim(cfg, trace_path)
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
                wr_stall_ticks=fe["stall_ticks"], rd_stall_ticks=fe["stall_ticks"])


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
                wr_stall_ticks=wfe["stall_ticks"], rd_stall_ticks=rfe["stall_ticks"])


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
                    both: Optional[str] = None) -> dict:
    """One CSV row from CAPTURED traces (MC-013 item 5): either a write trace and a read trace run as two
    passes, or one trace carrying both directions. The bandwidth definition is unchanged: bytes the trace
    moves per direction over that direction's first-send to last-complete window."""
    t0 = time.time()
    row = dict(config=cfg.name, scenario=name, family="trace", burst_len=0, threads=0, clk_mhz=MC_CLK_MHZ)
    if both:
        wb, rb = trace_bytes(both)
        fe, c = run_pass(cfg, both)
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
    if sc.family == "mixed":
        path = os.path.join(tmpdir, f"{sc.name}.trace")
        write_trace(path, [interleave_bursts(w_walks, sc.burst_len, "ST"),
                           interleave_bursts(r_walks, sc.burst_len, "LD")])
        fe, c = run_pass(cfg, path)
        row.update(_both_dirs_row(fe, c))
        notes.append(f"{sc.threads} writers + {sc.threads} readers from one GO, union "
                     f"{_bw(2 * per_dir_bytes, fe['cycles'])} MB/s over {fe['cycles']} cycles")
    else:
        wpath = os.path.join(tmpdir, f"{sc.name}_wr.trace")
        rpath = os.path.join(tmpdir, f"{sc.name}_rd.trace")
        write_trace(wpath, [interleave_bursts(w_walks, sc.burst_len, "ST")])
        write_trace(rpath, [interleave_bursts(r_walks, sc.burst_len, "LD")])
        row.update(_two_pass_row(run_pass(cfg, wpath), run_pass(cfg, rpath)))
    row["wr_bw_mb_s"] = _bw(per_dir_bytes, row["wr_cycles"])
    row["rd_bw_mb_s"] = _bw(per_dir_bytes, row["rd_cycles"])
    if row["wr_coalesced"] or row["rd_forwarded"]:
        notes.append(f"controller coalesced {row['wr_coalesced']} writes / forwarded "
                     f"{row['rd_forwarded']} reads (the board does neither)")
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
            print(f"    wr {row['wr_bw_mb_s']} / rd {row['rd_bw_mb_s']} MB/s  "
                  f"(rd hits/miss/conf {row['rd_row_hits']}/{row['rd_row_misses']}/{row['rd_row_conflicts']}, "
                  f"{row['elapsed_s']} s)", flush=True)
    print(f"wrote {args.out}")
    return 0


def cmd_run_trace(args: argparse.Namespace) -> int:
    cfg = CONFIGS[args.config]
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    print(f"{cfg.name} {args.name} ...", flush=True)
    row = run_trace_files(cfg, args.name, wr=args.wr, rd=args.rd, both=args.both)
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
    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
