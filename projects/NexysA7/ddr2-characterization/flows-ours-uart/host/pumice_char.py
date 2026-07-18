#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice_char.py -- DDR2/LPDDR2 memory-controller performance characterization.

Access-pattern + mode sweep built on the discrete AXI4 perf collateral the
ddr2-char harness already taps off the controller's AXI port (mirrors the
STREAM characterization host flow, stream_ext_char.py):

  * axi_bus_meter         -> per-cycle {productive, backpressure, starvation,
                             idle} on the R and W data channels
  * axi_perf_latency_hist -> per-transaction log2 latency histogram
                             (AR->firstR and AR->RLAST for reads; AW->B writes)

read back BY NAME through DDR2CharDriver.perf_meters() / perf_hist_dump().

The loop is: program a workload -> clear + un-freeze the perf window -> run ->
FREEZE the window (critical: the meters keep counting during the slow UART
read-back, so a run that reads counters un-frozen inflates `idle` by thousands
of cycles) -> read counters -> derive metrics.

Three access-pattern families, each mapped onto the DDR2 page/bank geometry so
they exercise DISTINCT controller behaviours. The default ROW_MAJOR scheme maps
a byte address as  word = addr >> BYTE_OFFSET ;  col = word[COL_W-1:0] ;
bank = word[COL_W +: BANK_W] ; row = word[COL_W+BANK_W +: ROW_W]  -- so the bank
field sits just above the column and a full page is contiguous:

  incremental           contiguous linear march (stride = one burst). Streams
                        across columns, then banks, then rows. Best-case
                        sequential baseline.
  row_major             march bounded to a single DRAM page (wrap_mask = page-1)
                        so EVERY burst is a guaranteed page HIT. Isolates
                        same-row back-to-back column throughput (no ACT/PRE
                        after the first activate).
  col_major             stride = one row in the SAME bank, so EVERY burst is a
                        guaranteed page MISS (PRE + ACT each time). The classic
                        column-major traversal of a row-major matrix -- worst
                        case, exposes tRC / tRP / tRAS.
  col_major_interleaved stride = one bank instead of one row, so successive
                        bursts hop banks and their activates PIPELINE. The delta
                        vs col_major reveals the controller's bank-level
                        parallelism.

The two headline "perf issue" signals the summary flags:
  * incremental_BW / col_major_BW           -> the page-management penalty
  * col_major_interleaved_BW / col_major_BW -> bank-level parallelism recovered

IMPORTANT -- single address dimension. The harness pattern generator walks ONE
dma_address_gen dimension (index_0; index_1 / stride_1 are held at 0 in a single
instance, see axi4_master_wr_pattern_gen.sv). So all families are expressed
through stride_0 + wrap_mask_0 + burst_len, NOT a nested 2D loop.

Sim vs board. Over the DFI-loopback sim there is no a7ddrphy and no DDR2 page
timing modelled, so the families move identical data in identical time -- the
sim validates the *mechanism* (program / run / read-back / integrity), the board
reveals the *timing* separation. See test_ddr2_char_char.py (sim regression) and
the board CLI (pumice_master.py --char).
"""

from __future__ import annotations

import csv as _csv
import io
import sys
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

import ddr2_char as dc
from ddr2_char import DDR2CharDriver

# wait-on-one-engine helper (write-then-read is phased). Imported from the
# master program so there is exactly one implementation; pumice_master imports
# this module lazily (in main), so there is no import cycle.
from pumice_master import wait_engine


# =============================================================================
# DRAM geometry (byte-address space, ROW_MAJOR scheme)
# =============================================================================
@dataclass(frozen=True)
class Geometry:
    """DDR2 geometry as seen from the AXI byte address, for the ROW_MAJOR
    address-map scheme (the controller's power-on default).

    Defaults match the Nexys A7 board build: MT47H64M16 (1Gb x16), COL_WIDTH=10,
    NUM_BANKS=8, and the x16 device-word column granularity (BYTE_OFFSET_WIDTH =
    log2(DRAM_DEVICE_WIDTH/8) = log2(2) = 1). That yields a 2 KB page. Override
    for a different build; the sweep also *discovers* the real boundaries from
    the bandwidth cliffs, so exact values only sharpen the default strides.
    """
    col_width:     int = 10
    bank_width:    int = 3          # log2(NUM_BANKS=8)
    row_width:     int = 13
    byte_offset:   int = 1          # log2(device bytes); x16 -> 1
    beat_bytes:    int = 8          # AXI data bus = 64b -> 8 bytes/beat (axi_size=3)

    @property
    def page_bytes(self) -> int:
        """Contiguous span within one open (bank, row) page."""
        return (1 << self.col_width) << self.byte_offset

    @property
    def bank_stride(self) -> int:
        """Address delta that advances the bank field by one (ROW_MAJOR: the
        bank sits just above the column, so this equals one page)."""
        return self.page_bytes

    @property
    def row_stride_same_bank(self) -> int:
        """Address delta to the same column of the NEXT row in the SAME bank
        (must skip past all banks) -> page miss on every step."""
        return self.page_bytes << self.bank_width


DEFAULT_GEOM = Geometry()


def _stable_seed(name: str) -> int:
    """Deterministic 32-bit seed from a scenario name (FNV-1a). Python's
    built-in hash() is per-process randomized, which would make runs
    non-reproducible; this keeps the LFSR/hash pattern stable across runs."""
    h = 0x811C_9DC5
    for ch in name.encode():
        h = ((h ^ ch) * 0x0100_0193) & 0xFFFF_FFFF
    return h or 0x1EAF_F00D          # never all-zero (LFSR/seed guard)

# Access-pattern families.
FAM_INCREMENTAL   = "incremental"
FAM_ROW_MAJOR     = "row_major"
FAM_COL_MAJOR     = "col_major"
FAM_COL_INTERLEAVE = "col_major_interleaved"
FAMILIES = (FAM_INCREMENTAL, FAM_ROW_MAJOR, FAM_COL_MAJOR, FAM_COL_INTERLEAVE)

# Hardware limit: the harness engine's txn_count CSR field is 16-bit
# (WR_BLEN_TXN txn[23:8]). Base suite counts are kept small so a board soak can
# multiply them ~1000x and still fit; a scale that would exceed this is clamped
# (with a note) rather than silently truncated.
TXN_MAX = 0xFFFF


# =============================================================================
# Scenario + result records
# =============================================================================
@dataclass(frozen=True)
class Scenario:
    """One generator setup: an access-pattern family plus generator-side knobs.

    Controller-side knobs (paging scheme, page policy, reorder/OOO, refresh)
    live on ControllerConfig and are crossed against these scenarios by
    run_matrix -- so every generator setup is exercised under every config.
    id_mode stays here because it is how the pattern gen forms AW/AR ids
    (FIXED = single id; LFSR = multi-id traffic); whether the controller then
    returns/schedules those out of order is the config's rd_in_order /
    force_inorder / lookahead.
    """
    name:      str
    family:    str
    burst_len: int = 8
    txn_count: int = 256
    gap:       int = 0
    id_mode:   int = dc.ID_MODE_FIXED       # FIXED single-id; LFSR multi-id
    axi_size:  int = dc.AXI_SIZE_8

    def burst_bytes(self, geom: Geometry) -> int:
        return self.burst_len * (1 << self.axi_size)


# =============================================================================
# Controller configuration axis (paging / scheduling / refresh)
# =============================================================================
# Sentinel: request the deepest reorder window; apply() clamps to the build's
# SCHED_TUNING.lookahead_max_obs read from the device.
LOOKAHEAD_MAX = 0xF


@dataclass(frozen=True)
class ControllerConfig:
    """A named preset of the controller's runtime perf knobs (pumice CSRs).

    None = leave at the build-time default. Changing any of these between runs
    is integrity-safe (write and read decode a given address identically), so
    the same data round-trips under every config -- only the *timing* changes.
    """
    name:          str
    scheme:        Optional[int] = None     # dc.SCHEME_* (paging)
    page_policy:   Optional[int] = None     # dc.PAGE_POLICY_*
    lookahead:     Optional[int] = None     # reorder-window depth (0=off)
    force_inorder: Optional[bool] = None    # 1 = FIFO-only (no row-hit reorder)
    happy_enable:  Optional[bool] = None    # HAPPY page predictor
    rd_in_order:   bool = True              # R-channel return ordering (harness cfg)
    t_refi:        Optional[int] = None      # refresh interval (MC cycles)
    # Board (always-on pre-pull / a7ddrphy write_latency=0): t_phy_wrlat MUST be
    # 0 so write data is presented concurrent with the WR command. The old
    # default 4 clobbered the leveling-time value every scenario -> writes land
    # wrong -> every read mismatches (0/N integrity). See pumice_master.py.
    t_phy_wrlat:   int = 0
    t_rddata_en:   int = 6

    def apply(self, drv: DDR2CharDriver) -> None:
        # rd_in_order + the DFI latencies live on the harness CTRLR_CFG (one
        # non-rmw write, so always send the known-good latencies with it).
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=self.t_phy_wrlat,
                               t_rddata_en=self.t_rddata_en,
                               rd_in_order=self.rd_in_order)
        if self.scheme is not None:
            drv.set_addr_map_scheme(self.scheme)
        if self.page_policy is not None:
            drv.set_page_policy(self.page_policy)
        if self.t_refi is not None:
            drv.set_refresh_interval(self.t_refi)
        sched: Dict[str, object] = {}
        if self.lookahead is not None:
            la = self.lookahead
            if la > 0:
                la = min(la, drv.get_lookahead_max())    # HW-clamp to build max
            sched["lookahead"] = la
        if self.force_inorder is not None:
            sched["force_inorder"] = self.force_inorder
        if self.happy_enable is not None:
            sched["happy_enable"] = self.happy_enable
        if sched:
            drv.set_scheduler(**sched)


# Presets -- each changes ONE main lever from `baseline` (except `reorder` /
# `happy_hybrid`, the combined high-performance configs, and the *_refresh pair
# which stress refresh bandwidth). XOR_HASH is omitted (not synthesized).
CONFIGS: Dict[str, ControllerConfig] = {
    "baseline": ControllerConfig(
        "baseline", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_CLOSE,
        lookahead=0, force_inorder=False, rd_in_order=True),
    "bank_interleave": ControllerConfig(
        "bank_interleave", scheme=dc.SCHEME_BANK_INTERLEAVE,
        page_policy=dc.PAGE_POLICY_CLOSE, lookahead=0, force_inorder=False,
        rd_in_order=True),
    "open_page": ControllerConfig(
        "open_page", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_OPEN,
        lookahead=0, force_inorder=False, rd_in_order=True),
    "inorder": ControllerConfig(
        "inorder", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_CLOSE,
        lookahead=0, force_inorder=True, rd_in_order=True),
    "reorder": ControllerConfig(
        "reorder", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_OPEN,
        lookahead=LOOKAHEAD_MAX, force_inorder=False, rd_in_order=False),
    "happy_hybrid": ControllerConfig(
        "happy_hybrid", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_HYBRID, happy_enable=True,
        lookahead=LOOKAHEAD_MAX, force_inorder=False, rd_in_order=False),
    "fast_refresh": ControllerConfig(
        "fast_refresh", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_CLOSE, t_refi=0x0100, rd_in_order=True),
    "slow_refresh": ControllerConfig(
        "slow_refresh", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_CLOSE, t_refi=0x7FFF, rd_in_order=True),
}
BASELINE = CONFIGS["baseline"]
# The default matrix isolates the main levers (scheme, page policy, reorder).
DEFAULT_MATRIX = ["baseline", "bank_interleave", "open_page", "inorder", "reorder"]


def resolve_configs(spec) -> List[ControllerConfig]:
    """Resolve a config spec to ControllerConfig objects.

    spec may be: a list of names/objects, or a string -- "matrix" (the default
    isolating set), "all" (every preset), or a comma-separated name list.
    """
    if isinstance(spec, str):
        if spec == "matrix":
            names = list(DEFAULT_MATRIX)
        elif spec == "all":
            names = list(CONFIGS)
        else:
            names = [s.strip() for s in spec.split(",") if s.strip()]
    else:
        names = list(spec)
    out: List[ControllerConfig] = []
    for n in names:
        if isinstance(n, ControllerConfig):
            out.append(n)
        elif n in CONFIGS:
            out.append(CONFIGS[n])
        else:
            raise ValueError(f"unknown controller config {n!r}; "
                             f"available: {sorted(CONFIGS)}")
    return out


@dataclass(frozen=True)
class Meter:
    """Immutable snapshot of one axi_bus_meter (R or W data channel)."""
    prod:  int
    bp:    int
    starv: int
    idle:  int

    @property
    def total(self) -> int:
        return self.prod + self.bp + self.starv + self.idle

    @property
    def util(self) -> float:
        return (self.prod / self.total) if self.total else 0.0


@dataclass(frozen=True)
class CharRecord:
    """Full result for one (config, Scenario) point -- W+R phases + metrics."""
    scenario:   Scenario
    config:     str                  # ControllerConfig.name it ran under
    ok:         bool
    mismatched: int
    # write phase
    wr_cycles:  int
    wr_meter:   Meter
    # read phase
    rd_cycles:  int
    rd_meter:   Meter
    rd_hist:    Tuple[int, ...]      # 16-bin log2 histogram, AR->firstR
    rd_hist_total: int
    # context
    bytes_moved: int                 # per phase (wr == rd == txn*blen*beat)
    clk_mhz:     float
    notes:       Tuple[str, ...] = ()

    # ---- derived bandwidth / latency ------------------------------------
    @staticmethod
    def _bw_mb_s(bytes_moved: int, cycles: int, clk_mhz: float) -> float:
        if cycles <= 0:
            return 0.0
        # bytes/cycle * cycles/s  (clk_mhz*1e6)  -> bytes/s  -> /1e6 = MB/s
        return (bytes_moved / cycles) * clk_mhz

    @property
    def wr_bw_mb_s(self) -> float:
        return self._bw_mb_s(self.bytes_moved, self.wr_cycles, self.clk_mhz)

    @property
    def rd_bw_mb_s(self) -> float:
        return self._bw_mb_s(self.bytes_moved, self.rd_cycles, self.clk_mhz)

    @property
    def rd_bytes_per_cycle(self) -> float:
        return (self.bytes_moved / self.rd_cycles) if self.rd_cycles else 0.0

    @property
    def util_reliable(self) -> bool:
        """True when the bus-meter window (bucket sum) is close to the measured
        run (hardware timer cycles), so utilization reflects the WORKLOAD rather
        than host UART observation latency (the start command + status polls
        elapse while the free-running meter counts). False for tiny runs -- use
        --char-scale ~1000 on the board. Bandwidth (timer-based) stays reliable
        regardless."""
        rd_ratio = self.rd_meter.total / max(self.rd_cycles, 1)
        wr_ratio = self.wr_meter.total / max(self.wr_cycles, 1)
        return max(rd_ratio, wr_ratio) <= 2.0

    @property
    def rd_avg_latency_cyc(self) -> float:
        """Mean AR->firstR latency (cycles) from the log2 histogram. Bin b
        counts [2^b, 2^(b+1)); use the geometric-ish midpoint 1.5*2^b (bin 0
        counts latencies <=1 -> weight 1)."""
        if self.rd_hist_total <= 0:
            return 0.0
        acc = 0.0
        for b, cnt in enumerate(self.rd_hist):
            mid = 1.0 if b == 0 else 1.5 * (1 << b)
            acc += cnt * mid
        return acc / self.rd_hist_total


# =============================================================================
# Stride/wrap mapping -- the heart of the three families
# =============================================================================
def strides_for(sc: Scenario, geom: Geometry) -> Tuple[int, int]:
    """Return (stride_0, wrap_mask_0) for a scenario given the DRAM geometry.

    index_1 is inert in the harness pattern-gen, so this single (stride, wrap)
    pair fully defines the address walk: addr[i] = base + (i*stride & wrap-or-all).
    """
    bb = sc.burst_bytes(geom)
    if sc.family == FAM_INCREMENTAL:
        # Contiguous march across the whole address space.
        return bb, 0
    if sc.family == FAM_ROW_MAJOR:
        # Contiguous, but wrapped inside one page -> every burst a page HIT.
        return bb, geom.page_bytes - 1
    if sc.family == FAM_COL_MAJOR:
        # One row in the SAME bank per burst -> page MISS every burst.
        return geom.row_stride_same_bank, 0
    if sc.family == FAM_COL_INTERLEAVE:
        # One bank per burst -> activates pipeline across banks.
        return geom.bank_stride, 0
    raise ValueError(f"unknown access family: {sc.family!r}")


# =============================================================================
# Measurement
# =============================================================================
def _read_meter(drv: DDR2CharDriver, which: str) -> Meter:
    m = drv.perf_meters()[which]
    return Meter(prod=m.prod, bp=m.bp, starv=m.starv, idle=m.idle)


def measure(drv: DDR2CharDriver, sc: Scenario, *,
            cfg: ControllerConfig = BASELINE, geom: Geometry = DEFAULT_GEOM,
            base_addr: int = 0x0, clk_mhz: float = 100.0,
            timeout_s: float = 20.0) -> CharRecord:
    """Run one (config, scenario) point (write phase then read phase) + perf.

    The controller `cfg` is applied first, then the generator is programmed for
    the scenario. Data integrity uses the address-hashed data mode (data =
    f(byte_addr, seeds)): OOO-safe, so multi-id (id_mode=LFSR) and
    wrapped/overlapping address walks (row_major) still validate per-beat --
    overlapping writes store identical f(addr) values, so the read of any
    address gets its expected value regardless of write/return order.
    """
    stride, wrap = strides_for(sc, geom)
    seed = _stable_seed(sc.name)
    beat_bytes = 1 << sc.axi_size
    bytes_moved = sc.txn_count * sc.burst_len * beat_bytes
    notes: List[str] = []

    prog = dict(start_addr=base_addr, burst_len=sc.burst_len,
                txn_count=sc.txn_count, stride_0=stride, wrap_mask_0=wrap,
                gap=sc.gap, id_mode=sc.id_mode, axi_size=sc.axi_size,
                data_mode=True, lfsr_seed=seed, hash_seed0=seed,
                hash_seed1=seed ^ 0x9E37_79B9, hash_seed2=seed ^ 0x85EB_CA6B)

    cfg.apply(drv)                          # paging / scheduling / refresh

    # Meter window discipline: the bus meter is a free-running counter, and
    # programming an engine is a dozen UART register writes (thousands of sim
    # cycles each) during which the AXI bus is idle. So keep the meter FROZEN
    # while programming, then clear + unfreeze immediately before start -- the
    # window is (start .. done) plus only the one start-command's transport
    # latency, not the whole programming sequence. (Clearing before programming
    # counted that idle as starvation and made util meaningless.)

    # ---- write phase ----
    drv.freeze_trace(True)                  # no counting during programming
    drv.program_wr_engine(**prog)
    drv.clear_stats()                       # zero buckets + errors AFTER program
    drv.timer_clear()
    drv.freeze_trace(False)                 # start counting
    drv.start_wr()
    wr_ok = wait_engine(drv, "wr", timeout_s=timeout_s)
    drv.freeze_trace(True)                  # stop meters BEFORE slow read-back
    # Window from the WRITE engine's own hardware stamps (w_last-w_first), NOT
    # timer.cycles: the harness timer only stops on wr_done AND rd_done, so in a
    # single-engine phase timer.cycles free-runs (or stops on a stale other-engine
    # done). The per-engine stamps are latched at this engine's start/done and are
    # immune to that. See ddr2_char_harness.sv timer block.
    _tw = drv.timer()
    wr_cycles = max(_tw.w_last - _tw.w_first, 0)
    wr_meter = _read_meter(drv, "wr")

    # ---- read phase ----
    drv.program_rd_engine(**prog)           # (still frozen from above)
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    drv.start_rd()
    rd_ok = wait_engine(drv, "rd", timeout_s=timeout_s)
    drv.freeze_trace(True)
    _tr = drv.timer()                       # read window from r_last-r_first stamps
    rd_cycles = max(_tr.r_last - _tr.r_first, 0)
    rd_meter = _read_meter(drv, "rd")
    rd_hist, rd_total = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    drv.freeze_trace(False)                 # leave running for the next scenario

    mism = drv.beats_mismatched()
    ok = wr_ok and rd_ok and mism == 0
    if not wr_ok:
        notes.append("write engine did not complete")
    if not rd_ok:
        notes.append("read engine did not complete")
    if mism:
        notes.append(f"{mism} beats mismatched")
    if rd_total != sc.txn_count:
        notes.append(f"hist total {rd_total} != txn_count {sc.txn_count}")

    return CharRecord(
        scenario=sc, config=cfg.name, ok=ok, mismatched=mism,
        wr_cycles=wr_cycles, wr_meter=wr_meter,
        rd_cycles=rd_cycles, rd_meter=rd_meter,
        rd_hist=tuple(rd_hist), rd_hist_total=rd_total,
        bytes_moved=bytes_moved, clk_mhz=clk_mhz, notes=tuple(notes))


# =============================================================================
# Scenario suites (level-scaled, mirrors the repo TEST_LEVEL convention)
# =============================================================================
def build_suite(level: str = "medium", txn_scale: int = 1,
                families: Optional[Tuple[str, ...]] = None) -> List[Scenario]:
    """Build the scenario grid for a level, with an optional cycle multiplier.

    `families` restricts the access-pattern families (default: all four). A run
    profile uses this to define exactly which generator setups a run covers.

    basic  -- one burst_len (8), the 4 families: quick smoke (~8 phases).
    medium -- 4 families x burst_len {4, 8, 16} + an OOO (id LFSR) and a gapped
              variant of the col_major thrash case.
    full   -- medium plus the OOO variant applied to every family; the robust
              characterization pass.

    Run length (cycles) scales with txn_count. Base counts are deliberately
    SMALL (sim runs over a slow UART), so `txn_scale` multiplies every
    scenario's txn_count to make a real board soak. `txn_scale=1000` on the
    FPGA turns the quick sim-sized pass into a ~1000x-longer run for stable
    perf counters -- see run_suite / `pumice_master.py --char --char-scale`.
    The result is clamped to the 16-bit engine limit (TXN_MAX) with a stderr
    note if it would overflow.
    """
    level = level.lower()
    if level not in ("basic", "medium", "full"):
        raise ValueError(f"level must be basic|medium|full, got {level!r}")
    if txn_scale < 1:
        raise ValueError(f"txn_scale must be >= 1, got {txn_scale}")

    base = {"basic": 8, "medium": 64, "full": 64}[level]
    txn = base * txn_scale
    if txn > TXN_MAX:
        print(f"[char] txn_count {txn} exceeds 16-bit engine limit {TXN_MAX}; "
              f"clamping (raise burst_len or run --char repeatedly for more "
              f"cycles)", file=sys.stderr)
        txn = TXN_MAX
    blens = {"basic": (8,), "medium": (4, 8, 16), "full": (4, 8, 16)}[level]
    fams = tuple(families) if families else FAMILIES

    suite: List[Scenario] = []
    for fam in fams:
        for bl in blens:
            suite.append(Scenario(name=f"{fam}_bl{bl}", family=fam,
                                   burst_len=bl, txn_count=txn))

    # Generator-side stress variants. Multi-id (id_mode=LFSR) creates the
    # out-of-order-capable traffic; whether it is actually reordered is the
    # controller config's job (rd_in_order / force_inorder / lookahead), so the
    # matrix cross of these against the `reorder`/`inorder` configs is what
    # exercises OOO. The gap variant probes idle-recovery. (Only added when
    # their family is in scope.)
    if level in ("medium", "full") and FAM_COL_MAJOR in fams:
        suite.append(Scenario(name="col_major_bl8_multiid", family=FAM_COL_MAJOR,
                              burst_len=8, txn_count=txn,
                              id_mode=dc.ID_MODE_LFSR))
        suite.append(Scenario(name="col_major_bl8_gap", family=FAM_COL_MAJOR,
                              burst_len=8, txn_count=txn, gap=8))
    if level == "full":
        for fam in fams:
            suite.append(Scenario(name=f"{fam}_bl8_multiid", family=fam,
                                  burst_len=8, txn_count=txn,
                                  id_mode=dc.ID_MODE_LFSR))

    return suite


def run_matrix(drv: DDR2CharDriver, *, configs=None, level: str = "medium",
               txn_scale: int = 1, families: Optional[Tuple[str, ...]] = None,
               base_addr: int = 0x0, timeout_s: float = 20.0,
               geom: Geometry = DEFAULT_GEOM, clk_mhz: float = 100.0,
               progress: Optional[Callable[[str, int, int], None]] = None,
               ) -> List[CharRecord]:
    """Run the scenario suite under EACH controller config -- the full
    (config x generator) matrix. Returns a flat list, each record tagged with
    its config name. `configs` may be a spec string ("matrix"/"all"/comma
    names) or a list; defaults to just the baseline (single config). `families`
    restricts the access patterns (default: all four).

    `txn_scale` multiplies every scenario's workload (cycles): 1 for a quick
    sim-sized pass, ~1000 for a long FPGA soak (see build_suite)."""
    cfgs = resolve_configs(configs if configs is not None else [BASELINE])
    suite = build_suite(level, txn_scale=txn_scale, families=families)
    recs: List[CharRecord] = []
    total = len(cfgs) * len(suite)
    i = 0
    for cfg in cfgs:
        for sc in suite:
            i += 1
            if progress:
                progress(f"{cfg.name}/{sc.name}", i, total)
            recs.append(measure(drv, sc, cfg=cfg, geom=geom,
                               base_addr=base_addr, clk_mhz=clk_mhz,
                               timeout_s=timeout_s))
    return recs


def run_suite(drv: DDR2CharDriver, *, level: str = "medium", txn_scale: int = 1,
              base_addr: int = 0x0, geom: Geometry = DEFAULT_GEOM,
              clk_mhz: float = 100.0,
              progress: Optional[Callable[[str, int, int], None]] = None,
              ) -> List[CharRecord]:
    """Single-config (baseline) sweep -- run_matrix with just the baseline."""
    return run_matrix(drv, configs=[BASELINE], level=level, txn_scale=txn_scale,
                      base_addr=base_addr, geom=geom, clk_mhz=clk_mhz,
                      progress=progress)


# =============================================================================
# Run profiles -- the SINGLE source of truth for what a "run" is.
# =============================================================================
# A profile names one (controller-configs x generator-scenarios) matrix. Both
# the sim harness and the board CLI select a profile BY NAME and execute it via
# run_profile, so a given profile is the identical program on sim and FPGA --
# the ONLY difference is txn_scale (sim=1 for speed, ~1000 on the board for a
# long soak), exactly analogous to lowering the UART baud in sim. Add a profile
# here once; both targets pick it up.
RUN_PROFILES: Dict[str, dict] = {
    # Sim CI + quick board check: covers the config-apply path (scheme switch +
    # scheduler CSRs) and the best-case/worst-case access patterns. Small.
    "smoke": dict(configs=["baseline", "bank_interleave", "reorder"],
                  level="basic", families=(FAM_INCREMENTAL, FAM_COL_MAJOR)),
    # The isolating config matrix over the full family/burst grid.
    "matrix": dict(configs=DEFAULT_MATRIX, level="medium", families=None),
    # Everything: every preset (incl. refresh + happy) x the full grid.
    "full": dict(configs="all", level="full", families=None),
}


def run_profile(drv: DDR2CharDriver, profile: str = "smoke", *,
                txn_scale: int = 1, base_addr: int = 0x0, timeout_s: float = 20.0,
                geom: Geometry = DEFAULT_GEOM, clk_mhz: float = 100.0,
                progress: Optional[Callable[[str, int, int], None]] = None,
                ) -> List[CharRecord]:
    """Run a named RUN_PROFILES matrix. This is the entry both the sim test and
    the board CLI call, so `run_profile(drv, "smoke")` is the SAME program in
    both -- pass txn_scale=1 in sim, ~1000 on the FPGA."""
    if profile not in RUN_PROFILES:
        raise ValueError(f"unknown run profile {profile!r}; "
                         f"available: {sorted(RUN_PROFILES)}")
    p = RUN_PROFILES[profile]
    return run_matrix(drv, configs=p["configs"], level=p["level"],
                      families=p["families"], txn_scale=txn_scale,
                      base_addr=base_addr, timeout_s=timeout_s, geom=geom,
                      clk_mhz=clk_mhz, progress=progress)


# =============================================================================
# Reporting + issue detection
# =============================================================================
def _by_family_bl(recs: List[CharRecord]
                  ) -> Dict[Tuple[str, int], CharRecord]:
    """Index the plain (single-id, no-gap) scenarios of ONE config by
    (family, burst_len)."""
    out: Dict[Tuple[str, int], CharRecord] = {}
    for r in recs:
        sc = r.scenario
        if sc.id_mode == dc.ID_MODE_FIXED and sc.gap == 0:
            out[(sc.family, sc.burst_len)] = r
    return out


def _summarize_one_config(recs: List[CharRecord]) -> List[str]:
    """Per-config headline signals + issue flags (recs are all one config)."""
    lines: List[str] = []
    idx = _by_family_bl(recs)
    for bl in sorted({bl for (_f, bl) in idx}):
        inc = idx.get((FAM_INCREMENTAL, bl))
        rmj = idx.get((FAM_ROW_MAJOR, bl))
        cmj = idx.get((FAM_COL_MAJOR, bl))
        cil = idx.get((FAM_COL_INTERLEAVE, bl))
        if not (inc and cmj):
            continue
        inc_bw = inc.rd_bw_mb_s or 1e-9
        lines.append(f"  bl={bl:<3} rd BW  inc={inc.rd_bw_mb_s:8.1f}"
                     f"  row={rmj.rd_bw_mb_s if rmj else 0:8.1f}"
                     f"  col={cmj.rd_bw_mb_s:8.1f}"
                     f"  col_ilv={cil.rd_bw_mb_s if cil else 0:8.1f} MB/s"
                     f"  | page-penalty(col/inc)={cmj.rd_bw_mb_s / inc_bw:5.1%}"
                     + (f"  bank-recovery(ilv/col)="
                        f"{cil.rd_bw_mb_s / (cmj.rd_bw_mb_s or 1e-9):.2f}x"
                        if cil else ""))
        if cil and cil.rd_bw_mb_s <= cmj.rd_bw_mb_s * 1.10:
            lines.append(f"    [FLAG] bl{bl}: bank interleave gives no gain over "
                         "same-bank thrash -- activates not pipelined across banks")
        if cmj.rd_meter.total and cmj.rd_meter.starv > cmj.rd_meter.bp:
            lines.append(f"    [FLAG] bl{bl}: col_major STARVATION dominates "
                         f"({cmj.rd_meter.util:.1%} util) -- command-bound "
                         "(ACT/PRE), not data-bound")
    return lines


def _summarize_cross_config(recs: List[CharRecord]) -> List[str]:
    """Compare configs against baseline for the key access patterns -- the
    'which controller config mitigates the page thrash / does OOO help' view."""
    configs = sorted({r.config for r in recs})
    if len(configs) < 2:
        return []
    # Index (config, family, bl) for the plain scenarios.
    idx: Dict[Tuple[str, str, int], CharRecord] = {}
    for r in recs:
        sc = r.scenario
        if sc.id_mode == dc.ID_MODE_FIXED and sc.gap == 0:
            idx[(r.config, sc.family, sc.burst_len)] = r
    bls = sorted({sc.burst_len for r in recs for sc in [r.scenario]})
    bl = 8 if 8 in bls else (bls[len(bls) // 2] if bls else 0)

    lines = [f"cross-config read BW @ bl={bl} (MB/s; ratio vs baseline):"]
    base = "baseline" if "baseline" in configs else configs[0]
    for fam in FAMILIES:
        b = idx.get((base, fam, bl))
        if not b:
            continue
        b_bw = b.rd_bw_mb_s or 1e-9
        cells = []
        best_cfg, best_bw = base, b_bw
        for cfg in configs:
            r = idx.get((cfg, fam, bl))
            if not r:
                continue
            cells.append(f"{cfg}={r.rd_bw_mb_s:.0f}({r.rd_bw_mb_s / b_bw:.2f}x)")
            if r.rd_bw_mb_s > best_bw:
                best_cfg, best_bw = cfg, r.rd_bw_mb_s
        lines.append(f"  {fam:<22} " + "  ".join(cells))
        if best_cfg != base and best_bw > b_bw * 1.10:
            lines.append(f"      -> best: {best_cfg} ({best_bw / b_bw:.2f}x "
                         f"baseline) mitigates this pattern")
    return lines


def summarize(recs: List[CharRecord]) -> List[str]:
    """Headline perf signals + issue flags. Handles one or many configs."""
    lines: List[str] = []
    configs = sorted({r.config for r in recs})
    for cfg in configs:
        sub = [r for r in recs if r.config == cfg]
        lines.append(f"[config: {cfg}]")
        lines.extend(_summarize_one_config(sub))
    lines.extend(_summarize_cross_config(recs))
    if recs and not any(r.util_reliable for r in recs):
        lines.append("[NOTE] utilization is observation-latency-dominated at "
                     "this run size (meter window >> timer run) -- treat rd/wr "
                     "util as unreliable; bandwidth (timer-based) is fine. Raise "
                     "--char-scale (~1000 on the board) for meaningful util.")
    for r in recs:                                   # integrity/completion
        if not r.ok:
            lines.append(f"[FLAG] {r.config}/{r.scenario.name}: NOT OK -- "
                         + "; ".join(r.notes))
    return lines


def format_table(recs: List[CharRecord]) -> str:
    """Render the per-(config, scenario) metrics table."""
    buf = io.StringIO()
    hdr = (f"{'config':<16} {'scenario':<24} {'ok':>3} {'blen':>4} {'gap':>3} "
           f"{'id':>4} {'wr_MB/s':>9} {'wr_util':>7} {'rd_MB/s':>9} "
           f"{'rd_util':>7} {'rd_lat':>7}")
    print(hdr, file=buf)
    print("-" * len(hdr), file=buf)
    id_name = {dc.ID_MODE_FIXED: "fix", dc.ID_MODE_COUNTER: "cnt",
               dc.ID_MODE_LFSR: "lfsr"}
    for r in recs:
        sc = r.scenario
        print(f"{r.config:<16} {sc.name:<24} {'Y' if r.ok else 'N':>3} "
              f"{sc.burst_len:>4} {sc.gap:>3} {id_name.get(sc.id_mode, '?'):>4} "
              f"{r.wr_bw_mb_s:>9.1f} {r.wr_meter.util:>7.1%} "
              f"{r.rd_bw_mb_s:>9.1f} {r.rd_meter.util:>7.1%} "
              f"{r.rd_avg_latency_cyc:>7.1f}", file=buf)
    return buf.getvalue()


def print_report(recs: List[CharRecord], file=sys.stdout) -> None:
    print(format_table(recs), file=file)
    n_cfg = len({r.config for r in recs})
    print(f"=== characterization summary (clk="
          f"{recs[0].clk_mhz if recs else 0:.0f} MHz, {n_cfg} config(s)) ===",
          file=file)
    for line in summarize(recs):
        print(line, file=file)
    n_ok = sum(1 for r in recs if r.ok)
    print(f"\n{n_ok}/{len(recs)} points passed integrity", file=file)


def write_csv(recs: List[CharRecord], path: str) -> None:
    """Write one row per scenario (flat, tool-friendly)."""
    cols = ["config", "scenario", "family", "burst_len", "txn_count", "gap",
            "id_mode", "ok", "mismatched", "bytes_moved", "clk_mhz",
            "wr_cycles", "wr_util", "wr_bw_mb_s",
            "rd_cycles", "rd_util", "rd_bw_mb_s", "rd_avg_latency_cyc",
            "rd_hist_total", "notes"]
    with open(path, "w", newline="") as fh:
        w = _csv.writer(fh)
        w.writerow(cols)
        for r in recs:
            sc = r.scenario
            w.writerow([r.config, sc.name, sc.family, sc.burst_len, sc.txn_count,
                        sc.gap, sc.id_mode, int(r.ok),
                        r.mismatched, r.bytes_moved, r.clk_mhz,
                        r.wr_cycles, f"{r.wr_meter.util:.4f}", f"{r.wr_bw_mb_s:.2f}",
                        r.rd_cycles, f"{r.rd_meter.util:.4f}", f"{r.rd_bw_mb_s:.2f}",
                        f"{r.rd_avg_latency_cyc:.2f}", r.rd_hist_total,
                        "; ".join(r.notes)])
