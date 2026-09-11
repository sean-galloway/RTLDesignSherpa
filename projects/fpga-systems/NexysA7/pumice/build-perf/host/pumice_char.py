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
import os
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
    def device_bytes(self) -> int:
        """Whole-device span: 2^(col+bank+row) addressable words x word size."""
        return (1 << (self.col_width + self.bank_width + self.row_width)) \
               << self.byte_offset

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
    schedules those out of order is the config's order_mode (FR-FCFS reorders
    across the whole CAM; in_order does not), and R always returns in AR order.
    """
    name:      str
    family:    str
    burst_len: int = 8
    txn_count: int = 256
    gap:       int = 0
    id_mode:   int = dc.ID_MODE_FIXED       # FIXED single-id; LFSR multi-id
    axi_size:  int = dc.AXI_SIZE_8
    # Per-generator cap on bursts in flight. 0 = as built (GEN_MAX_OUTSTANDING,
    # 32 on the current bitstream). This is the axis for the latency cliff:
    # read bandwidth is bounded by outstanding x AxLEN / (latency + AxLEN), so
    # sweeping it at a fixed AxLEN walks straight up to the knee and flat after
    # it. One bitstream, the whole curve. Values above the built ceiling
    # saturate in RTL, so an over-request reads as a flat tail, not a dip.
    max_outstanding: int = 0

    def burst_bytes(self, geom: Geometry) -> int:
        return self.burst_len * (1 << self.axi_size)


# =============================================================================
# Controller configuration axis (paging / scheduling / refresh)
# =============================================================================
# (There is no reorder-window knob: the CAM+arbiter scheduler reorders across
# every entry under FR-FCFS, and SCHED_POLICY.order_mode is the only lever
# that changes that -- 1 = in_order, 3 = age_threshold.)


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
    order_mode:    Optional[int] = None     # SCHED_POLICY.order_mode (0=FR-FCFS, 1=in_order, 3=age_threshold)
    age_thresh:    Optional[int] = None     # SCHED_POLICY.age_thresh (MC cycles/16)
    page_mode:     Optional[int] = None     # PAGE_POLICY_CFG.policy_mode (0=legacy)
    page_tr_init:  Optional[int] = None     # PAGE_TIMEOUT_CFG.tr_init
    page_access:   Optional[Dict[str, int]] = None  # mode 5 table (set_page_access_cfg kw)
    page_rbl:      Optional[Dict[str, int]] = None  # modes 6/7 table (set_page_rbl_cfg kw)
    rd_in_order:   bool = True              # HARNESS check-engine R ordering (CTRLR_CFG bit; pumice R is always AR-order)
    refresh:       Optional[Dict[str, int]] = None  # REF_CTRL (set_refresh kw: mode/postpone/pullin)
    t_refi:        Optional[int] = None      # refresh interval (MC cycles)
    # PHY data timing: MUST match the board-validated bring-up tuple
    # (TASK-BRINGUP: t_phy_wrlat=1 / t_rddata_en=6; sim loopback overrides via
    # TEST_T_PHY_WRLAT=0). apply() re-programs these EVERY scenario, so a stale
    # hardcode here silently clobbers the leveled value -> writes land shifted
    # -> every read mismatches (0/N integrity). This bit us twice: first with a
    # hardcoded 4, then with the pre-tuple 0.
    t_phy_wrlat:   int = int(os.environ.get("TEST_T_PHY_WRLAT", "1"))
    t_rddata_en:   int = 6
    # rddata_delay slides the read DATA onto the rddata_valid cycle. VERIFIED
    # 75/DDR2-300 value = 7 (ILA 2026-09-05: data arrived 1 cycle after valid
    # at 8; razor-sharp single-cycle optimum 6->fail,7->clean,8->fail). Was
    # MISSING from apply() -> stayed 0 -> every read mismatched.
    rddata_delay:  int = int(os.environ.get("TEST_RDDATA_DELAY", "7"))
    rd_phase:      int = 0
    wr_phase:      int = 0
    # JEDEC DDR2 timings (MC cycles) derived from the part + the MC clock.
    # Until 2026-09-08 nothing programmed TIMINGS_*, so every board number was
    # taken on the RDL resets (tRCD/tRP 15 cycles, tCCD 4 = 8 CK, tREFI 1950
    # cycles = 26 us at 75 MHz). Default ON; TEST_JEDEC_TIMINGS=0 restores the
    # reset values for an A/B. PUMICE_MC_CLK_HZ selects the derivation clock;
    # the 100 MHz default is safe (never fewer cycles) on any slower board clock,
    # and the 75 MHz board build should export PUMICE_MC_CLK_HZ=75000000.
    jedec_timings: bool = os.environ.get("TEST_JEDEC_TIMINGS", "1") != "0"
    mc_clk_hz:     int = int(float(os.environ.get("PUMICE_MC_CLK_HZ", "100000000")))

    def apply(self, drv: DDR2CharDriver) -> None:
        # rd_in_order + the DFI latencies live on the harness CTRLR_CFG (one
        # non-rmw write, so always send the known-good latencies with it).
        drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                               t_phy_wrlat=self.t_phy_wrlat,
                               t_rddata_en=self.t_rddata_en,
                               rd_in_order=self.rd_in_order)
        # Program the read-capture alignment every scenario for the same
        # reason as the latencies above: soft_reset clears it, and a read
        # one cycle off valid mismatches 100%.
        drv.set_dfi_phase(rd_phase=self.rd_phase, wr_phase=self.wr_phase)
        drv.set_dfi_rddata_delay(self.rddata_delay)
        # JEDEC timings BEFORE the per-config refresh override below, so a
        # config's deliberate t_refi (the *_refresh pair) still wins.
        if self.jedec_timings:
            applied = drv.set_jedec_timings(self.mc_clk_hz)
            print(f"[config {self.name}] jedec timings @ {self.mc_clk_hz/1e6:.2f} MHz: "
                  + " ".join(f"{k}={v}" for k, v in applied.items()),
                  file=sys.stderr, flush=True)
        # EVERY mode axis is programmed on EVERY config, defaulting to 0 =
        # "build default". Skipping a field when the preset leaves it None
        # makes the matrix ORDER-DEPENDENT: the config inherits whatever the
        # previous one programmed. That is not hypothetical -- on 2026-09-10
        # `refresh_credit` (a CLOSE-page preset) measured 574 MB/s when it ran
        # straight after `rbl_dyn`, because it inherited page_mode=7 and the
        # predictor kept the page open; standalone the same preset measures
        # 33.8. A characterization campaign whose numbers depend on run order
        # is worthless, so nothing is left to inherit.
        if self.scheme is not None:
            drv.set_addr_map_scheme(self.scheme)
        drv.set_page_policy(self.page_policy if self.page_policy is not None else 0)
        if self.t_refi is not None:
            drv.set_refresh_interval(self.t_refi)
        drv.set_refresh(**(self.refresh if self.refresh is not None
                           else {"mode": 0, "postpone": 0, "pullin": 0}))
        # table shape first, then the mode select (predictors read the shape
        # at entry -- see Pumice.set_page_mode)
        drv.set_page_access_cfg(**(self.page_access if self.page_access is not None
                                   else {"ctr_open_max": 0, "ctr_init": 0}))
        drv.set_page_rbl_cfg(**(self.page_rbl if self.page_rbl is not None
                                else {"miss_thresh": 0, "ways_log2": 0,
                                      "sets_log2": 0, "reset_interval": 0}))
        drv.set_page_mode(self.page_mode if self.page_mode is not None else 0,
                          tr_init=self.page_tr_init)
        drv.set_sched_policy(
            order_mode=self.order_mode if self.order_mode is not None else 0,
            age_thresh=self.age_thresh if self.age_thresh is not None else 0)


# Presets. Every knob here is a CSR the CURRENT controller reads (2026-09-09
# cleanup: the pre-rearchitecture lookahead / force_inorder knobs and the
# presets that only differed by them -- reorder, lever_* -- are gone; a
# "reorder" run is `open_page`, since FR-FCFS reorders by default).
#
# Levers, one per axis:
#   scheme       ADDR_MAP.bank_lsb        ROW_MAJOR | BANK_INTERLEAVE
#   page_policy  REFRESH_TUNING.policy_or CLOSE | OPEN   (static policies)
#   page_mode    PAGE_POLICY_CFG.mode     4 adapt_time, 5 adapt_access, 6 rbl_static, 7 rbl_dyn
#   order_mode   SCHED_POLICY.order_mode  0 FR-FCFS | 1 in_order | 3 age_threshold
#   t_refi       TIMINGS_RFC_REFI.tREFI   refresh-bandwidth stress
#   refresh      REF_CTRL                 mode / postpone / pullin credits
# `baseline` = row-major, close-page, FR-FCFS; every other preset changes one
# lever from it, except the predictor set, which sits on open_page (a
# predictor's job is deciding when to close an open row).
CONFIGS: Dict[str, ControllerConfig] = {
    "baseline": ControllerConfig(
        "baseline", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_CLOSE,
        order_mode=0, rd_in_order=True),
    # ---- axis: address map ------------------------------------------------
    "bank_interleave": ControllerConfig(
        "bank_interleave", scheme=dc.SCHEME_BANK_INTERLEAVE,
        page_policy=dc.PAGE_POLICY_CLOSE, order_mode=0, rd_in_order=True),
    # ---- axis: page policy (static) --------------------------------------
    "open_page": ControllerConfig(
        "open_page", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_OPEN,
        order_mode=0, rd_in_order=True),
    "open_interleave": ControllerConfig(
        "open_interleave", scheme=dc.SCHEME_BANK_INTERLEAVE,
        page_policy=dc.PAGE_POLICY_OPEN, order_mode=0, rd_in_order=True),
    # ---- axis: scheduling order ------------------------------------------
    # in_order: per-channel FIFO on the base bitstream (each CAM issues its
    # oldest entry; the arbiter's read/write preference picks the side);
    # global read-vs-write age order needs the PUMICE_ENHANCED build.
    "inorder": ControllerConfig(
        "inorder", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_CLOSE,
        order_mode=1, rd_in_order=True),
    "inorder_open": ControllerConfig(
        "inorder_open", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_OPEN,
        order_mode=1, rd_in_order=True),
    # age_threshold: FR-FCFS until a reference is older than 16*age_thresh
    # MC cycles, then only boosted entries issue (a starvation bound).
    "age_thr": ControllerConfig(
        "age_thr", scheme=dc.SCHEME_ROW_MAJOR, page_policy=dc.PAGE_POLICY_OPEN,
        order_mode=3, age_thresh=8, rd_in_order=True),
    # ---- axis: page-policy predictors (Axis 2 modes 4..7, on open_page) --
    "adapt_time": ControllerConfig(
        "adapt_time", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_OPEN, page_mode=4, page_tr_init=24,
        order_mode=0, rd_in_order=True),
    # Sim-validated shapes: acc ctr_open_max=2/ctr_init=0 (test_pumice_core_acc),
    # rbl miss_thresh=2 no epochs (test_pumice_core_rbl); rbl_dyn wants epochs.
    "adapt_access": ControllerConfig(
        "adapt_access", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_OPEN, page_mode=5,
        page_access={"ctr_open_max": 2, "ctr_init": 0},
        order_mode=0, rd_in_order=True),
    "rbl_static": ControllerConfig(
        "rbl_static", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_OPEN, page_mode=6,
        page_rbl={"miss_thresh": 2, "ways_log2": 0, "sets_log2": 0, "reset_interval": 0},
        order_mode=0, rd_in_order=True),
    "rbl_dyn": ControllerConfig(
        "rbl_dyn", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_OPEN, page_mode=7,
        page_rbl={"miss_thresh": 2, "ways_log2": 0, "sets_log2": 0, "reset_interval": 256},
        order_mode=0, rd_in_order=True),
    # ---- axis: refresh ----------------------------------------------------
    "fast_refresh": ControllerConfig(
        "fast_refresh", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_CLOSE, order_mode=0, t_refi=0x0100,
        rd_in_order=True),
    "slow_refresh": ControllerConfig(
        "slow_refresh", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_CLOSE, order_mode=0, t_refi=0x7FFF,
        rd_in_order=True),
    # JEDEC refresh credits: postpone up to 8 under demand, pull in up to 8
    # on idle (REF_CTRL) -- the refresh-elasticity lever vs strict tREFI.
    "refresh_credit": ControllerConfig(
        "refresh_credit", scheme=dc.SCHEME_ROW_MAJOR,
        page_policy=dc.PAGE_POLICY_CLOSE, order_mode=0,
        refresh={"postpone": 8, "pullin": 8}, rd_in_order=True),
}
BASELINE = CONFIGS["baseline"]
# The default matrix isolates one lever per axis (map, page policy, order).
DEFAULT_MATRIX = ["baseline", "bank_interleave", "open_page", "inorder", "age_thr"]


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
    # Write-side byte count when it differs from bytes_moved. Sequential
    # phases move the same bytes both ways, so this stays None; a concurrent
    # run with an uneven generator mix (say one writer against two readers)
    # does not, and reusing one count there overstates the smaller side.
    wr_bytes:    Optional[int] = None

    # ---- derived bandwidth / latency ------------------------------------
    @staticmethod
    def _bw_mb_s(bytes_moved: int, cycles: int, clk_mhz: float) -> float:
        if cycles <= 0:
            return 0.0
        # bytes/cycle * cycles/s  (clk_mhz*1e6)  -> bytes/s  -> /1e6 = MB/s
        return (bytes_moved / cycles) * clk_mhz

    @property
    def wr_bw_mb_s(self) -> float:
        n = self.wr_bytes if self.wr_bytes is not None else self.bytes_moved
        return self._bw_mb_s(n, self.wr_cycles, self.clk_mhz)

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
        # One row in the SAME bank per burst -> page MISS every burst. Wrapped
        # at the DEVICE boundary: at board scale (txn_scale ~1000) the walk is
        # bigger than the device (64000 txn x 16 KiB = 1 GiB vs 128 MiB), and
        # an UNwrapped generator address makes the address-hash checker lie --
        # the DRAM wraps physically while the hash uses the pre-wrap address,
        # so every pre-final pass "mismatches" (2026-08-25 matrix: 26624/
        # 53248/40960 mismatched beats at bl4/8/16 == 55808*BL mod 2^16
        # EXACTLY, all configs identically -- a checker artifact, not
        # corruption; the same artifact was July's "col_major fails only at
        # scale 1000"). Wrapping the GENERATED address keeps hash==cell
        # while changing no DRAM-visible behaviour of the family.
        return geom.row_stride_same_bank, geom.device_bytes - 1
    if sc.family == FAM_COL_INTERLEAVE:
        # One bank per burst -> activates pipeline across banks. Same
        # device-boundary wrap rationale as col_major.
        return geom.bank_stride, geom.device_bytes - 1
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
                hash_seed1=seed ^ 0x9E37_79B9, hash_seed2=seed ^ 0x85EB_CA6B,
                max_outstanding=sc.max_outstanding)

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
    # ignore_error: a data mismatch latches rd_error and the default bail
    # would misreport a completed-but-wrong phase as "did not complete".
    wr_ok = wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
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
    rd_ok = wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)
    _tr = drv.timer()                       # read window from r_last-r_first stamps
    rd_cycles = max(_tr.r_last - _tr.r_first, 0)
    rd_meter = _read_meter(drv, "rd")
    rd_hist, rd_total = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    drv.freeze_trace(False)                 # leave running for the next scenario

    mism = drv.beats_mismatched()
    # 1:1 accounting: the histogram must see EXACTLY txn_count read
    # transactions — too many (stray/duplicate returns) is as much an error
    # as too few.
    ok = wr_ok and rd_ok and mism == 0 and rd_total == sc.txn_count
    if not wr_ok:
        notes.append("write engine did not complete")
    if not rd_ok:
        notes.append("read engine did not complete")
    if mism:
        notes.append(f"{mism} beats mismatched")
    if rd_total != sc.txn_count:
        notes.append(f"1:1 VIOLATION: hist total {rd_total} != txn_count "
                     f"{sc.txn_count} ({'EXTRA' if rd_total > sc.txn_count else 'MISSING'} returns)")

    return CharRecord(
        scenario=sc, config=cfg.name, ok=ok, mismatched=mism,
        wr_cycles=wr_cycles, wr_meter=wr_meter,
        rd_cycles=rd_cycles, rd_meter=rd_meter,
        rd_hist=tuple(rd_hist), rd_hist_total=rd_total,
        bytes_moved=bytes_moved, clk_mhz=clk_mhz, notes=tuple(notes))


def measure_concurrent(drv: DDR2CharDriver, sc: Scenario, *,
                      cfg: ControllerConfig = BASELINE, geom: Geometry = DEFAULT_GEOM,
                      base_addr: int = 0x0, clk_mhz: float = 100.0,
                      timeout_s: float = 40.0, n_wr: int = 1, n_rd: int = 1
                      ) -> CharRecord:
    """Run writers and readers in ONE window instead of back to back.

    Every other measurement here is a write phase followed by a read phase, so
    the controller never sees both directions at once and read/write turnaround
    (tWTR / tRTW) is never paid. That is the workload where a global reorder
    scheduler is supposed to earn its area: it can batch same-direction columns
    and amortise the turnaround, where a per-bank round-robin machine pays it
    per switch. It is also the only way to load more than one generator, which
    is what the generator array and the two crossbars exist for.

    Regions: the device is split into (n_wr + n_rd) equal power-of-two regions
    and every generator gets its own, so concurrent traffic never races on an
    address. The family's own wrap is intersected with the region mask, which
    keeps the access PATTERN (row stride, bank stride) and only shortens the
    walk. Reader regions are pre-filled in a separate untimed pass; because the
    data mode is the address hash f(addr, seeds), a reader validates against
    that pre-fill without any ordering assumption.

    The returned record carries the SHARED window in both cycle fields, so
    wr_bw_mb_s and rd_bw_mb_s are each direction's share of it and their sum is
    the total throughput the controller sustained.
    """
    # Never program more generators than the bitstream has. The driver's
    # num_gen is only a default; the board is the authority.
    hw = drv.sync_gen_config()
    if n_wr > hw["num_wr_gen"] or n_rd > hw["num_rd_gen"]:
        n_wr, n_rd = min(n_wr, hw["num_wr_gen"]), min(n_rd, hw["num_rd_gen"])

    n_reg = max(n_wr + n_rd, 1)
    stride, fam_wrap = strides_for(sc, geom)
    beat0 = 1 << sc.axi_size

    # Region placement decides what this measures, so it is chosen, not
    # inherited. Give each generator the SMALLEST power-of-two region that
    # holds its own walk and place them ADJACENTLY, so concurrent generators
    # land in neighbouring banks and the run measures multi-master
    # arbitration. Spacing them far apart instead puts them in different ROWS
    # of the same banks, which measures page thrash and nothing else -- with a
    # device/4 split, two readers on row_major collapsed from 570 to 224 MB/s
    # purely from that (2026-09-10).
    #
    # A family whose natural walk already spans the device (col_major,
    # col_interleave) cannot be placed adjacently; those fall back to an even
    # split of the device, with the family wrap intersected so the pattern is
    # preserved and only the walk shortened.
    span = (fam_wrap + 1) if fam_wrap else (sc.txn_count * sc.burst_len * beat0)
    span = 1 << max(0, (span - 1).bit_length())          # round up to pow2
    if span * n_reg <= geom.device_bytes:
        region, wrap = span, fam_wrap
    else:
        region = geom.device_bytes
        while (geom.device_bytes // (region // 2)) <= n_reg and region > geom.page_bytes:
            region //= 2
        wrap = (fam_wrap & (region - 1)) if fam_wrap else (region - 1)
    seed = _stable_seed(sc.name)
    beat_bytes = 1 << sc.axi_size
    per_gen_bytes = sc.txn_count * sc.burst_len * beat_bytes
    notes: List[str] = []

    def _prog(idx: int) -> dict:
        return dict(start_addr=base_addr + idx * region, burst_len=sc.burst_len,
                    txn_count=sc.txn_count, stride_0=stride, wrap_mask_0=wrap,
                    gap=sc.gap, id_mode=sc.id_mode, axi_size=sc.axi_size,
                    data_mode=True, lfsr_seed=seed, hash_seed0=seed,
                    hash_seed1=seed ^ 0x9E37_79B9, hash_seed2=seed ^ 0x85EB_CA6B,
                    max_outstanding=sc.max_outstanding)

    cfg.apply(drv)

    # ---- untimed pre-fill of every reader region -------------------------
    drv.freeze_trace(True)
    for r in range(n_rd):
        drv.program_wr_engine(gen=0, **_prog(n_wr + r))
        drv.clear_stats()
        drv.timer_clear()
        drv.start_wr(0x01)
        if not wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True):
            notes.append(f"pre-fill of reader region {r} did not complete")

    # ---- timed concurrent window -----------------------------------------
    for w in range(n_wr):
        drv.program_wr_engine(gen=w, **_prog(w))
    for r in range(n_rd):
        drv.program_rd_engine(gen=r, **_prog(n_wr + r))
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    drv.start_both(wr_mask=(1 << n_wr) - 1, rd_mask=(1 << n_rd) - 1)
    wr_ok = wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    rd_ok = wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)

    t = drv.timer()
    # ONE window covering both directions: first kick to last completion.
    first = min(t.w_first, t.r_first)
    last = max(t.w_last, t.r_last)
    window = max(last - first, 0)
    wr_meter = _read_meter(drv, "wr")
    rd_meter = _read_meter(drv, "rd")
    rd_hist, rd_total = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    drv.freeze_trace(False)

    mism = drv.beats_mismatched()
    expect_rd_txn = sc.txn_count * n_rd
    ok = wr_ok and rd_ok and mism == 0 and rd_total == expect_rd_txn
    if not wr_ok:
        notes.append("write engines did not complete")
    if not rd_ok:
        notes.append("read engines did not complete")
    if mism:
        notes.append(f"{mism} beats mismatched")
    if rd_total != expect_rd_txn:
        notes.append(f"1:1 VIOLATION: hist total {rd_total} != {expect_rd_txn}")
    notes.append(f"concurrent {n_wr}w+{n_rd}r of {hw['num_wr_gen']}w+"
                 f"{hw['num_rd_gen']}r built, region 0x{region:X}")

    return CharRecord(
        scenario=sc, config=cfg.name, ok=ok, mismatched=mism,
        wr_cycles=window, wr_meter=wr_meter,
        rd_cycles=window, rd_meter=rd_meter,
        rd_hist=tuple(rd_hist), rd_hist_total=rd_total,
        bytes_moved=per_gen_bytes * max(n_rd, 1),
        wr_bytes=per_gen_bytes * max(n_wr, 1), clk_mhz=clk_mhz,
        notes=tuple(notes))


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
    # controller config's job (order_mode), so the matrix cross of these
    # against the `open_page`/`inorder` configs is what exercises OOO. The
    # gap variant probes idle-recovery. (Only added when
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
               concurrent: Optional[Tuple[int, int]] = None,
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
            if concurrent:
                n_wr, n_rd = concurrent
                recs.append(measure_concurrent(
                    drv, sc, cfg=cfg, geom=geom, base_addr=base_addr,
                    clk_mhz=clk_mhz, timeout_s=max(timeout_s, 40.0),
                    n_wr=n_wr, n_rd=n_rd))
            else:
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
    "smoke": dict(configs=["baseline", "bank_interleave", "open_page", "inorder"],
                  level="basic", families=(FAM_INCREMENTAL, FAM_COL_MAJOR)),
    # The isolating config matrix over the full family/burst grid.
    "matrix": dict(configs=DEFAULT_MATRIX, level="medium", families=None),
    # Minimal repros: one config x col_major only -- tight wave-debug iteration.
    "open_min": dict(configs=["open_page"], level="basic",
                     families=(FAM_COL_MAJOR,)),
    "baseline_min": dict(configs=["baseline"], level="basic",
                         families=(FAM_COL_MAJOR,)),
    # PUMICE-020 repro: the multiid (LFSR-id) scenario only — medium level is
    # what adds col_major_bl8_multiid to the suite. baseline config; the 1:1
    # hist-vs-txn_count check is the assertion under investigation.
    "multiid_min": dict(configs=["baseline"], level="medium",
                        families=(FAM_COL_MAJOR,)),
    # Axis-2 page-policy predictors (modes 4..7) on the reorder config, over
    # the pattern pair that separates them (streaming vs page-thrash). This
    # is the sim gate for the restored modes' CSR path.
    "paging": dict(configs=["adapt_time", "adapt_access", "rbl_static", "rbl_dyn"],
                   level="basic", families=(FAM_INCREMENTAL, FAM_COL_MAJOR)),
    # Axis-1 order modes on the base build: per-channel in_order vs
    # age_threshold vs plain reorder, streaming vs page-thrash.
    "order": dict(configs=["open_page", "inorder", "inorder_open", "age_thr"],
                  level="basic", families=(FAM_INCREMENTAL, FAM_COL_MAJOR)),
    # Refresh elasticity: strict vs credited vs the tREFI extremes.
    "refresh": dict(configs=["baseline", "refresh_credit", "fast_refresh", "slow_refresh"],
                    level="basic", families=(FAM_INCREMENTAL, FAM_COL_MAJOR)),
    # BOTH DIRECTIONS AT ONCE, one generator each. Every other profile runs a
    # write phase then a read phase, so read/write turnaround is never paid.
    # This is the first workload that makes the controller interleave
    # directions, which is where a global reorder scheduler should beat a
    # per-bank round-robin one.
    "concurrent": dict(configs=["open_page"], level="basic", families=None,
                       concurrent=(1, 1)),
    # Multi-master: two readers against one writer, all on disjoint regions.
    # Loads the generator array and both crossbars. NOTE two WRITERS is not
    # safe on pumice yet -- PUMICE-027, B returns out of AW order while the
    # write bridge routes by position -- so writers stay at one.
    "multigen": dict(configs=["open_page"], level="basic", families=None,
                     concurrent=(1, 2)),
    # Everything: every preset x the full grid.
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
                      clk_mhz=clk_mhz, progress=progress,
                      concurrent=p.get("concurrent"))


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
