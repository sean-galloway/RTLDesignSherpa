# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""scoria DDR3 characterization -- the perf matrix, run on the board.

Adapted from pumice_char.py. The access-pattern families and the derived
ratios are carried over because they are generation-neutral and they are what
actually diagnoses a controller:

  incremental_BW / col_major_BW            -> the page-management penalty
  col_major_interleaved_BW / col_major_BW  -> bank-level parallelism recovered

What is genuinely different for scoria, and why each matters
-----------------------------------------------------------
1. Geometry is DERIVED FROM bank_lsb, not assumed.
   pumice's Geometry hardcodes "the bank sits just above the column" because
   its address-map scheme mux was retired and that is the only arrangement it
   has. scoria carries ADDR_MAP.bank_lsb as a runtime field (default 10, which
   IS that arrangement), so bank_stride is computed from it. A char run that
   assumed the default while the CSR said otherwise would compute strides that
   do not land where it thinks -- and every family would silently measure
   something else.

2. The address HASH is a hard stop, not a knob to note.
   ADDR_MAP.hash_en scrambles the address-to-(bank,row,col) mapping. With it
   set, a geometry-derived stride does not produce the access pattern its
   family name claims: col_major stops being a guaranteed page miss and
   becomes a random walk. check_addr_map() refuses to characterize rather than
   reporting numbers whose family labels are wrong.

3. Eight stall buckets, not seven -- and that is testable.
   STALL_ZQ was added because ZQ waits otherwise fall through the chain into
   STALL_BANKTIMER, which claims to name a per-bank tRCD/tRP/tRAS block. The
   sum property (every stalled cycle in exactly one bucket) holds either way,
   so the sum alone cannot catch a misattribution. zq_attribution_check()
   tests it directly: with ZQ disabled the zq bucket must be 0, and with a
   short interval it must be nonzero. That is the first functional test of
   this morning's STALL_ZQ wiring, which has never run.

4. ZQ is sampled AROUND every measurement.
   A periodic ZQCS blocks the whole device for tZQCS, so a bandwidth dip can be
   a calibration rather than a scheduling defect. pumice has no equivalent
   because DDR2 has no ZQ command. Without this, the honest reading of an
   outlier is "unexplained".

NOT YET RUN: there is no scoria bitstream. Everything here is verified against
the regmaps and by self-consistency checks; nothing has measured hardware.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass, replace
from typing import Dict, List, Optional, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

import ddr3_char as d3                                  # noqa: E402
from ddr3_char import DDR3CharDriver                    # noqa: E402


# =============================================================================
# Geometry
# =============================================================================
@dataclass(frozen=True)
class Geometry:
    """DDR3 geometry as seen from the AXI byte address.

    Defaults are the Genesys 2 board build: 2 x MT41J256M16 (4Gb x16 each) side
    by side -> a 32-bit DRAM bus, COL_WIDTH=10, NUM_BANKS=8, ROW_WIDTH=15.

    device_bytes then comes out at exactly 1 GiB, which the board independently
    reported at bring-up ("SDRAM: 1.0GiB 32-bit @ 800MT/s") -- so these defaults
    are cross-checked against hardware rather than read off a datasheet. If a
    future edit makes device_bytes disagree with what the BIOS banner says, the
    edit is wrong.

    byte_offset is log2(DRAM bus bytes) = log2(4) = 2, NOT the x16 device's 1:
    the controller addresses the PAIR, so a column step advances four bytes.
    That is the one value most likely to be copied wrong from pumice, where the
    bus is 16-bit and byte_offset is 1.
    """
    col_width:   int = 10
    bank_width:  int = 3            # log2(NUM_BANKS=8)
    row_width:   int = 15           # MT41J256M16
    byte_offset: int = 2            # log2(32-bit DRAM bus = 4 bytes)
    beat_bytes:  int = 8            # host AXI 64-bit -> 8 bytes (axi_size=3)
    #: ADDR_MAP.bank_lsb. Default 10 == col_width, i.e. the bank field sits
    #: immediately above the column. READ IT FROM HARDWARE -- see
    #: check_addr_map(); this default is a default, not an assumption.
    bank_lsb:    int = 10
    #: JEDEC burst length on the DRAM bus. DDR3 is BL8 (or BC4); scoria fixes
    #: one BL per controller instance at init.
    dram_bl:     int = 8

    @property
    def device_bytes(self) -> int:
        """Whole-device span: 2^(col+bank+row) bus-words x bus width."""
        return (1 << (self.col_width + self.bank_width + self.row_width)) \
               << self.byte_offset

    @property
    def page_bytes(self) -> int:
        """Contiguous span within one open (bank, row) page. 4 KiB here: a x16
        MT41J256M16 has a 2 KiB page and there are two of them in parallel."""
        return (1 << self.col_width) << self.byte_offset

    @property
    def bank_stride(self) -> int:
        """Address delta that advances the bank field by one.

        Derived from bank_lsb rather than equated to page_bytes. They coincide
        at the default (bank_lsb == col_width) and diverge the moment anyone
        moves the bank field, which is exactly when a hardcoded stride starts
        measuring the wrong thing without saying so.
        """
        return 1 << (self.bank_lsb + self.byte_offset)

    @property
    def row_stride_same_bank(self) -> int:
        """Address delta to the same column of the NEXT row in the SAME bank
        (must step past every bank) -> a page MISS on every burst."""
        return self.bank_stride << self.bank_width

    @property
    def dram_burst_bytes(self) -> int:
        """Bytes moved by one DRAM burst: BL beats x bus width."""
        return self.dram_bl << self.byte_offset

    @property
    def burst_len_multiple(self) -> int:
        """Legal-AxLEN quantum: AXI beats per DRAM burst.

        Derived, not a magic number. BL8 on a 32-bit bus moves 32 bytes; a
        64-bit AXI beat is 8; so 4. pumice's is 2 for its own config, and
        copying that number across would let one AXI burst straddle a fractional
        DRAM burst -- which the hardware answers with SLVERR or a partial
        transfer, surfacing as read-back mismatches rather than as a config error.
        """
        q, r = divmod(self.dram_burst_bytes, self.beat_bytes)
        if r:
            raise ValueError(
                f"DRAM burst {self.dram_burst_bytes}B is not a whole number of "
                f"{self.beat_bytes}B AXI beats -- no legal AxLEN exists")
        return q


DEFAULT_GEOM = Geometry()

#: Cross-check the defaults against what the board reported at bring-up.
BOARD_REPORTED_BYTES = 1 << 30      # "SDRAM: 1.0GiB" from the LiteDRAM BIOS
assert DEFAULT_GEOM.device_bytes == BOARD_REPORTED_BYTES, (
    f"geometry says {DEFAULT_GEOM.device_bytes} bytes, the board reported "
    f"{BOARD_REPORTED_BYTES}. One of them is wrong and it is probably not the "
    f"board -- see build-litedram/results/README.md.")
assert DEFAULT_GEOM.page_bytes == 4096
assert DEFAULT_GEOM.burst_len_multiple == 4


# =============================================================================
# Access-pattern families
# =============================================================================
FAM_INCREMENTAL    = "incremental"
FAM_ROW_MAJOR      = "row_major"
FAM_COL_MAJOR      = "col_major"
FAM_COL_INTERLEAVE = "col_major_interleaved"
FAMILIES = (FAM_INCREMENTAL, FAM_ROW_MAJOR, FAM_COL_MAJOR, FAM_COL_INTERLEAVE)

TXN_MAX = 0xFFFF


@dataclass(frozen=True)
class Scenario:
    """One generator setup: an access-pattern family plus generator knobs."""
    name:      str
    family:    str
    burst_len: int = 8
    txn_count: int = 256
    gap:       int = 0
    id_mode:   int = d3.ID_MODE_FIXED
    axi_size:  int = d3.AXI_SIZE_8
    #: Per-generator cap on bursts in flight. 0 = as built. This is the axis
    #: for the latency cliff: read bandwidth is bounded by
    #: outstanding x AxLEN / (latency + AxLEN), so sweeping it at fixed AxLEN
    #: walks up to the knee and flattens after it. One bitstream, whole curve.
    max_outstanding: int = 0

    def burst_bytes(self, geom: Geometry) -> int:
        return self.burst_len * (1 << self.axi_size)


def strides_for(sc: Scenario, geom: Geometry) -> Tuple[int, int]:
    """Return (stride_0, wrap_mask_0) for a scenario given the geometry.

    index_1 is inert in the harness pattern generator, so this single
    (stride, wrap) pair fully defines the walk:
        addr[i] = base + (i*stride & wrap-or-all)
    """
    bb = sc.burst_bytes(geom)
    if sc.family == FAM_INCREMENTAL:
        return bb, 0                                  # contiguous, whole space
    if sc.family == FAM_ROW_MAJOR:
        return bb, geom.page_bytes - 1                # wrapped in one page: HIT
    if sc.family == FAM_COL_MAJOR:
        # One row in the SAME bank per burst -> page MISS every burst.
        #
        # Wrapped at the DEVICE boundary, and the reason is a checker artifact
        # pumice diagnosed the hard way: at board scale the walk exceeds the
        # device, the DRAM wraps physically while the address hash uses the
        # pre-wrap address, so every pre-final pass "mismatches". pumice's
        # 2026-08-25 matrix showed 26624/53248/40960 mismatched beats at
        # bl4/8/16 == 55808*BL mod 2^16 exactly, identically across configs --
        # arithmetic, not corruption. Wrapping the GENERATED address keeps
        # hash == cell and changes nothing the DRAM sees.
        #
        # scoria's device is 1 GiB against pumice's 128 MiB, so the wrap is
        # eight times further out -- it bites later, not never.
        return geom.row_stride_same_bank, geom.device_bytes - 1
    if sc.family == FAM_COL_INTERLEAVE:
        # One bank per burst -> activates PIPELINE across banks. Same wrap.
        return geom.bank_stride, geom.device_bytes - 1
    raise ValueError(f"unknown access family: {sc.family!r}")


# =============================================================================
# Stall attribution -- EIGHT buckets on scoria
# =============================================================================
@dataclass(frozen=True)
class StallStats:
    """Stall-cause attribution as a DELTA over one phase.

    The bus meters say the controller did not accept a beat, not WHY. These
    counters split every stalled cycle by the constraint that caused it, so a
    bandwidth report can say where the missing percent went.

    EIGHT buckets on scoria against pumice's seven: `zq` is new. It exists
    because ZQ waits otherwise fall through the stall-reason chain into
    `banktimer`, whose whole claim is that it names a per-bank tRCD/tRP/tRAS
    block -- so the misattribution reads as a real timing problem on a part
    that has none.

    Free-running counters: diff a before/after pair, never read absolute.
    """
    bp:         int   # a command was picked and the DFI would not take it
    refresh:    int   # refresh pending/draining owns the bus
    turnaround: int   # tWTR / tRTW
    tccd:       int   # column-to-column spacing
    actlimit:   int   # tFAW / tRRD
    banktimer:  int   # tRCD / tRP / tRAS on the target bank
    noreq:      int   # both CAMs empty: requester-bound, not DRAM-bound
    zq:         int   # ZQCS wait or inside the tZQCS window

    _F = ("bp", "refresh", "turnaround", "tccd", "actlimit", "banktimer",
          "noreq", "zq")

    def __sub__(self, other: "StallStats") -> "StallStats":
        m = lambda a, b: (a - b) & 0xFFFF_FFFF
        return StallStats(*[m(getattr(self, f), getattr(other, f))
                            for f in self._F])

    @property
    def total(self) -> int:
        return sum(getattr(self, f) for f in self._F)

    @property
    def counted(self) -> bool:
        return self.total > 0

    def limiter(self) -> str:
        """The single largest bucket -- what to go and fix first."""
        if not self.counted:
            return "none"
        return max(self._F, key=lambda f: getattr(self, f))

    def as_dict(self) -> Dict[str, int]:
        return {f: getattr(self, f) for f in self._F}


def read_stall_stats(drv: DDR3CharDriver) -> StallStats:
    d = drv.stall_reasons()
    return StallStats(**{k: d[k] for k in StallStats._F})


# =============================================================================
# scoria-specific guards
# =============================================================================
def check_addr_map(drv: DDR3CharDriver, geom: Geometry = DEFAULT_GEOM,
                   *, strict: bool = True) -> Geometry:
    """Read the live address map and return a geometry that matches HARDWARE.

    Two things this refuses to let pass silently:

    hash_en -- with the address hash on, a geometry-derived stride does not
    produce the pattern its family name claims. col_major stops being a
    guaranteed page miss and becomes a walk whose bank/row sequence depends on
    hash_seed. Every family label would be wrong and every derived ratio
    meaningless, so this raises rather than annotating.

    bank_lsb -- taken from the CSR, not from the default. They agree at
    power-on (both 10), which is exactly why an assumed value survives testing
    and then measures the wrong thing the first time someone moves the field.
    """
    hash_en = drv.scoria.regs.read("ADDR_MAP.hash_en")
    bank_lsb = drv.scoria.regs.read("ADDR_MAP.bank_lsb")
    if hash_en:
        seed = drv.scoria.regs.read("ADDR_MAP.hash_seed")
        msg = (f"ADDR_MAP.hash_en is SET (seed 0x{seed:02X}). The access-pattern "
               f"families are geometry-derived, so with hashing on their names "
               f"are lies: col_major is not a guaranteed page miss and the "
               f"page-management / bank-parallelism ratios measure nothing. "
               f"Clear hash_en to characterize, or characterize something else.")
        if strict:
            raise RuntimeError(msg)
        print(f"WARNING: {msg}")
    if bank_lsb != geom.bank_lsb:
        print(f"note: ADDR_MAP.bank_lsb is {bank_lsb}, geometry default is "
              f"{geom.bank_lsb} -- using hardware. bank_stride "
              f"{1 << (bank_lsb + geom.byte_offset)}B "
              f"(was {geom.bank_stride}B).")
    return replace(geom, bank_lsb=bank_lsb)


def zq_attribution_check(drv: DDR3CharDriver, *,
                         probe_interval: int = 2048,
                         t_zqcs: int = 16,
                         settle_reads: int = 3) -> Dict[str, object]:
    """Test that ZQ stalls land in the ZQ bucket -- the FIRST test of that path.

    The sum property (every stalled cycle in exactly one bucket) cannot catch a
    misattribution: if ZQ cycles were still landing in `banktimer` the sum
    would still be right and `banktimer` would merely be inflated. So this
    checks the thing the sum cannot:

        ZQ disabled      -> the zq bucket must not advance
        ZQ at a short    -> the zq bucket MUST advance, and zqcs_total with it
        interval

    A pass here is what makes `limiter() == "banktimer"` trustworthy on a DDR3
    part. Returns the evidence rather than just a verdict, because "it passed"
    without the counts is the kind of claim this repo does not accept.
    """
    out: Dict[str, object] = {}

    drv.set_zq(enable=0)
    for _ in range(settle_reads):
        read_stall_stats(drv)
    a = read_stall_stats(drv)
    b = read_stall_stats(drv)
    out["disabled_delta_zq"] = (b - a).zq
    out["disabled_zq_total"] = drv.zq_status()["total"]

    drv.set_zq(enable=1, interval=probe_interval, t_zqcs=t_zqcs)
    c = read_stall_stats(drv)
    zq0 = drv.zq_status()["total"]
    for _ in range(settle_reads):
        read_stall_stats(drv)
    d = read_stall_stats(drv)
    zq1 = drv.zq_status()["total"]
    out["enabled_delta_zq"] = (d - c).zq
    out["enabled_zqcs_issued"] = (zq1 - zq0) & 0xFFFF
    out["overdue"] = drv.zq_status()["overdue"]

    out["pass"] = bool(out["disabled_delta_zq"] == 0
                       and out["enabled_delta_zq"] > 0
                       and out["enabled_zqcs_issued"] > 0)
    if not out["pass"]:
        out["why"] = (
            "zq bucket advanced with ZQ disabled" if out["disabled_delta_zq"]
            else "zq bucket did NOT advance with ZQ enabled -- either the "
                 "STALL_ZQ wiring is wrong and those cycles are still being "
                 "charged to banktimer, or the arbiter never granted "
                 f"(overdue={out['overdue']})")
    return out


@dataclass(frozen=True)
class ZqWindow:
    """ZQ activity across one measurement, so an outlier is attributable."""
    zqcs_issued: int
    busy_seen: bool
    overdue: bool

    @property
    def perturbed(self) -> bool:
        return self.zqcs_issued > 0 or self.busy_seen


def zq_window(before: Dict[str, int], after: Dict[str, int]) -> ZqWindow:
    """Fold a zq_status() pair into a verdict about the measurement window.

    A ZQCS blocks the WHOLE device for tZQCS, so a dip that coincides with one
    is calibration, not a scheduling defect. DDR2 needs no equivalent because
    it has no ZQ command -- which is why pumice_char has nothing like this and
    why an unexplained scoria outlier would otherwise stay unexplained.
    """
    return ZqWindow(
        zqcs_issued=(after["total"] - before["total"]) & 0xFFFF,
        busy_seen=bool(before["busy"] or after["busy"]),
        overdue=bool(after["overdue"]),
    )


# =============================================================================
# Derived ratios -- the diagnosis, and the reason the families exist
# =============================================================================
def derived_ratios(bw_by_family: Dict[str, float]) -> Dict[str, Optional[float]]:
    """Turn four bandwidth numbers into two statements about the controller.

    Generation-neutral, which is why they port unchanged from pumice:

      page_penalty   incremental / col_major
                     How much the controller loses when every burst is a page
                     miss. A controller that manages pages well keeps this low.

      bank_parallel  col_major_interleaved / col_major
                     How much of that loss bank-level parallelism wins back.
                     Both families miss the page on every burst; only the
                     interleaved one lets the activates pipeline. 1.0 means the
                     controller got NOTHING from eight banks -- which is what
                     arbiter starvation looks like, and is how pumice's flat
                     2%-of-peak was eventually read.
    """
    def r(a: str, b: str) -> Optional[float]:
        x, y = bw_by_family.get(a), bw_by_family.get(b)
        if x is None or y is None or y == 0:
            return None
        return x / y
    return {
        "page_penalty":  r(FAM_INCREMENTAL, FAM_COL_MAJOR),
        "bank_parallel": r(FAM_COL_INTERLEAVE, FAM_COL_MAJOR),
    }


def peak_mb_s(geom: Geometry = DEFAULT_GEOM, mt_s: int = 800) -> float:
    """Theoretical peak, MB/s. Every bandwidth table must carry this.

    32-bit bus at 800 MT/s -> 3200 MB/s. A measured number without its peak is
    not a result, it is a number: pumice's 12.7 MB/s only became a defect
    report once it was 2% of 3200 rather than "12.7".
    """
    return mt_s * (1 << geom.byte_offset)
