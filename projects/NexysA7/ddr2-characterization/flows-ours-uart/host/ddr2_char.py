#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for the DDR2/LPDDR2 characterization harness.

Wraps `UARTAxiBridge` (from projects/components/converters/bin) with a
DDR2-specific register map (mirroring harness_csr.sv). The register
layout is authoritative in the SV; this file must be kept in sync.

Usage:

    from ddr2_char import DDR2CharDriver, MEMTYPE_DDR2

    d = DDR2CharDriver(port="/dev/ttyUSB1")
    assert d.build_id() == 0x44445232, "wrong bitstream loaded"

    d.set_controller_cfg(memtype=MEMTYPE_DDR2, t_phy_wrlat=4, t_rddata_en=6)
    d.set_controller_cap(cap_lookahead_max=4, cap_synth_mask=0xF)

    d.program_wr_engine(
        start_addr=0x0000_0000,
        burst_len=8,
        txn_count=1024,
        lfsr_seed=0xDEADBEEF,
    )
    d.program_rd_engine(
        start_addr=0x0000_0000,
        burst_len=8,
        txn_count=1024,
        lfsr_seed=0xDEADBEEF,  # must match writer for CRC to line up
    )

    d.clear_stats()
    d.start_wr()
    d.start_rd()
    d.wait_done(timeout_s=30.0)

    exp, act, match, valid = d.crc()
    assert match and valid, f"CRC mismatch: exp=0x{exp:08X} act=0x{act:08X}"

    tm = d.timer()
    m  = d.perf_meters()
    print(f"took {tm['cycles']} cycles; "
          f"WR util={m['wr']['prod']/(sum(m['wr'].values()) or 1):.1%}")
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

# Pull in the repo's shared UART client.
_REPO_ROOT = os.environ.get("REPO_ROOT")
if not _REPO_ROOT:
    raise RuntimeError(
        "REPO_ROOT is not set. Source RTLDesignSherpa/env_python before "
        "importing this module."
    )
sys.path.insert(0, os.path.join(_REPO_ROOT, "projects/components/converters/bin"))
from uart_axi_bridge import UARTAxiBridge  # noqa: E402


# =============================================================================
# Bridge address map (bridge_ddr2_char_axil.toml). 1 master x 4 slaves.
# =============================================================================
DDR2_APB_BASE     = 0x00000000  # ddr2-lpddr2 controller CSR (APB)
HARNESS_CSR_BASE  = 0x00010000  # this driver targets these regs
DEBUG_SRAM_BASE   = 0x00040000  # MonBus/DFI trace ring (256 KB @ AXIL64)
DFI_MON_RAM_BASE  = 0x00080000  # DFI cmd-only observability (4 KB)


# =============================================================================
# harness_csr register offsets (from HARNESS_CSR_BASE).
# =============================================================================
# ---- Harness ctrl / status ----
CTRL          = 0x00
STATUS        = 0x04
DBG_WR_PTR    = 0x08
DBG_OVERFLOW  = 0x0C
CRC_EXPECTED  = 0x10
CRC_ACTUAL    = 0x14
CRC_MATCH     = 0x18
SCRATCH       = 0x1C
BUILD_ID      = 0x20
BEATS_MISM    = 0x24
# ---- Timer ----
TIMER_CTRL    = 0x28
TIMER_STATUS  = 0x2C
TIMER_CYC_LO  = 0x30
TIMER_CYC_HI  = 0x34
TIMER_EXP_BEATS = 0x38
RESP_DELAY    = 0x3C
TIMER_R_FIRST_LO = 0x40
TIMER_R_FIRST_HI = 0x44
TIMER_R_LAST_LO  = 0x48
TIMER_R_LAST_HI  = 0x4C
TIMER_W_FIRST_LO = 0x50
TIMER_W_FIRST_HI = 0x54
TIMER_W_LAST_LO  = 0x58
TIMER_W_LAST_HI  = 0x5C
# ---- Runtime controller cfg ----
CTRLR_CFG     = 0x60
CTRLR_CAP     = 0x64
# ---- WR engine cfg ----
WR_START_ADDR    = 0x100
WR_STRIDE_0      = 0x104
WR_STRIDE_1      = 0x108
WR_WRAP_MASK_0   = 0x10C
WR_WRAP_MASK_1   = 0x110
WR_BLEN_TXN      = 0x114  # {gap[27:24], txn[23:8], blen[7:0]}
WR_AXI_ATTR      = 0x118  # {dm[11], burst[10:9], size[8:6], mode[5:4], id[3:0]}
WR_LFSR_SEED     = 0x11C
WR_HASH_SEED0    = 0x120
WR_HASH_SEED1    = 0x124
WR_HASH_SEED2    = 0x128
# ---- RD engine cfg ----
RD_START_ADDR    = 0x180
RD_STRIDE_0      = 0x184
RD_STRIDE_1      = 0x188
RD_WRAP_MASK_0   = 0x18C
RD_WRAP_MASK_1   = 0x190
RD_BLEN_TXN      = 0x194
RD_AXI_ATTR      = 0x198
RD_LFSR_SEED     = 0x19C
RD_HASH_SEED0    = 0x1A0
RD_HASH_SEED1    = 0x1A4
RD_HASH_SEED2    = 0x1A8
# ---- Perf observability ----
OBS_RD_PROD    = 0x1C0
OBS_RD_BP      = 0x1C4
OBS_RD_STARV   = 0x1C8
OBS_RD_IDLE    = 0x1CC
OBS_WR_PROD    = 0x1D0
OBS_WR_BP      = 0x1D4
OBS_WR_STARV   = 0x1D8
OBS_WR_IDLE    = 0x1DC
OBS_HIST_SEL   = 0x1E0  # {bin[5:2], metric[1], bus[0]}
OBS_HIST_COUNT = 0x1E4  # muxed rd/wr on bus bit
OBS_HIST_TOTAL = 0x1E8


# =============================================================================
# Enumerations (mirroring ddr2_lpddr2_pkg)
# =============================================================================
MEMTYPE_DDR2   = 0
MEMTYPE_LPDDR2 = 1

# AXI id-picker modes (per engine cfg_id_mode)
ID_MODE_FIXED   = 0
ID_MODE_COUNTER = 1
ID_MODE_LFSR    = 2

# AXI size (bytes = 2^size); 3 = 8 bytes = 64b bus
AXI_SIZE_1  = 0
AXI_SIZE_2  = 1
AXI_SIZE_4  = 2
AXI_SIZE_8  = 3
AXI_SIZE_16 = 4

# AXI burst types
AXI_BURST_FIXED = 0
AXI_BURST_INCR  = 1
AXI_BURST_WRAP  = 2

# Hist selector bits
HIST_BUS_RD    = 0
HIST_BUS_WR    = 1
HIST_METRIC_0  = 0  # AR->firstR (RD) or AW->B (WR)
HIST_METRIC_1  = 1  # AR->RLAST (RD only; WR ignores)


# =============================================================================
# Data structures returned by driver methods
# =============================================================================
@dataclass
class Status:
    wr_done:        bool
    rd_done:        bool
    wr_error:       bool
    rd_error:       bool
    any_error:      bool
    dbg_clear_busy: bool
    init_done:      bool
    init_fail:      bool


@dataclass
class TimerState:
    done:        bool
    running:     bool
    passed:      bool
    cycles:      int
    r_first:     int
    r_last:      int
    w_first:     int
    w_last:      int


@dataclass
class MeterCounts:
    prod:   int
    bp:     int
    starv:  int
    idle:   int

    def utilisation(self) -> float:
        total = self.prod + self.bp + self.starv + self.idle
        return (self.prod / total) if total else 0.0


# =============================================================================
# Driver
# =============================================================================
class DDR2CharDriver:
    """Host-side driver for the DDR2 characterization harness.

    All 32-bit accesses go through the UART bridge to the harness_csr
    slave (base 0x0001_0000 in the bridge address map). Multi-field
    registers are bit-packed here so callers work with named kwargs.
    """

    BUILD_ID_MAGIC = 0x44445232  # ASCII "DDR2"

    def __init__(self, port: str = "/dev/ttyUSB1", baudrate: int = 115200,
                 timeout: float = 1.0):
        self.bridge = UARTAxiBridge(port=port, baudrate=baudrate,
                                    timeout=timeout)

    # ----- Low-level helpers -----------------------------------------------
    def _rd(self, off: int) -> int:
        val = self.bridge.read(HARNESS_CSR_BASE + off)
        if val is None:
            raise IOError(f"UART read failed at csr+0x{off:03X}")
        return val

    def _wr(self, off: int, val: int) -> None:
        if not self.bridge.write(HARNESS_CSR_BASE + off, val & 0xFFFFFFFF):
            raise IOError(f"UART write failed at csr+0x{off:03X}")

    def _rd64(self, off_lo: int, off_hi: int) -> int:
        return (self._rd(off_hi) << 32) | self._rd(off_lo)

    # ----- Identity + reset ------------------------------------------------
    def build_id(self) -> int:
        return self._rd(BUILD_ID)

    def scratch(self, val: Optional[int] = None) -> int:
        """Ping test — write then read back if `val` supplied."""
        if val is not None:
            self._wr(SCRATCH, val)
        return self._rd(SCRATCH)

    def clear_stats(self) -> None:
        """Pulse CTRL.clear_stats. Zeros the debug_sram write pointer,
        the sticky error latches, all bus-meter buckets, and the
        latency-histogram bins."""
        self._wr(CTRL, 1 << 2)

    def soft_reset(self) -> None:
        self._wr(CTRL, 1 << 4)

    def freeze_trace(self, on: bool = True) -> None:
        """Latch or unlatch CTRL.freeze_trace.

        NB: freeze_trace also freezes the perf meters/histograms (they
        share the perf_freeze wire from harness_csr). Turn it OFF before
        starting a new run.
        """
        # freeze_trace is a *latch*, not a pulse — write reads back next
        # AXIL cycle. To un-freeze we have to write the whole CTRL word
        # with the bit clear, but the other CTRL bits are all self-
        # clearing pulses, so writing 0 works.
        self._wr(CTRL, (1 << 3) if on else 0)

    # ----- Controller runtime cfg -----------------------------------------
    def set_controller_cfg(self,
                           memtype:     int = MEMTYPE_DDR2,
                           t_phy_wrlat: int = 0,
                           t_rddata_en: int = 0,
                           rd_in_order: bool = False) -> None:
        val = ((memtype & 1)
               | ((t_phy_wrlat & 0xFF) << 8)
               | ((t_rddata_en & 0xFF) << 16)
               | ((1 if rd_in_order else 0) << 24))
        self._wr(CTRLR_CFG, val)

    def set_controller_cap(self, cap_lookahead_max: int,
                           cap_synth_mask: int) -> None:
        val = ((cap_lookahead_max & 0xF)
               | ((cap_synth_mask & 0xF) << 4))
        self._wr(CTRLR_CAP, val)

    # ----- Engine programming ---------------------------------------------
    def _pack_blen_txn(self, burst_len: int, txn_count: int, gap: int) -> int:
        return ((burst_len & 0xFF)
                | ((txn_count & 0xFFFF) << 8)
                | ((gap & 0xF) << 24))

    def _pack_axi_attr(self, axi_id: int, id_mode: int, axi_size: int,
                       axi_burst: int, data_mode: int) -> int:
        return ((axi_id & 0xF)
                | ((id_mode & 3) << 4)
                | ((axi_size & 7) << 6)
                | ((axi_burst & 3) << 9)
                | ((1 if data_mode else 0) << 11))

    def program_wr_engine(self, *,
                          start_addr:    int,
                          burst_len:     int = 8,
                          txn_count:     int = 1024,
                          stride_0:      int = 0,
                          stride_1:      int = 0,
                          wrap_mask_0:   int = 0,
                          wrap_mask_1:   int = 0,
                          gap:           int = 0,
                          axi_id:        int = 0,
                          id_mode:       int = ID_MODE_FIXED,
                          axi_size:      int = AXI_SIZE_8,
                          axi_burst:     int = AXI_BURST_INCR,
                          data_mode:     bool = False,
                          lfsr_seed:     int = 0xDEADBEEF,
                          hash_seed0:    int = 0,
                          hash_seed1:    int = 0,
                          hash_seed2:    int = 0) -> None:
        self._wr(WR_START_ADDR,  start_addr)
        self._wr(WR_STRIDE_0,    stride_0 & 0xFFFFFFFF)
        self._wr(WR_STRIDE_1,    stride_1 & 0xFFFFFFFF)
        self._wr(WR_WRAP_MASK_0, wrap_mask_0)
        self._wr(WR_WRAP_MASK_1, wrap_mask_1)
        self._wr(WR_BLEN_TXN,    self._pack_blen_txn(burst_len, txn_count, gap))
        self._wr(WR_AXI_ATTR,    self._pack_axi_attr(axi_id, id_mode, axi_size,
                                                     axi_burst, data_mode))
        self._wr(WR_LFSR_SEED,   lfsr_seed)
        self._wr(WR_HASH_SEED0,  hash_seed0)
        self._wr(WR_HASH_SEED1,  hash_seed1)
        self._wr(WR_HASH_SEED2,  hash_seed2)

    def program_rd_engine(self, *,
                          start_addr:    int,
                          burst_len:     int = 8,
                          txn_count:     int = 1024,
                          stride_0:      int = 0,
                          stride_1:      int = 0,
                          wrap_mask_0:   int = 0,
                          wrap_mask_1:   int = 0,
                          gap:           int = 0,
                          axi_id:        int = 0,
                          id_mode:       int = ID_MODE_FIXED,
                          axi_size:      int = AXI_SIZE_8,
                          axi_burst:     int = AXI_BURST_INCR,
                          data_mode:     bool = False,
                          lfsr_seed:     int = 0xDEADBEEF,
                          hash_seed0:    int = 0,
                          hash_seed1:    int = 0,
                          hash_seed2:    int = 0) -> None:
        self._wr(RD_START_ADDR,  start_addr)
        self._wr(RD_STRIDE_0,    stride_0 & 0xFFFFFFFF)
        self._wr(RD_STRIDE_1,    stride_1 & 0xFFFFFFFF)
        self._wr(RD_WRAP_MASK_0, wrap_mask_0)
        self._wr(RD_WRAP_MASK_1, wrap_mask_1)
        self._wr(RD_BLEN_TXN,    self._pack_blen_txn(burst_len, txn_count, gap))
        self._wr(RD_AXI_ATTR,    self._pack_axi_attr(axi_id, id_mode, axi_size,
                                                     axi_burst, data_mode))
        self._wr(RD_LFSR_SEED,   lfsr_seed)
        self._wr(RD_HASH_SEED0,  hash_seed0)
        self._wr(RD_HASH_SEED1,  hash_seed1)
        self._wr(RD_HASH_SEED2,  hash_seed2)

    # ----- Run control -----------------------------------------------------
    def start_wr(self) -> None:
        self._wr(CTRL, 1 << 0)

    def start_rd(self) -> None:
        self._wr(CTRL, 1 << 1)

    def start_both(self) -> None:
        self._wr(CTRL, (1 << 0) | (1 << 1))

    def status(self) -> Status:
        s = self._rd(STATUS)
        return Status(
            wr_done        = bool(s & (1 << 0)),
            rd_done        = bool(s & (1 << 1)),
            wr_error       = bool(s & (1 << 2)),
            rd_error       = bool(s & (1 << 3)),
            any_error      = bool(s & (1 << 4)),
            dbg_clear_busy = bool(s & (1 << 5)),
            init_done      = bool(s & (1 << 6)),
            init_fail      = bool(s & (1 << 7)),
        )

    def wait_done(self, timeout_s: float = 30.0,
                  poll_interval_s: float = 0.05) -> Status:
        """Poll STATUS until both engines report done or timeout expires."""
        deadline = time.monotonic() + timeout_s
        while time.monotonic() < deadline:
            s = self.status()
            if s.any_error:
                raise RuntimeError(
                    f"engine reported error mid-run: wr={s.wr_error} "
                    f"rd={s.rd_error}"
                )
            if s.wr_done and s.rd_done:
                return s
            time.sleep(poll_interval_s)
        raise TimeoutError(
            f"engines did not complete within {timeout_s} s: "
            f"wr_done={s.wr_done} rd_done={s.rd_done}"
        )

    # ----- Result readback -------------------------------------------------
    def crc(self) -> Tuple[int, int, bool, bool]:
        """Return (expected, actual, match, both_valid)."""
        exp = self._rd(CRC_EXPECTED)
        act = self._rd(CRC_ACTUAL)
        m   = self._rd(CRC_MATCH)
        return exp, act, bool(m & 1), (m & 6) == 6

    def beats_mismatched(self) -> int:
        return self._rd(BEATS_MISM)

    # ----- Timer -----------------------------------------------------------
    def timer_clear(self) -> None:
        self._wr(TIMER_CTRL, 1)

    def set_timer_expected_beats(self, n: int) -> None:
        self._wr(TIMER_EXP_BEATS, n & 0xFFFFFFFF)

    def timer(self) -> TimerState:
        st = self._rd(TIMER_STATUS)
        return TimerState(
            done    = bool(st & 1),
            running = bool(st & 2),
            passed  = bool(st & 4),
            cycles  = self._rd64(TIMER_CYC_LO, TIMER_CYC_HI),
            r_first = self._rd64(TIMER_R_FIRST_LO, TIMER_R_FIRST_HI),
            r_last  = self._rd64(TIMER_R_LAST_LO,  TIMER_R_LAST_HI),
            w_first = self._rd64(TIMER_W_FIRST_LO, TIMER_W_FIRST_HI),
            w_last  = self._rd64(TIMER_W_LAST_LO,  TIMER_W_LAST_HI),
        )

    # ----- Response-delay knobs (currently unwired on the RTL side; see
    #        harness_csr comment at 0x3C — kept here so a follow-up that
    #        instantiates axi_response_delay has the API in place). ----
    def set_resp_delay(self, rd_cycles: int, wr_cycles: int) -> None:
        self._wr(RESP_DELAY,
                 ((wr_cycles & 0xFFFF) << 16) | (rd_cycles & 0xFFFF))

    # ----- Perf: bus meters -----------------------------------------------
    def perf_meters(self) -> Dict[str, MeterCounts]:
        rd = MeterCounts(
            prod  = self._rd(OBS_RD_PROD),
            bp    = self._rd(OBS_RD_BP),
            starv = self._rd(OBS_RD_STARV),
            idle  = self._rd(OBS_RD_IDLE),
        )
        wr = MeterCounts(
            prod  = self._rd(OBS_WR_PROD),
            bp    = self._rd(OBS_WR_BP),
            starv = self._rd(OBS_WR_STARV),
            idle  = self._rd(OBS_WR_IDLE),
        )
        return {"rd": rd, "wr": wr}

    # ----- Perf: latency histograms ---------------------------------------
    def _write_hist_sel(self, bus: int, metric: int, bin_idx: int) -> None:
        sel = ((bus & 1)
               | ((metric & 1) << 1)
               | ((bin_idx & 0xF) << 2))
        self._wr(OBS_HIST_SEL, sel)

    def perf_hist_bin(self, bus: int, metric: int, bin_idx: int
                      ) -> Tuple[int, int]:
        """Return (count, total) for the requested bin.

        `bus`     = HIST_BUS_RD or HIST_BUS_WR
        `metric`  = HIST_METRIC_0 (AR->firstR / AW->B) or HIST_METRIC_1
                    (AR->RLAST; WR side ignores)
        `bin_idx` = 0..15 (log2 latency bin b covers [2^b, 2^(b+1)) cycles)
        """
        self._write_hist_sel(bus, metric, bin_idx)
        return self._rd(OBS_HIST_COUNT), self._rd(OBS_HIST_TOTAL)

    def perf_hist_dump(self, bus: int, metric: int = HIST_METRIC_0
                       ) -> Tuple[List[int], int]:
        """Sweep all 16 bins for one metric. Returns (counts[16], total).

        The total is read from the last bin's `perf_hist_bin` -- it is the
        same value across every bin readout, so we take one at the end.
        """
        counts = []
        total  = 0
        for b in range(16):
            c, t = self.perf_hist_bin(bus, metric, b)
            counts.append(c)
            total = t
        return counts, total

    # ----- debug_sram trace ring pointer ----------------------------------
    def dbg_wr_ptr(self) -> int:
        """Words written to debug_sram since last clear."""
        return self._rd(DBG_WR_PTR)

    def dbg_overflow(self) -> bool:
        return bool(self._rd(DBG_OVERFLOW) & 1)


# =============================================================================
# Quick CLI for one-shot smoke reads (dump_status.py style)
# =============================================================================
def _cli() -> None:
    import argparse
    p = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    p.add_argument("--port", default="/dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    args = p.parse_args()

    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    bid = d.build_id()
    print(f"BUILD_ID    = 0x{bid:08X} ({'ok' if bid == d.BUILD_ID_MAGIC else 'MISMATCH'})")
    s = d.status()
    print(f"STATUS      = {s}")
    tm = d.timer()
    print(f"TIMER       = done={tm.done} running={tm.running} pass={tm.passed}")
    print(f"TIMER_CYCLES= {tm.cycles}")
    exp, act, match, valid = d.crc()
    print(f"CRC         = exp=0x{exp:08X} act=0x{act:08X} match={match} valid={valid}")
    print(f"BEATS_MISM  = {d.beats_mismatched()}")
    m = d.perf_meters()
    print(f"WR meter    = prod={m['wr'].prod} bp={m['wr'].bp} "
          f"starv={m['wr'].starv} idle={m['wr'].idle} "
          f"util={m['wr'].utilisation():.1%}")
    print(f"RD meter    = prod={m['rd'].prod} bp={m['rd'].bp} "
          f"starv={m['rd'].starv} idle={m['rd'].idle} "
          f"util={m['rd'].utilisation():.1%}")


if __name__ == "__main__":
    _cli()
