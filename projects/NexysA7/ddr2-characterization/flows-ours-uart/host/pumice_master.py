#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice_master.py -- master host program for the pumice (DDR2/LPDDR2)
characterization harness on the Nexys A7.

Mirrors the stream characterization host flow: it talks to the FPGA over UART
(the ASCII W/R bridge protocol via UARTAxiBridge -> DDR2CharDriver), then drives
three layers on top of that transport:

    A7Leveling            -- run the a7ddrphy read/write leveling by driving the
                             calibration CSR knobs (harness_csr 0x80-0x8C) and
                             using the harness's own pattern-gen + CRC engines as
                             a data-eye detector.
    SimpleTest            -- init (reset + controller cfg + leveling) then run a
                             small write-then-read integrity pass.
    FullCharacterization  -- init then sweep burst-length / stride / gap
                             workloads, collecting the cycle timer, bus-meter
                             utilisation, and AXI latency histograms.

Usage:
    ./pumice_master.py --port /dev/ttyUSB1 --simple
    ./pumice_master.py --port /dev/ttyUSB1 --full
    ./pumice_master.py --port /dev/ttyUSB1 --level-only

NOTE: leveling on real DDR2 is data-dependent; the delay-sweep here finds the
CRC-passing tap window from the live device. The a7ddrphy DQS write-leveling
knobs (wlevel_en/strobe) are exposed too; this flow uses the practical
data-eye scan (write a known pattern, sweep read taps, centre the window),
which is robust with the harness's built-in pattern/CRC engines.
"""

import argparse
import sys
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# The driver lives alongside this file.
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import ddr2_char as dc
from ddr2_char import DDR2CharDriver


# =============================================================================
# Shared helper -- wait on ONE engine (write-then-read is phased; the driver's
# wait_done() needs BOTH engines done, which would hang after a write-only or
# read-only phase).
# =============================================================================
def wait_engine(drv: DDR2CharDriver, which: str, timeout_s: float = 15.0) -> bool:
    assert which in ("wr", "rd")
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        s = drv.status()
        if s.any_error:
            return False
        if (which == "wr" and s.wr_done) or (which == "rd" and s.rd_done):
            return True
        time.sleep(0.005)
    return False


# =============================================================================
# Layer 1 -- a7ddrphy read/write leveling
# =============================================================================
@dataclass
class LevelingResult:
    ok:          bool
    rd_tap:      int = -1           # centred read IDELAY tap
    rd_window:   Tuple[int, int] = (-1, -1)  # (first, last) passing tap
    wr_phase:    int = -1           # working write phase
    notes:       List[str] = field(default_factory=list)


class A7Leveling:
    """Drives the a7ddrphy calibration CSR knobs to align the DQ capture.

    Read leveling: reset the DQ IDELAY, write a known pattern once, then step
    the read delay tap while re-reading + CRC-checking; the contiguous range
    of passing taps is the data eye, and we park the tap at its centre.
    Write leveling: sweep the write phase (0..DFI_RATE-1) and keep the first
    phase that yields a clean write-then-read.
    """

    MAX_RD_TAPS = 32     # Artix-7 IDELAYE2 has 32 taps (5-bit)
    N_WR_PHASES = 4      # DFI_RATE = 4 on the a7ddrphy config

    def __init__(self, drv: DDR2CharDriver, base_addr: int = 0x0000_0000,
                 burst_len: int = 8, txn_count: int = 32,
                 seed: int = 0x1EAF_F00D, verbose: bool = True):
        self.drv = drv
        self.base = base_addr
        self.blen = burst_len
        self.txn = txn_count
        self.seed = seed
        self.verbose = verbose

    def _log(self, msg: str) -> None:
        if self.verbose:
            print(f"[level] {msg}")

    # ---- low-level engine sequencing (write THEN read, phased) -----------
    def _write_pattern(self) -> bool:
        self.drv.program_wr_engine(start_addr=self.base, burst_len=self.blen,
                                   txn_count=self.txn, lfsr_seed=self.seed,
                                   data_mode=True, hash_seed0=self.seed)
        self.drv.start_wr()
        return wait_engine(self.drv, "wr")

    def _read_check(self) -> bool:
        """Read the pattern back; True iff CRC matches and no beats mismatch."""
        self.drv.program_rd_engine(start_addr=self.base, burst_len=self.blen,
                                   txn_count=self.txn, lfsr_seed=self.seed,
                                   data_mode=True, hash_seed0=self.seed)
        self.drv.clear_stats()
        self.drv.start_rd()
        if not wait_engine(self.drv, "rd"):
            return False
        # beats_mismatched is the authoritative per-beat integrity signal and
        # is valid in every mode. The leveling pattern uses data_mode (address-
        # hashed data checked per beat), where the summary CRC latches stay
        # invalid — so gate on beats_mismatched, and only require a CRC match
        # when the CRC is actually valid (LFSR mode).
        _exp, _act, match, valid = self.drv.crc()
        crc_ok = match if valid else True
        return crc_ok and (self.drv.beats_mismatched() == 0)

    # ---- knob helpers ----------------------------------------------------
    def reset_phy(self) -> None:
        self.drv.phy_poke(dc.PHY_RST, 1)
        self.drv.phy_poke(dc.PHY_RST, 0)
        # Reset the read-path delay + bitslip to a known zero.
        self.drv.phy_poke(dc.PHY_RDLY_DQ_RST, 1)
        self.drv.phy_poke(dc.PHY_RDLY_DQ_BITSLIP_RST, 1)
        self.drv.phy_poke(dc.PHY_WDLY_DQ_BITSLIP_RST, 1)

    def _select_lane(self, lane: int) -> None:
        self.drv.phy_poke(dc.PHY_DLY_SEL, 1 << lane)

    # ---- leveling passes -------------------------------------------------
    def _scan_read_taps(self) -> Tuple[int, Tuple[int, int]]:
        """With a pattern already written at the current write phase, sweep the
        read IDELAY tap and return (centre, (first,last)) of the longest
        CRC-passing run, or (-1,(-1,-1)) if none passes. Leaves the tap parked
        at the centre when a window is found."""
        self.drv.phy_poke(dc.PHY_RDLY_DQ_RST, 1)
        passing: List[int] = []
        for tap in range(self.MAX_RD_TAPS):
            if self._read_check():
                passing.append(tap)
            self.drv.phy_poke(dc.PHY_RDLY_DQ_INC, 1)
        self.drv.phy_poke(dc.PHY_RDLY_DQ_RST, 1)     # back to tap 0
        if not passing:
            return -1, (-1, -1)
        first, last = self._longest_run(passing)
        centre = (first + last) // 2
        for _ in range(centre):
            self.drv.phy_poke(dc.PHY_RDLY_DQ_INC, 1)
        return centre, (first, last)

    @staticmethod
    def _longest_run(vals: List[int]) -> Tuple[int, int]:
        best = (vals[0], vals[0]); cur = (vals[0], vals[0])
        for v in vals[1:]:
            if v == cur[1] + 1:
                cur = (cur[0], v)
            else:
                cur = (v, v)
            if (cur[1] - cur[0]) > (best[1] - best[0]):
                best = cur
        return best

    def run(self) -> LevelingResult:
        """Joint (write-phase, read-tap) calibration. Write leveling on the
        a7ddrphy is data-independent in JEDEC (DQS-vs-CK), but with the harness
        pattern/CRC engines the practical detector is a joint search: for each
        write phase, write a pattern and sweep the read taps; the first phase
        that yields a passing tap-window wins, and we centre the read tap in it.
        """
        res = LevelingResult(ok=False)
        self._log("resetting PHY calibration state")
        self.reset_phy()
        for phase in range(self.N_WR_PHASES):
            self.drv.phy_poke(dc.PHY_WRPHASE, phase)
            if not self._write_pattern():
                continue
            centre, window = self._scan_read_taps()
            if centre < 0:
                self._log(f"write phase {phase}: no read eye")
                continue
            self._log(f"write phase {phase}: read eye {window}, centre {centre}")
            res.wr_phase, res.rd_tap, res.rd_window = phase, centre, window
            # Final confirmation at the centred (phase, tap).
            res.ok = self._write_pattern() and self._read_check()
            if not res.ok:
                res.notes.append("final verify at centred (phase,tap) failed")
            return res
        res.notes.append("no (write phase, read tap) combination passed")
        return res


# =============================================================================
# Layer 2 -- simple write-then-read integrity test
# =============================================================================
@dataclass
class SimpleResult:
    ok:       bool
    expected: int
    actual:   int
    mismatched: int


class SimpleTest:
    def __init__(self, drv: DDR2CharDriver, base_addr: int = 0x0000_0000,
                 t_phy_wrlat: int = 4, t_rddata_en: int = 6):
        self.drv = drv
        self.base = base_addr
        self.t_phy_wrlat = t_phy_wrlat
        self.t_rddata_en = t_rddata_en
        self.level: Optional[LevelingResult] = None

    def init(self, do_leveling: bool = True) -> None:
        d = self.drv
        d.soft_reset()
        time.sleep(0.01)
        d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                             t_phy_wrlat=self.t_phy_wrlat,
                             t_rddata_en=self.t_rddata_en,
                             rd_in_order=True)
        if do_leveling:
            self.level = A7Leveling(d, base_addr=self.base).run()
            if not self.level.ok:
                print(f"[simple] WARNING: leveling not clean: {self.level.notes}")

    def run(self, burst_len: int = 8, txn_count: int = 64) -> SimpleResult:
        d = self.drv
        seed = 0xC0FFEE01
        d.program_wr_engine(start_addr=self.base, burst_len=burst_len,
                            txn_count=txn_count, lfsr_seed=seed, data_mode=True,
                            hash_seed0=seed)
        d.program_rd_engine(start_addr=self.base, burst_len=burst_len,
                            txn_count=txn_count, lfsr_seed=seed, data_mode=True,
                            hash_seed0=seed)
        d.start_wr()
        wr_ok = wait_engine(d, "wr")
        # NB: do NOT clear_stats() between write and read — it wipes the WR
        # engine's latched expected-CRC (and exp_valid), so the read-side
        # CRC comparison would then compare against 0. beats_mismatched is
        # the authoritative per-beat integrity signal; CRC is the summary.
        d.start_rd()
        rd_ok = wait_engine(d, "rd")
        exp, act, match, valid = d.crc()
        mism = d.beats_mismatched()
        # beats_mismatched is the authoritative per-beat integrity signal and
        # is valid in every mode. The summary CRC is only produced in LFSR
        # (data_mode off) mode; in data_mode the engine checks address-hashed
        # data per beat and leaves the CRC latches invalid — so only enforce a
        # CRC match when the CRC is actually valid.
        crc_ok = match if valid else True
        ok = wr_ok and rd_ok and (mism == 0) and crc_ok
        return SimpleResult(ok=ok, expected=exp, actual=act, mismatched=mism)


# =============================================================================
# Layer 3 -- full characterization sweep
# =============================================================================
@dataclass
class CharPoint:
    burst_len: int
    stride:    int
    gap:       int
    ok:        bool
    cycles:    int
    rd_util:   float
    wr_util:   float
    rd_hist:   List[int]


class FullCharacterization:
    # (burst_len, byte-stride, inter-burst gap) workload grid.
    DEFAULT_GRID = [
        (4,   0,  0),   # dense small bursts, same page
        (8,   0,  0),   # dense BL8
        (16,  0,  0),   # long bursts
        (8,   4096, 0), # page-crossing stride
        (8,   0,  8),   # gapped (idle) bursts
        (8,   64, 0),   # bank-hopping stride
    ]

    def __init__(self, drv: DDR2CharDriver, base_addr: int = 0x0000_0000,
                 txn_count: int = 1024, grid=None):
        self.drv = drv
        self.base = base_addr
        self.txn = txn_count
        self.grid = grid or self.DEFAULT_GRID

    def init(self, do_leveling: bool = True) -> Optional[LevelingResult]:
        st = SimpleTest(self.drv, base_addr=self.base)
        st.init(do_leveling=do_leveling)
        return st.level

    def _run_point(self, blen: int, stride: int, gap: int) -> CharPoint:
        d = self.drv
        seed = 0x5EED_0000 | (blen << 8) | gap
        d.clear_stats()
        d.timer_clear()
        d.program_wr_engine(start_addr=self.base, burst_len=blen,
                            txn_count=self.txn, stride_0=stride, gap=gap,
                            lfsr_seed=seed, data_mode=True, hash_seed0=seed)
        d.program_rd_engine(start_addr=self.base, burst_len=blen,
                            txn_count=self.txn, stride_0=stride, gap=gap,
                            lfsr_seed=seed, data_mode=True, hash_seed0=seed)
        d.start_wr(); wr_ok = wait_engine(d, "wr")
        d.clear_stats(); d.timer_clear()
        d.start_rd(); rd_ok = wait_engine(d, "rd")
        _exp, _act, match, valid = d.crc()
        ok = wr_ok and rd_ok and valid and match and d.beats_mismatched() == 0
        t = d.timer()
        meters = d.perf_meters()
        rd_hist, _tot = d.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
        return CharPoint(burst_len=blen, stride=stride, gap=gap, ok=ok,
                         cycles=t.cycles, rd_util=meters["rd"].utilisation(),
                         wr_util=meters["wr"].utilisation(), rd_hist=rd_hist)

    def run(self) -> List[CharPoint]:
        pts: List[CharPoint] = []
        for (blen, stride, gap) in self.grid:
            p = self._run_point(blen, stride, gap)
            pts.append(p)
            print(f"[char] blen={blen:<3} stride={stride:<5} gap={gap:<2} "
                  f"{'PASS' if p.ok else 'FAIL'}  cyc={p.cycles:<8} "
                  f"rd_util={p.rd_util:5.1%} wr_util={p.wr_util:5.1%}")
        return pts


# =============================================================================
# CLI
# =============================================================================
def main() -> int:
    ap = argparse.ArgumentParser(description="pumice DDR2 characterization master")
    ap.add_argument("--port", default="/dev/ttyUSB1", help="UART device")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0,
                    help="DRAM base address for the workload")
    ap.add_argument("--no-level", action="store_true",
                    help="skip a7ddrphy leveling (assume already levelled)")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--level-only", action="store_true",
                      help="run leveling and report the eye, nothing else")
    mode.add_argument("--simple", action="store_true",
                      help="init + one write-then-read integrity pass")
    mode.add_argument("--full", action="store_true",
                      help="init + full workload-sweep characterization")
    args = ap.parse_args()

    drv = DDR2CharDriver(port=args.port, baudrate=args.baud)
    bid = drv.build_id()
    if bid != 0x4444_5232:
        print(f"WARNING: BUILD_ID=0x{bid:08X} (expected 0x44445232 'DDR2') "
              "-- wrong bitstream loaded?")

    if args.level_only:
        res = A7Leveling(drv, base_addr=args.base).run()
        print(f"leveling ok={res.ok} wr_phase={res.wr_phase} "
              f"rd_tap={res.rd_tap} window={res.rd_window} notes={res.notes}")
        return 0 if res.ok else 1

    if args.simple:
        st = SimpleTest(drv, base_addr=args.base)
        st.init(do_leveling=not args.no_level)
        r = st.run()
        print(f"simple: {'PASS' if r.ok else 'FAIL'} "
              f"expected=0x{r.expected:08X} actual=0x{r.actual:08X} "
              f"mismatched={r.mismatched}")
        return 0 if r.ok else 1

    if args.full:
        fc = FullCharacterization(drv, base_addr=args.base)
        fc.init(do_leveling=not args.no_level)
        pts = fc.run()
        n_ok = sum(1 for p in pts if p.ok)
        print(f"\nfull characterization: {n_ok}/{len(pts)} workloads passed")
        return 0 if n_ok == len(pts) else 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
