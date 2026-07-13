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
import os
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
    bitslip:     int = -1           # winning read bitslip (coarse word align)
    wr_phase:    int = -1           # kept for API compat (A7 fixes wrphase=3)
    notes:       List[str] = field(default_factory=list)


class A7Leveling:
    """A7DDRPHY READ leveling (A7 has no write leveling / output ODELAY — the
    wlevel_*/wdly_*/half_sys8x_taps CSRs are inert; do not touch them).

    Per LiteDRAM's read-leveling: for each byte lane sweep the read IDELAY tap
    (rdly_dq_inc, 0..31) within each coarse word-alignment bitslip
    (rdly_dq_bitslip, 0..7), writing a known pattern and checking that the read
    back has zero mismatched beats. The longest contiguous passing tap-run is
    the data eye; park the tap at its centre under the widest-eye bitslip.

    Discipline (learned the hard way on silicon):
      * Every rdly/bitslip strobe is dly_sel-bracketed — the PHY gates these by
        dly_sel, so an un-bracketed pulse is a silent no-op.
      * PHY_RST is NEVER pulsed post-init: it tears down the DFI link and only a
        reprogram recovers. Reset the read path with rdly_dq_rst / bitslip_rst.
      * A failing read can wedge the controller; each tap test issues a
        soft_reset first (which now re-inits the controller datapath but
        preserves the PHY CSR taps + cfg) so the pattern write is always clean.
      * wrphase/rdphase stay at the PHY defaults (3/2) — sweeping wrphase breaks
        the write path (pumice's DFI adapter is fixed to those phases).
    """

    N_BITSLIPS  = 8      # a7ddrphy ISERDES bitslip range (mod-8)
    MAX_RD_TAPS = 32     # IDELAYE2 5-bit tap

    def __init__(self, drv: DDR2CharDriver, base_addr: int = 0x0000_0000,
                 burst_len: int = 4, txn_count: int = 2,
                 seed: int = 0x1EAF_F00D, t_phy_wrlat: int = 0,
                 t_rddata_en: int = 6, rddata_delay: int = 0,
                 rd_phase: int = 0, lane_mask: int = 0b11, verbose: bool = True):
        self.drv = drv
        self.base = base_addr
        self.blen = burst_len
        self.txn = txn_count
        self.seed = seed
        self.wrlat = t_phy_wrlat
        self.rden = t_rddata_en
        self.rddly = rddata_delay       # dfi_rddata->rddata_valid realign (ILA=8)
        self.rdphase = rd_phase         # a7ddrphy rdphase=1 (RD cmd on phase 1)
        self.lanes = lane_mask          # x16 -> both byte lanes together (0b11)
        self.verbose = verbose

    def _log(self, msg: str) -> None:
        if self.verbose:
            print(f"[level] {msg}")

    # ---- dly_sel-bracketed PHY strobe (the PHY gates rdly/bitslip by dly_sel)
    def _strobe(self, knob: int) -> None:
        self.drv.phy_poke(dc.PHY_DLY_SEL, self.lanes)
        self.drv.phy_poke(knob, 1)
        self.drv.phy_poke(dc.PHY_DLY_SEL, 0)

    # ---- controller recovery (soft_reset now re-inits the datapath; PHY taps
    #      + cfg persist) so every pattern write starts from a clean state
    def _reinit(self) -> None:
        self.drv.soft_reset()
        time.sleep(0.005)
        self.drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                                    t_phy_wrlat=self.wrlat,
                                    t_rddata_en=self.rden, rd_in_order=True)
        self.drv.set_dfi_rddata_delay(self.rddly)
        self.drv.set_dfi_phase(rd_phase=self.rdphase, wr_phase=0)
        # A prior failing read leaves a STICKY rd_error/any_error latch that
        # soft_reset does not clear (it lives in harness_csr) — clear_stats
        # does. Without this, wait_engine() would false-negative every write
        # after the first bad read. beats_mismatched (our metric) is also reset.
        self.drv.clear_stats()

    def _test(self) -> bool:
        """reinit -> write pattern -> read back; True iff zero beats mismatched."""
        self._reinit()
        self.drv.program_wr_engine(start_addr=self.base, burst_len=self.blen,
                                   txn_count=self.txn, stride_0=self.blen * 8,
                                   lfsr_seed=self.seed, data_mode=True,
                                   hash_seed0=self.seed)
        self.drv.start_wr()
        if not wait_engine(self.drv, "wr"):
            return False
        self.drv.program_rd_engine(start_addr=self.base, burst_len=self.blen,
                                   txn_count=self.txn, stride_0=self.blen * 8,
                                   lfsr_seed=self.seed, data_mode=True,
                                   hash_seed0=self.seed)
        self.drv.clear_stats()
        self.drv.start_rd()
        wait_engine(self.drv, "rd")   # rd_error on mismatch is fine; check beats
        return self.drv.beats_mismatched() == 0

    def _reset_read_path(self) -> None:
        self._strobe(dc.PHY_RDLY_DQ_RST)
        self._strobe(dc.PHY_RDLY_DQ_BITSLIP_RST)

    def _scan_taps(self):
        """At the current bitslip, sweep the 32 IDELAY taps; return passing taps."""
        self._strobe(dc.PHY_RDLY_DQ_RST)          # tap 0
        passing = []
        for tap in range(self.MAX_RD_TAPS):
            if self._test():
                passing.append(tap)
            self._strobe(dc.PHY_RDLY_DQ_INC)
        self._strobe(dc.PHY_RDLY_DQ_RST)          # back to tap 0
        return passing

    @staticmethod
    def _longest_run(vals):
        best = (vals[0], vals[0]); cur = (vals[0], vals[0])
        for v in vals[1:]:
            cur = (cur[0], v) if v == cur[1] + 1 else (v, v)
            if (cur[1] - cur[0]) > (best[1] - best[0]):
                best = cur
        return best

    def run(self) -> LevelingResult:
        """Sweep bitslip x IDELAY-tap, find the widest read eye, centre the tap."""
        res = LevelingResult(ok=False)
        self._log("A7 read leveling (read-only, dly_sel-bracketed, no PHY_RST)")
        self._reset_read_path()
        best = None                     # (width, bitslip, (lo, hi))
        for bs in range(self.N_BITSLIPS):
            passing = self._scan_taps()
            if passing:
                lo, hi = self._longest_run(passing)
                self._log(f"bitslip {bs}: eye taps {lo}..{hi} (width {hi - lo + 1})")
                if best is None or (hi - lo + 1) > best[0]:
                    best = (hi - lo + 1, bs, (lo, hi))
            else:
                self._log(f"bitslip {bs}: no passing tap")
            self._strobe(dc.PHY_RDLY_DQ_BITSLIP)   # advance bitslip (wraps mod-8)
        if best is None:
            res.notes.append("no (bitslip, tap) combination passed — analog "
                             "read path (DQ/DQS capture) not recoverable by "
                             "IDELAY/bitslip; check sys4x_dqs clock / IO / pins")
            return res
        _w, bs, (lo, hi) = best
        centre = (lo + hi) // 2
        self.apply_taps(bs, centre)               # winning bitslip + centre tap
        res.bitslip, res.rd_tap, res.rd_window = bs, centre, (lo, hi)
        self._log(f"chosen bitslip {bs}, read tap {centre} (eye {lo}..{hi})")
        res.ok = self._test()
        if not res.ok:
            res.notes.append("final verify at centred (bitslip, tap) failed")
        return res

    # ---- save / restore a known-good read window --------------------------
    # Leveling is a ~256-iteration UART sweep AND the PHY IDELAY/bitslip state is
    # lost on every FPGA reprogram, so re-leveling dominates every board run.
    # Persist the winning (bitslip, tap) once, then RESTORE it (apply + verify,
    # no sweep) on later runs / after a reprogram. The window is board- and
    # PHY-specific; a failed restore-verify falls back to a full re-level.
    def apply_taps(self, bitslip: int, tap: int) -> None:
        """Apply a known (bitslip, IDELAY tap) directly — no eye sweep."""
        self._reset_read_path()
        self._strobe(dc.PHY_RDLY_DQ_BITSLIP_RST)
        for _ in range(int(bitslip)):
            self._strobe(dc.PHY_RDLY_DQ_BITSLIP)
        self._strobe(dc.PHY_RDLY_DQ_RST)
        for _ in range(int(tap)):
            self._strobe(dc.PHY_RDLY_DQ_INC)

    def restore(self, saved: "LevelingResult") -> LevelingResult:
        """Re-apply a saved window (no sweep) and verify one write-read pass."""
        self.apply_taps(saved.bitslip, saved.rd_tap)
        res = LevelingResult(ok=self._test(), rd_tap=saved.rd_tap,
                             rd_window=saved.rd_window, bitslip=saved.bitslip)
        self._log(f"restored bitslip {saved.bitslip}, tap {saved.rd_tap} "
                  f"-> verify {'OK' if res.ok else 'FAILED (re-level needed)'}")
        if not res.ok:
            res.notes.append("restored (bitslip,tap) failed verify — re-level")
        return res

    @staticmethod
    def save_level(path: str, res: "LevelingResult") -> None:
        import json
        with open(path, "w") as fh:
            json.dump({"ok": res.ok, "bitslip": res.bitslip, "rd_tap": res.rd_tap,
                       "rd_window": list(res.rd_window)}, fh, indent=2)

    @staticmethod
    def load_level(path: str) -> "LevelingResult":
        import json
        d = json.load(open(path))
        return LevelingResult(ok=bool(d.get("ok", True)), bitslip=int(d["bitslip"]),
                              rd_tap=int(d["rd_tap"]),
                              rd_window=tuple(d.get("rd_window", (-1, -1))))


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
                 t_phy_wrlat: int = 0, t_rddata_en: int = 6,
                 rddata_delay: int = 0, rd_phase: int = 0,
                 level_cache: Optional[str] = None):
        self.drv = drv
        self.base = base_addr
        self.t_phy_wrlat = t_phy_wrlat
        self.t_rddata_en = t_rddata_en
        self.rddata_delay = rddata_delay
        self.rd_phase = rd_phase
        # Optional path to persist / reuse the leveled read window (skips the
        # ~256-iteration sweep on later runs; re-levels + re-saves if the saved
        # window fails verify, e.g. after a bitstream change).
        self.level_cache = level_cache
        self.level: Optional[LevelingResult] = None

    def init(self, do_leveling: bool = True) -> None:
        d = self.drv
        d.soft_reset()
        time.sleep(0.01)
        d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2,
                             t_phy_wrlat=self.t_phy_wrlat,
                             t_rddata_en=self.t_rddata_en,
                             rd_in_order=True)
        d.set_dfi_rddata_delay(self.rddata_delay)
        d.set_dfi_phase(rd_phase=self.rd_phase, wr_phase=0)
        if do_leveling:
            lv = A7Leveling(d, base_addr=self.base,
                            t_phy_wrlat=self.t_phy_wrlat,
                            t_rddata_en=self.t_rddata_en,
                            rddata_delay=self.rddata_delay,
                            rd_phase=self.rd_phase)
            import os as _os
            if self.level_cache and _os.path.exists(self.level_cache):
                self.level = lv.restore(A7Leveling.load_level(self.level_cache))
                if not self.level.ok:                     # stale -> re-level
                    print("[simple] cached leveling failed verify; re-leveling")
                    self.level = lv.run()
                    if self.level.ok:
                        A7Leveling.save_level(self.level_cache, self.level)
            else:
                self.level = lv.run()
                if self.level.ok and self.level_cache:
                    A7Leveling.save_level(self.level_cache, self.level)
                    print(f"[simple] saved leveling -> {self.level_cache}")
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
                 txn_count: int = 1024, grid=None, rd_phase: int = 0,
                 rddata_delay: int = 0, level_cache: Optional[str] = None):
        self.drv = drv
        self.base = base_addr
        self.txn = txn_count
        self.grid = grid or self.DEFAULT_GRID
        self.rd_phase = rd_phase
        self.rddata_delay = rddata_delay
        self.level_cache = level_cache

    def init(self, do_leveling: bool = True) -> Optional[LevelingResult]:
        st = SimpleTest(self.drv, base_addr=self.base, rd_phase=self.rd_phase,
                        rddata_delay=self.rddata_delay, level_cache=self.level_cache)
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
    ap.add_argument("--port", default="auto", help="UART device")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0,
                    help="DRAM base address for the workload")
    ap.add_argument("--no-level", action="store_true",
                    help="skip a7ddrphy leveling (assume already levelled)")
    ap.add_argument("--rd-phase", type=int, default=0,
                    help="DFI sub-phase for the READ command. The Nexys a7ddrphy "
                         "takes the DFI command on phase 0 and handles rdphase "
                         "internally, so 0 is correct here (on-silicon: rd_phase=1 "
                         "made reads WORSE, 16/16). Non-zero is for a PHY that "
                         "genuinely consumes a per-command rdphase off the DFI bus.")
    ap.add_argument("--rd-delay", type=int, default=8,
                    help="dfi_rddata_delay: sys-cycles to delay read data to "
                         "meet the a7ddrphy's late rddata_valid (~read_latency=8; "
                         "0=passthrough, for a PHY with no rddata/valid skew)")
    ap.add_argument("--char-level", default="medium",
                    choices=["basic", "medium", "full"],
                    help="scenario depth for --char (basic/medium/full)")
    ap.add_argument("--char-scale", type=int, default=1,
                    help="workload cycle multiplier for --char. Base counts are "
                         "sim-sized (quick); use ~1000 on the FPGA for a long "
                         "soak with stable perf counters (clamped to the 16-bit "
                         "engine txn limit)")
    ap.add_argument("--char-configs", default="baseline",
                    help="controller configs to cross against every generator "
                         "scenario: 'baseline' (default, single), 'matrix' (the "
                         "isolating set: baseline/bank_interleave/open_page/"
                         "inorder/reorder), 'all', or a comma-separated list of "
                         "preset names (paging/OOO/refresh)")
    ap.add_argument("--char-profile", default=None,
                    help="run a named RUN_PROFILES matrix (smoke/matrix/full) -- "
                         "the SAME definition the sim harness pulls, so a board "
                         "run and a sim run are identical bar --char-scale. "
                         "Overrides --char-configs/--char-level when set")
    ap.add_argument("--csv", default=None,
                    help="write --char records to this CSV path")
    ap.add_argument("--level-cache", default=None,
                    help="persist/reuse the leveled read window (JSON). If the "
                         "file exists it is RESTORED (apply + verify, no ~256-"
                         "iter sweep); a failed verify re-levels + re-saves. "
                         "Board+PHY specific; delete it after a bitstream change.")
    ap.add_argument("--clk-mhz", type=float, default=100.0,
                    help="controller clock for bandwidth (MB/s) derivation")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--level-only", action="store_true",
                      help="run leveling and report the eye, nothing else")
    mode.add_argument("--simple", action="store_true",
                      help="init + one write-then-read integrity pass")
    mode.add_argument("--full", action="store_true",
                      help="init + full workload-sweep characterization")
    mode.add_argument("--char", action="store_true",
                      help="init + access-pattern characterization sweep "
                           "(incremental / row-major / col-major page attack)")
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)

    drv = DDR2CharDriver(port=args.port, baudrate=args.baud)
    bid = drv.build_id()
    if bid != 0x4444_5232:
        print(f"WARNING: BUILD_ID=0x{bid:08X} (expected 0x44445232 'DDR2') "
              "-- wrong bitstream loaded?")

    if args.level_only:
        lv = A7Leveling(drv, base_addr=args.base, rd_phase=args.rd_phase,
                        rddata_delay=args.rd_delay)
        if args.level_cache and os.path.exists(args.level_cache):
            res = lv.restore(A7Leveling.load_level(args.level_cache))
            if not res.ok:
                res = lv.run()
                if res.ok:
                    A7Leveling.save_level(args.level_cache, res)
        else:
            res = lv.run()
            if res.ok and args.level_cache:
                A7Leveling.save_level(args.level_cache, res)
                print(f"saved leveling -> {args.level_cache}")
        print(f"leveling ok={res.ok} wr_phase={res.wr_phase} "
              f"rd_tap={res.rd_tap} window={res.rd_window} notes={res.notes}")
        return 0 if res.ok else 1

    if args.simple:
        st = SimpleTest(drv, base_addr=args.base, rd_phase=args.rd_phase,
                        rddata_delay=args.rd_delay, level_cache=args.level_cache)
        st.init(do_leveling=not args.no_level)
        r = st.run()
        print(f"simple: {'PASS' if r.ok else 'FAIL'} "
              f"expected=0x{r.expected:08X} actual=0x{r.actual:08X} "
              f"mismatched={r.mismatched}")
        return 0 if r.ok else 1

    if args.full:
        fc = FullCharacterization(drv, base_addr=args.base, rd_phase=args.rd_phase,
                                  rddata_delay=args.rd_delay,
                                  level_cache=args.level_cache)
        fc.init(do_leveling=not args.no_level)
        pts = fc.run()
        n_ok = sum(1 for p in pts if p.ok)
        print(f"\nfull characterization: {n_ok}/{len(pts)} workloads passed")
        return 0 if n_ok == len(pts) else 1

    if args.char:
        # Lazy import keeps pumice_char's `from pumice_master import wait_engine`
        # free of an import cycle (this module is fully loaded before main runs).
        import pumice_char as pc
        # Reuse the SimpleTest init path (reset + controller cfg + leveling).
        st = SimpleTest(drv, base_addr=args.base, rd_phase=args.rd_phase,
                        rddata_delay=args.rd_delay, level_cache=args.level_cache)
        st.init(do_leveling=not args.no_level)

        def _progress(name: str, i: int, n: int) -> None:
            print(f"[char {i}/{n}] {name}", file=sys.stderr)

        if args.char_profile:
            recs = pc.run_profile(drv, args.char_profile,
                                 txn_scale=args.char_scale, base_addr=args.base,
                                 clk_mhz=args.clk_mhz, progress=_progress)
        else:
            recs = pc.run_matrix(drv, configs=args.char_configs,
                                level=args.char_level, txn_scale=args.char_scale,
                                base_addr=args.base, clk_mhz=args.clk_mhz,
                                progress=_progress)
        print()
        pc.print_report(recs)
        if args.csv:
            pc.write_csv(recs, args.csv)
            print(f"\nwrote {len(recs)} records to {args.csv}")
        n_ok = sum(1 for r in recs if r.ok)
        return 0 if n_ok == len(recs) else 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
