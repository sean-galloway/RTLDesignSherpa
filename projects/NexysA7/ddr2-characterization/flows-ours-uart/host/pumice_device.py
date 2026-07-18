# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Named device composition for the pumice DDR2 char flow.

The mirror of STREAM's stream_device.py: each register map imports on its own as
a `Device` over one injected bridge -- NO hand-merging:

  * `Pumice`  -> the PeakRDL-generated pumice controller regmap (pumice_regmap.py,
                 APB slave @ base 0x0). Carries pumice's runtime knobs by name
                 (DFI phase, page policy, scheduler tuning) plus by-name access to
                 every other controller register.
  * harness   -> the char-harness CSR regmap (harness_csr_regmap.py) @ 0x0001_0000.

Separate `Device` objects are sufficient (see DDR2CharDriver's self.pumice /
self.regs); `build_ddr2_bus()` is offered only when a single top container to
iterate is convenient. The SAME objects drive the FPGA and cocotb sim -- only the
injected bridge differs.

    from pumice_device import build_ddr2_bus
    bus = build_ddr2_bus(bridge)
    bus["pumice"].set_dfi_phase(rd_phase=0)
    bus["pumice"].set_page_policy(1)                 # OPEN
    if bus["harness"].STATUS.init_done: ...
"""

from __future__ import annotations

import logging
import os
from typing import Dict, Optional

from TBClasses.harness.device import Device, DeviceBus


# Register-window base addresses in the char-harness bridge map.
DDR2_APB_BASE    = 0x0000_0000   # pumice controller CSR (APB slave)
HARNESS_CSR_BASE = 0x0001_0000   # char-harness control block


def _repo_root() -> str:
    env = os.environ.get("REPO_ROOT")
    if env:
        return env
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(12):
        if os.path.isdir(os.path.join(d, "bin", "TBClasses")):
            return d
        d = os.path.dirname(d)
    raise FileNotFoundError("REPO_ROOT not found; source env_python")


def _pumice_regmap() -> str:
    return os.path.join(_repo_root(), "projects/components/memory-controllers/"
                        "pumice-ddr2-lpddr2/dv/tbclasses/pumice_regmap.py")


def _harness_regmap() -> str:
    return os.path.join(_repo_root(), "projects/NexysA7/ddr2-characterization/"
                        "ddr2_char_framework/dv/tbclasses/harness_csr_regmap.py")


class Pumice(Device):
    """One pumice DDR2/LPDDR2 controller instance, addressed by name.

    Extends the generic `Device` with a few common runtime knobs; every other
    controller register is reachable by name via the inherited `dev.<REG>.<field>`
    sugar and write/read/field helpers.
    """

    # ----- DFI phase --------------------------------------------------------
    def set_dfi_phase(self, rd_phase: int, wr_phase: int = 0,
                      gear_ratio: Optional[int] = None,
                      bl: Optional[int] = None) -> None:
        """Place the READ/WRITE DFI commands on given sub-phases (a7ddrphy
        rdphase/wrphase contract). DFI_PHASE @ APB 0x060; set while idle.

        DFI_PHASE also carries gear_ratio[8:7] (= log2(active DFI rate): 0=1:1,
        1=1:2, 2=1:4) and bl[12:9] (= JEDEC burst length in device beats, the
        single source of truth for the sub-DFI-word framing, task #146). This is
        a FULL-WORD write (rd_phase/wr_phase are the only other named fields), so
        writing it naively would clobber gear_ratio/bl to 0 and pumice would mask
        off all but DFI phase 0 / collapse the burst framing -> the geared
        read/write path breaks (reads never complete). Both are therefore
        PRESERVED by default: pass gear_ratio/bl=None (default) to read-modify-
        write and keep whatever the RTL reset / a prior write established, or pass
        explicit values. The board build's RTL reset is gear_ratio=2 (=1:4,
        matching the fixed nphases=4 a7ddrphy) and bl=8 (DDR2 BL8 — a BL8 x16
        read fills one full 128b DFI word in one 8-slot PHY event; BL4 filled
        only half -> stale -> the on-silicon read-fail root cause), so the None
        defaults leave the board (and the rate-4 sim) correct as intended."""
        if gear_ratio is None and bl is None:
            # rmw: splice rd/wr phase in, leave gear_ratio/bl (+ any other bits)
            # untouched so the geared DFI read path is not broken.
            self.regs.write("DFI_PHASE", rmw=True, rd_phase=rd_phase & 0x7,
                            wr_phase=wr_phase & 0x7)
        elif gear_ratio is not None and bl is not None:
            # full-word: set every named field explicitly (no rmw needed).
            self.regs.write("DFI_PHASE", rd_phase=rd_phase & 0x7,
                            wr_phase=wr_phase & 0x7,
                            gear_ratio=gear_ratio & 0x3, bl=bl & 0xF)
        else:
            # only one of gear_ratio/bl given -> rmw to preserve the other field.
            fields = dict(rd_phase=rd_phase & 0x7, wr_phase=wr_phase & 0x7)
            if gear_ratio is not None:
                fields["gear_ratio"] = gear_ratio & 0x3
            if bl is not None:
                fields["bl"] = bl & 0xF
            self.regs.write("DFI_PHASE", rmw=True, **fields)

    def get_dfi_phase(self) -> tuple:
        return (self.regs.field("DFI_PHASE", "rd_phase"),
                self.regs.field("DFI_PHASE", "wr_phase"))

    # ----- PHY timing / memtype --------------------------------------------
    def set_phy_timing(self, *, memtype: Optional[int] = None,
                       t_phy_wrlat: Optional[int] = None,
                       t_rddata_en: Optional[int] = None,
                       refresh_burst: Optional[int] = None) -> None:
        """PHY_TIMING @ APB 0x064: memtype (0=DDR2,1=LPDDR2), t_phy_wrlat
        (WR cmd -> dfi_wrdata_en; 0 for a7ddrphy pre-pull), t_rddata_en
        (RD cmd -> dfi_rddata_en window), refresh_burst (1..8). Only supplied
        fields change (rmw). Program BEFORE releasing init."""
        kw: Dict[str, int] = {}
        if memtype is not None:
            kw["memtype"] = memtype & 1
        if t_phy_wrlat is not None:
            kw["t_phy_wrlat"] = t_phy_wrlat & 0xFF
        if t_rddata_en is not None:
            kw["t_rddata_en"] = t_rddata_en & 0xFF
        if refresh_burst is not None:
            kw["refresh_burst"] = refresh_burst & 0xF
        if kw:
            self.regs.write("PHY_TIMING", rmw=True, **kw)

    def set_deskew(self, *, deskew_lo: Optional[int] = None,
                   deskew_hi: Optional[int] = None) -> None:
        """PHY_TIMING @ APB 0x064 deskew_lo[25:24]/deskew_hi[27:26]: per-64b-beat
        read-capture DESKEW (realigns the two beats of a 128b DFI word the
        a7ddrphy returns skewed). Trained at bring-up; set while idle. rmw."""
        kw: Dict[str, int] = {}
        if deskew_lo is not None:
            kw["deskew_lo"] = deskew_lo & 0x3
        if deskew_hi is not None:
            kw["deskew_hi"] = deskew_hi & 0x3
        if kw:
            self.regs.write("PHY_TIMING", rmw=True, **kw)

    # ----- address map / paging --------------------------------------------
    def set_addr_map(self, *, bank_lsb: Optional[int] = None,
                     hash_en: Optional[int] = None,
                     hash_seed: Optional[int] = None) -> None:
        """ADDR_MAP @ APB 0x04C single-knob mapping: bank_lsb slides the bank
        field within the AXI address (col_lo|bank|col_hi|row|rank), hash_en
        folds an XOR hash over the row, hash_seed picks the fold. Only supplied
        fields change (rmw)."""
        kw: Dict[str, int] = {}
        if bank_lsb is not None:
            kw["bank_lsb"] = bank_lsb & 0x1F
        if hash_en is not None:
            kw["hash_en"] = 1 if hash_en else 0
        if hash_seed is not None:
            kw["hash_seed"] = hash_seed & 0xFF
        if kw:
            self.regs.write("ADDR_MAP", rmw=True, **kw)

    # Legacy scheme API (compat): the retired scheme selector is now a single
    # bank_lsb knob. Map the old enum onto bank_lsb so scheme-sweep programs
    # keep working. col_width defaults to the board geometry (10).
    _SCHEME_ROW_MAJOR = 1
    _SCHEME_BANK_INTERLEAVE = 2
    _SCHEME_XOR_HASH = 3

    def set_addr_map_scheme(self, scheme: int, col_width: int = 10) -> None:
        """Compat: legacy scheme -> ADDR_MAP.bank_lsb / hash_en.
        ROW_MAJOR = bank above the full column (bank_lsb=col_width);
        BANK_INTERLEAVE = bank at the LSB column boundary (bank_lsb=0);
        XOR_HASH = enable the row XOR fold. DEFAULT (0/None) leaves it as built."""
        if scheme == self._SCHEME_ROW_MAJOR:
            self.set_addr_map(bank_lsb=col_width, hash_en=0)
        elif scheme == self._SCHEME_BANK_INTERLEAVE:
            self.set_addr_map(bank_lsb=0, hash_en=0)
        elif scheme == self._SCHEME_XOR_HASH:
            self.set_addr_map(hash_en=1)
        # scheme 0 / DEFAULT: no write (keep build-time bank_lsb).

    def get_synth_scheme_mask(self) -> int:
        """Compat: every scheme is now runtime-expressible via bank_lsb + hash,
        so all three legacy schemes are 'synthesized' (b0=ROW_MAJOR,
        b1=BANK_INTERLEAVE, b2=XOR_HASH)."""
        return 0x7

    # ----- refresh ----------------------------------------------------------
    def set_page_policy(self, policy: int) -> None:
        """REFRESH_TUNING.page_policy_or (0=param default,1=OPEN,2=CLOSE,3=HYBRID)."""
        self.regs.write("REFRESH_TUNING", rmw=True, page_policy_or=policy & 0x3)

    def set_refresh(self, *, refpb_policy: Optional[int] = None,
                    refresh_defer: Optional[int] = None,
                    zqcs_freq_hz: Optional[int] = None) -> None:
        """Refresh scheduling knobs (REFRESH_TUNING); only supplied fields change."""
        kw: Dict[str, int] = {}
        if refpb_policy is not None:
            kw["refpb_policy_or"] = refpb_policy & 0x3
        if refresh_defer is not None:
            kw["refresh_defer_active"] = refresh_defer & 0xF
        if zqcs_freq_hz is not None:
            kw["zqcs_freq_hz"] = zqcs_freq_hz & 0xFFFF
        if kw:
            self.regs.write("REFRESH_TUNING", rmw=True, **kw)

    def set_refresh_interval(self, t_refi: int) -> None:
        """tREFI in MC cycles (TIMINGS_RFC_REFI.tREFI); rmw preserves tRFC."""
        self.regs.write("TIMINGS_RFC_REFI", rmw=True, tREFI=t_refi & 0xFFFF)

    # ----- command scheduler ------------------------------------------------
    def set_scheduler(self, *, lookahead: Optional[int] = None,
                      force_inorder: Optional[bool] = None,
                      happy_enable: Optional[bool] = None,
                      age_max: Optional[int] = None,
                      txn_high_water: Optional[int] = None) -> None:
        """SCHED_TUNING knobs; only supplied fields change (rmw)."""
        kw: Dict[str, int] = {}
        if lookahead is not None:
            kw["lookahead_active"] = lookahead & 0xF
        if force_inorder is not None:
            kw["force_inorder"] = 1 if force_inorder else 0
        if happy_enable is not None:
            kw["happy_enable"] = 1 if happy_enable else 0
        if age_max is not None:
            kw["age_max_runtime"] = age_max & 0xFF
        if txn_high_water is not None:
            kw["txn_queue_high_water"] = txn_high_water & 0xFF
        if kw:
            self.regs.write("SCHED_TUNING", rmw=True, **kw)

    def get_lookahead_max(self) -> int:
        """Build-time max reorder-window depth (SCHED_TUNING.lookahead_max_obs)."""
        return self.regs.field("SCHED_TUNING", "lookahead_max_obs")

    # ----- status -----------------------------------------------------------
    def init_done(self) -> bool:
        return bool(self.regs.field("STATUS", "init_done"))


def build_ddr2_bus(bridge, *, pumice_base: int = DDR2_APB_BASE,
                   harness_base: int = HARNESS_CSR_BASE,
                   log: Optional[logging.Logger] = None) -> DeviceBus:
    """Compose the pumice char flow's two register spaces onto one DeviceBus.

    Each regmap imports on its own as a named Device (no hand-merge):
      bus["pumice"]  -> pumice controller regmap (typed `Pumice`)
      bus["harness"] -> char-harness regmap (the hand-authored CSR map)
    """
    bus = DeviceBus(bridge, log=log)
    bus.add("pumice", base=pumice_base, regmap_file=_pumice_regmap(), cls=Pumice)
    bus.add("harness", base=harness_base, regmap_file=_harness_regmap())
    return bus
