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

    # ----- shadowed writes ---------------------------------------------------
    # On the board the bridge's pumice APB window returns a PRIOR transaction's
    # data on reads (request/response misalignment; the harness window is fine),
    # so a read-modify-write splices stale garbage into every field it meant to
    # preserve — and the corruption depends on the preceding UART traffic, which
    # made whole leveling sweeps silently run at reset timing. NO pumice write
    # may ever rmw. Every setter goes through a host-side write-through shadow:
    # seeded from the RDL reset default, fields spliced in, the FULL word
    # written. invalidate_shadow() must be called after any event that reverts
    # the CSRs to their resets (CTRL.soft_reset does; DDR2CharDriver.soft_reset
    # calls it).
    def invalidate_shadow(self) -> None:
        self._shadow: Dict[str, int] = {}

    def _reg_default(self, reg: str) -> int:
        d = self.regs.registers[reg]["default"]
        return int(d, 16) if isinstance(d, str) else int(d)

    def _wr(self, reg: str, **fields: int) -> int:
        if not hasattr(self, "_shadow"):
            self._shadow = {}
        word = self._shadow.get(reg)
        if word is None:
            word = self._reg_default(reg)
        for name, val in fields.items():
            lo, width = self.regs._field_lo_width(reg, name)
            mask = ((1 << width) - 1) << lo
            word = (word & ~mask) | ((int(val) << lo) & mask)
        self._shadow[reg] = word
        self.regs.write_word(reg, word)
        return word

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
        # Shadowed full-word write: omitted gear_ratio/bl keep their shadowed
        # (or RDL-reset) values — no on-device rmw, whose readback lies.
        fields = dict(rd_phase=rd_phase & 0x7, wr_phase=wr_phase & 0x7)
        if gear_ratio is not None:
            fields["gear_ratio"] = gear_ratio & 0x3
        if bl is not None:
            fields["bl"] = bl & 0xF
        self._wr("DFI_PHASE", **fields)

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
            self._wr("PHY_TIMING", **kw)


    # ----- mode registers (init MRS chain) ---------------------------------
    _MR_REG = {0: "MR0", 1: "MR1", 2: "MR2", 3: "MR3"}

    def set_mr(self, index: int, value: int) -> None:
        """Write a DDR2 mode-register value (MR0..MR3.VAL[15:0]) used by the init
        MRS chain. Takes effect on the NEXT init run (power-on or init_restart()).
        Runtime-writable so software can retune the mode register OR sweep the
        value to defeat an arbitrary board A-lane mapping on MRS commands (the
        MRS address bits are the MR value, so scrambled A-pins scramble it)."""
        if index not in self._MR_REG:
            raise ValueError(f"MR index {index} out of range 0..3")
        self._wr(self._MR_REG[index], VAL=value & 0xFFFF)

    def set_mr0(self, value: int) -> None: self.set_mr(0, value)
    def set_mr1(self, value: int) -> None: self.set_mr(1, value)
    def set_mr2(self, value: int) -> None: self.set_mr(2, value)
    def set_mr3(self, value: int) -> None: self.set_mr(3, value)

    def init_restart(self) -> None:
        """Pulse CTRL.init_force_restart: re-run the JEDEC MRS init WITHOUT a
        controller reset, applying freshly-written MRx.VAL while the CSRs are
        preserved (a soft_reset would wipe the CSRs before init could read them).
        Rising-edge triggered in init_sequencer -> write 1 then 0 to re-arm."""
        self._wr("CTRL", init_force_restart=1)
        self._wr("CTRL", init_force_restart=0)

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
            self._wr("ADDR_MAP", **kw)

    # Legacy scheme API (compat): the retired scheme selector is now a single
    # bank_lsb knob. Map the old enum onto bank_lsb so scheme-sweep programs
    # keep working. col_width defaults to the board geometry (10).
    _SCHEME_ROW_MAJOR = 1
    _SCHEME_BANK_INTERLEAVE = 2
    _SCHEME_XOR_HASH = 3

    def set_addr_map_scheme(self, scheme: int, col_width: int = 10,
                            burst_cols: int = 2) -> None:
        """Compat: legacy scheme -> ADDR_MAP.bank_lsb / hash_en.
        ROW_MAJOR = bank above the full column (bank_lsb=col_width);
        BANK_INTERLEAVE = bank at the LOWEST LEGAL boundary
        bank_lsb = log2(burst_cols), where burst_cols = one JEDEC DRAM burst
        in COLUMN-ADDRESS units. The column address is DEVICE-WORD granular
        (addr_mapper BYTE_OFFSET_WIDTH = clog2(DEVICE/8)), so burst_cols = BL
        (JEDEC device beats), NOT BL*DEVICE/BEAT -- that older "pumice-beat
        units" reading halved it on x16 and striped every burst (2026-08-25
        board finding; sim repro test_ddr2_char_char_families_x16). The
        design note on ADDR_MAP is explicit: max interleave preserves burst
        locality via col_lo — bank_lsb=0 with burst_cols>1 STRIPES one DRAM
        burst across banks, violating the one-burst-one-bank contract (writes
        stripe, the read command fetches one bank's columns -> deterministic
        per-burst corruption; the bank_interleave 0/14 board + 42-beat sim
        signature, issue #42);
        XOR_HASH = enable the row XOR fold. DEFAULT (0/None) leaves it as built."""
        if scheme == self._SCHEME_ROW_MAJOR:
            self.set_addr_map(bank_lsb=col_width, hash_en=0)
        elif scheme == self._SCHEME_BANK_INTERLEAVE:
            lsb = max(0, (burst_cols - 1).bit_length())   # log2 (burst_cols pow2)
            self.set_addr_map(bank_lsb=lsb, hash_en=0)
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
        self._wr("REFRESH_TUNING", page_policy_or=policy & 0x3)

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
            self._wr("REFRESH_TUNING", **kw)

    def set_refresh_interval(self, t_refi: int) -> None:
        """tREFI in MC cycles (TIMINGS_RFC_REFI.tREFI); rmw preserves tRFC."""
        self._wr("TIMINGS_RFC_REFI", tREFI=t_refi & 0xFFFF)

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
            self._wr("SCHED_TUNING", **kw)

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
