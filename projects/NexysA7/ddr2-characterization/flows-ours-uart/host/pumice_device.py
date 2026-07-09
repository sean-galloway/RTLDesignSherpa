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
    def set_dfi_phase(self, rd_phase: int, wr_phase: int = 0) -> None:
        """Place the READ/WRITE DFI commands on given sub-phases (a7ddrphy
        rdphase/wrphase contract). DFI_PHASE @ APB 0x060; set while idle."""
        self.regs.write("DFI_PHASE", rd_phase=rd_phase & 0x7,
                        wr_phase=wr_phase & 0x7)

    def get_dfi_phase(self) -> tuple:
        return (self.regs.field("DFI_PHASE", "rd_phase"),
                self.regs.field("DFI_PHASE", "wr_phase"))

    # ----- address map / paging --------------------------------------------
    def set_addr_map_scheme(self, scheme: int) -> None:
        """ADDR_MAP_TUNING.scheme_or (ROW_MAJOR / BANK_INTERLEAVE; DEFAULT =
        build-time). XOR_HASH may not be synthesized (see get_synth_scheme_mask)."""
        self.regs.write("ADDR_MAP_TUNING", scheme_or=scheme & 0x3)

    def get_synth_scheme_mask(self) -> int:
        """Bitmask of synthesized schemes: b0=ROW_MAJOR, b1=BANK_INTERLEAVE,
        b2=XOR_HASH."""
        return self.regs.field("ADDR_MAP_TUNING", "synth_mask_obs")

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
