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
from typing import Optional

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

    def set_dfi_phase(self, rd_phase: int = 0, wr_phase: int = 0) -> None:
        self.write("DFI_PHASE", rd_phase=rd_phase, wr_phase=wr_phase)

    def set_page_policy(self, policy_or: int) -> None:
        """REFRESH_TUNING.page_policy_or (0=param default,1=OPEN,2=CLOSE,3=HYBRID)."""
        self.write("REFRESH_TUNING", rmw=True, page_policy_or=policy_or)

    def set_scheduler(self, **fields: int) -> None:
        """RMW SCHED_TUNING fields (force_inorder / lookahead_active / ...)."""
        self.write("SCHED_TUNING", rmw=True, **fields)

    def init_done(self) -> bool:
        return bool(self.field("STATUS", "init_done"))


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
