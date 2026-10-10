# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""One scoria DDR3/LPDDR3 controller instance, addressed by name.

The controller half of the scoria characterization stack. Adapted from
pumice_device.Pumice: the shadowed-write discipline, the by-name field access
and the setter shapes are all carried over deliberately, because they encode
board failures that cost real time and are not DDR2-specific.

What is NOT carried over, and why:

  set_addr_map_scheme()   pumice's addr_map scheme mux was retired; only
                          ADDR_MAP.bank_lsb moves. scoria never had the mux,
                          so the method would be a setter for a field that
                          does not exist.
  DDR2 memtype defaults   scoria's memtype_e is DDR3/LPDDR3, so MEMTYPE=0
                          means DDR3 here and DDR2 there. Same encoding,
                          different meaning -- see mem_char_pkg.

What is NEW, because DDR3 is:

  set_zq()                periodic ZQCS. DDR2 has no ZQ command at all.
  zq_status()             including obs_overdue, which is the only way to see
                          the scheduler starving calibration.
  set_write_leveling()    DDR3 adds write leveling; the SEARCH runs here in
                          the host, not in RTL (scoria design decision D2).
  wrlvl_status()          four outcomes must be distinguishable: never
                          attempted, converged, timed out, swept with no flip.
  set_init_timing2()      tXPR and tZQinit, the two init waits DDR3 adds.
"""
from __future__ import annotations

import os
import sys
from typing import Dict, Optional

_REPO = os.environ.get("REPO_ROOT") or os.popen(
    "git rev-parse --show-toplevel").read().strip()
sys.path.insert(0, os.path.join(_REPO, "bin"))

from TBClasses.harness.device import Device   # noqa: E402

#: scoria controller CSR, generated from scoria_csr.rdl. By NAME, never by
#: offset -- offsets churn (the DDR3 block landed at 0x0C0-0x0E4 and STALL_ZQ
#: at 0x180 only because 0x17C was taken).
SCORIA_REGMAP = os.path.join(
    _REPO, "projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3",
    "regs/generated/scoria_csr_regmap.py")

#: Bridge address map. Mirrors pumice's layout so the shared harness_csr and
#: chargen blocks keep their bases and the host code for them is unchanged.
SCORIA_APB_BASE = 0x0000_0000   # scoria controller CSR
HARNESS_CSR_BASE = 0x0001_0000  # shared char-harness control block
CHARGEN_APB_BASE = 0x000A_0000  # shared traffic generators

# memtype_e, scoria_pkg. NOT interchangeable with pumice's despite the
# identical encoding: 0 is DDR2 there and DDR3 here.
MEMTYPE_DDR3 = 0
MEMTYPE_LPDDR3 = 1


class Scoria(Device):
    """A scoria controller, addressed by name.

    Every register is reachable by name via the inherited `dev.<REG>.<field>`
    sugar; the setters below exist for the multi-field registers where
    bit-packing by hand is how a leveling sweep silently runs at reset timing.
    """

    # ----- shadowed writes --------------------------------------------------
    # Carried over from pumice unchanged, and the reason is worth repeating
    # rather than assuming it does not apply: on the board, the bridge's
    # controller APB window returned a PRIOR transaction's data on reads
    # (request/response misalignment; the harness window was fine), so a
    # read-modify-write spliced stale garbage into every field it meant to
    # preserve -- and the corruption depended on preceding UART traffic, which
    # made whole leveling sweeps run at reset timing without a symptom.
    #
    # So NO controller write may ever rmw. Every setter goes through a
    # host-side write-through shadow: seeded from the RDL reset default, fields
    # spliced in, the FULL word written. This is untested on scoria's bridge
    # because that bridge does not exist yet -- it is retained as the safe
    # default, not as a claim the defect is present.
    #
    # invalidate_shadow() must be called after anything that reverts the CSRs
    # to reset. CTRL.soft_reset does.
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

    # ===== DDR3 additions ===================================================

    def set_init_timing2(self, *, t_xpr_wait: Optional[int] = None,
                         t_zqinit_wait: Optional[int] = None) -> None:
        """The two init waits DDR3 adds (JESD79-3F steps 5 and 11).

        Both in MC cycles, like every enforced timing in this map. Step 11
        waits the LONGER of tDLLK and tZQinit, which the sequencer does in
        hardware -- programming tZQinit shorter than tDLLK is therefore inert
        rather than dangerous.
        """
        f = {}
        if t_xpr_wait is not None:
            f["t_xpr_wait"] = t_xpr_wait
        if t_zqinit_wait is not None:
            f["t_zqinit_wait"] = t_zqinit_wait
        if f:
            self._wr("INIT_TIMING2", **f)

    def set_zq(self, *, enable: Optional[int] = None,
               t_zqcs: Optional[int] = None,
               interval: Optional[int] = None) -> None:
        """Periodic ZQCS. DDR2 has no ZQ command, so this is entirely new.

        `interval` is 32 bits in its own register on purpose: a ~128 ms
        interval at 100 MHz is ~12.8M cycles, which does not fit the 16 bits
        tREFI uses. interval 0 means DISABLED, not "as fast as possible".

        ZQ is maintenance traffic and sits BELOW refresh in the arbiter, so
        enabling it cannot starve refresh. It can itself be starved -- read
        zq_status()["overdue"] rather than assuming it is running.
        """
        f = {}
        if enable is not None:
            f["zq_enable"] = enable
        if t_zqcs is not None:
            f["t_zqcs"] = t_zqcs
        if f:
            self._wr("ZQ_CFG", **f)
        if interval is not None:
            self._wr("ZQ_INTERVAL", zq_interval=interval)

    def zq_status(self) -> Dict[str, int]:
        """ZQ telemetry, including the live countdown.

        `overdue` is the load-bearing one: the interval expired and the
        scheduler has not granted. Without it, zqcs_total advancing is the
        only evidence ZQ runs at all, and that says nothing about a controller
        stuck at ZQ_REQ.
        """
        return {
            "total": self.regs.read("ZQ_STATUS.zqcs_total"),
            "busy": self.regs.read("ZQ_STATUS.zq_busy"),
            "overdue": self.regs.read("ZQ_STATUS.zq_overdue"),
            "interval_cnt": self.regs.read("ZQ_OBS_INTERVAL.zq_interval_cnt"),
        }

    def set_write_leveling(self, *, strobe: Optional[int] = None,
                           cs_sel: Optional[int] = None,
                           t_wldqsen: Optional[int] = None,
                           t_wlmrd: Optional[int] = None,
                           t_wlmrd_max: Optional[int] = None,
                           t_wlo: Optional[int] = None,
                           t_wloe: Optional[int] = None) -> None:
        """Write-leveling interface. The SEARCH is the host's (decision D2).

        `strobe` is a singlepulse field: writing 1 emits exactly ONE DQS edge
        and self-clears. Do not hold it -- as a plain level it produced a
        strobe TRAIN, because the RTL leaves WL_READY the cycle it sees the
        strobe and returns there after tWLO, so the sweep would level against
        an edge the host did not place.

        t_wlmrd_max is OURS, not JEDEC: JESD79-3F declares tWLMRD's maximum
        controller-dependent, so it is a timeout here. 0 disables it.
        t_wloe is accepted and INERT -- we sample the prime DQ bit only.
        """
        cfg = {}
        if cs_sel is not None:
            cfg["wrlvl_cs_sel"] = cs_sel
        if cfg:
            self._wr("WRLVL_CFG", **cfg)
        t0, t1, t2 = {}, {}, {}
        if t_wldqsen is not None:
            t0["t_wldqsen"] = t_wldqsen
        if t_wlmrd is not None:
            t0["t_wlmrd"] = t_wlmrd
        if t_wlmrd_max is not None:
            t1["t_wlmrd_max"] = t_wlmrd_max
        if t_wlo is not None:
            t1["t_wlo"] = t_wlo
        if t_wloe is not None:
            t2["t_wloe"] = t_wloe
        if t0:
            self._wr("WRLVL_TIMING0", **t0)
        if t1:
            self._wr("WRLVL_TIMING1", **t1)
        if t2:
            self._wr("WRLVL_TIMING2", **t2)
        # strobe LAST, and never through the shadow: it is singlepulse, so a
        # shadowed word would re-assert it on the next unrelated WRLVL_CFG
        # write and emit a stray DQS edge.
        if strobe:
            self.regs.write("WRLVL_CFG.wrlvl_strobe", 1)

    def wrlvl_strobe(self) -> None:
        """Emit exactly one DQS edge. See set_write_leveling on singlepulse."""
        self.regs.write("WRLVL_CFG.wrlvl_strobe", 1)

    def wrlvl_status(self) -> Dict[str, int]:
        """Write-leveling telemetry.

        Four outcomes must stay distinguishable and this returns all of them:
        never attempted (attempts 0), converged (result_valid, flips > 0),
        timed out (timeout), and swept with no flip (attempts > 0, flips 0) --
        the last being the one a naive "did it finish" check reports as success.

        mr_wr and wrlvl_en are the controller's decode of MR0[11:9] and MR1[7],
        so they cross-check the host's own idea of what it programmed.
        """
        return {
            "attempts": self.regs.read("WRLVL_STATUS0.wrlvl_attempts"),
            "flips": self.regs.read("WRLVL_STATUS0.wrlvl_flips"),
            "result": self.regs.read("WRLVL_STATUS1.wrlvl_result"),
            "result_valid": self.regs.read("WRLVL_STATUS1.wrlvl_result_valid"),
            "timeout": self.regs.read("WRLVL_STATUS1.wrlvl_timeout"),
            "ever_done": self.regs.read("WRLVL_STATUS1.wrlvl_ever_done"),
            "state": self.regs.read("WRLVL_STATUS1.wrlvl_state"),
            "mr_wr": self.regs.read("WRLVL_STATUS1.mr_wr"),
            "wrlvl_en": self.regs.read("WRLVL_STATUS1.wrlvl_en"),
        }

    # ===== inherited-shape knobs ============================================

    def set_mr(self, index: int, value: int) -> None:
        """Write one mode register shadow (MR0..MR3).

        DDR3 uses all four; DDR2 used MR0-MR2 plus EMRS3. MR2 carries CWL on
        DDR3, which is why CWL is a real decode in the RTL rather than CL-1.
        """
        if not 0 <= index <= 3:
            raise ValueError(f"MR index {index} out of range 0..3")
        self._wr(f"MR{index}", **{"VAL": value})

    def init_restart(self) -> None:
        """Force a re-init from the top of the JEDEC sequence."""
        self.regs.write("CTRL.init_force_restart", 1)

    def init_done(self) -> bool:
        return bool(self.regs.read("STATUS.init_done"))

    def set_refresh_interval(self, t_refi: int) -> None:
        self._wr("TIMINGS_RFC_REFI", tREFI=t_refi)

    def stall_reasons(self) -> Dict[str, int]:
        """Every stall bucket, including STALL_ZQ.

        STALL_ZQ exists because without it ZQ waits fall through the
        stall-reason chain into STALL_BANKTIMER, whose whole claim is that it
        names a per-bank tRCD/tRP/tRAS block -- a misattributed bucket reads as
        a real timing problem on a part that has none.
        """
        names = ("BP", "REFRESH", "TURNAROUND", "TCCD", "ACTLIMIT",
                 "BANKTIMER", "NOREQ", "ZQ")
        return {n.lower(): self.regs.read(f"STALL_{n}.VAL") for n in names}
