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
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from uart_axi_bridge import UARTAxiBridge  # noqa: E402
from TBClasses.harness.device import Device  # noqa: E402  (harness as its own named device)
from pumice_device import Pumice  # noqa: E402  (controller as its own named device)

# PeakRDL-generated regmap for this project's harness_csr (by-name access).
HARNESS_REGMAP = os.path.join(
    _REPO_ROOT, "projects/NexysA7/ddr2-characterization/"
    "ddr2_char_framework/dv/tbclasses/harness_csr_regmap.py")

# PeakRDL-generated regmap for the pumice controller CSR (APB slave, base 0x0
# in the bridge map). Used for by-name access to pumice's own runtime knobs
# (e.g. DFI_PHASE rd_phase/wr_phase). 12-bit APB address space, 32-bit data.
PUMICE_REGMAP = os.path.join(
    _REPO_ROOT, "projects/components/memory-controllers/"
    "pumice-ddr2-lpddr2/dv/tbclasses/pumice_regmap.py")


# =============================================================================
# Bridge address map (bridge_ddr2_char_axil.toml). 1 master x 4 slaves.
# =============================================================================
DDR2_APB_BASE     = 0x00000000  # pumice controller CSR (APB)
HARNESS_CSR_BASE  = 0x00010000  # this driver targets these regs
DEBUG_SRAM_BASE   = 0x00040000  # MonBus/DFI trace ring (256 KB @ AXIL64)
DFI_MON_RAM_BASE  = 0x00080000  # DFI cmd-only observability (4 KB)


# =============================================================================
# harness_csr / engine / perf registers are accessed BY NAME via the PeakRDL
# regmap (self.regs.write("CTRL", ...), self.regs.field("STATUS", "init_done")),
# so no register-offset constants live here — offsets come from
# harness_csr_regmap.py. See HARNESS_REGMAP above.
# =============================================================================
# a7ddrphy CSR knob word-INDICES (rtl-vivado/a7ddrphy/a7ddrphy_csr_map.txt).
# These are the indirect-passthrough knob VALUES written via phy_poke/phy_peek
# to the PHY_CSR_* registers (which are themselves addressed by name). The
# a7ddrphy is LiteDRAM's flat CSR — no RDL/regmap — so these stay as indices.
PHY_RST              = 0
PHY_DLY_SEL          = 1    # byte-lane select (x16 -> 2 lanes)
PHY_HALF_SYS8X_TAPS  = 2
PHY_WLEVEL_EN        = 3
PHY_WLEVEL_STROBE    = 4    # strobe
PHY_RDLY_DQ_RST      = 5    # strobe
PHY_RDLY_DQ_INC      = 6    # strobe
PHY_RDLY_DQ_BITSLIP_RST = 7  # strobe
PHY_RDLY_DQ_BITSLIP  = 8    # strobe
PHY_WDLY_DQ_BITSLIP_RST = 9  # strobe
PHY_WDLY_DQ_BITSLIP  = 10   # strobe
PHY_RDPHASE          = 11
PHY_WRPHASE          = 12


# =============================================================================
# Enumerations (mirroring pumice_pkg)
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

# ---- Controller runtime perf knobs (pumice CSR override fields; 0 = build
#      default). These select paging / scheduling / refresh behaviour live.
# Address-map scheme (ADDR_MAP_TUNING.scheme_or). Only ROW_MAJOR +
# BANK_INTERLEAVE are synthesized in the char build (XOR_HASH is not; read
# ADDR_MAP_TUNING.synth_mask_obs to confirm).
SCHEME_DEFAULT         = 0
SCHEME_ROW_MAJOR       = 1
SCHEME_BANK_INTERLEAVE = 2
SCHEME_XOR_HASH        = 3
# Page policy (REFRESH_TUNING.page_policy_or).
PAGE_POLICY_DEFAULT = 0
PAGE_POLICY_OPEN    = 1
PAGE_POLICY_CLOSE   = 2
PAGE_POLICY_HYBRID  = 3
# Per-bank/all-bank refresh policy (REFRESH_TUNING.refpb_policy_or).
REFPB_DEFAULT = 0
REFPB_RR      = 1
REFPB_OLDEST  = 2
REFPB_DARP    = 3


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
                 timeout: float = 1.0, bridge=None):
        """Open the harness driver.

        By default a real UART bridge is opened on `port`. Inject `bridge`
        (any object with read(addr)->int|None / write(addr,val)->bool) to
        drive the identical register traffic elsewhere — e.g. a cocotb UART
        channel in simulation, or a mock for board-less tests. All register
        access goes by name through `self.regs` (a harness Device), sourced
        from the PeakRDL-generated harness regmap — no hardcoded offsets.
        """
        self.bridge = bridge if bridge is not None else UARTAxiBridge(
            port=port, baudrate=baudrate, timeout=timeout)
        # char-harness CSR block as its own named Device (the hand-authored
        # regmap). By-name access via self.regs.<op> / self.regs.<REG>.<field>.
        self.regs = Device(self.bridge, "harness", regs_base=HARNESS_CSR_BASE,
                           regmap_file=HARNESS_REGMAP)
        # pumice controller CSR (APB slave) as its own named Device. Owns the
        # controller runtime knobs (DFI phase, paging, refresh, scheduler) by
        # name; the driver methods below delegate to it. 12-bit APB addr, 32b data.
        self.pumice = Pumice(self.bridge, "pumice", regs_base=DDR2_APB_BASE,
                             regmap_file=PUMICE_REGMAP)

    # ----- Low-level helpers (by name via the register map) ----------------
    def _rd64(self, lo_name: str, hi_name: str) -> int:
        return (self.regs.read(hi_name) << 32) | self.regs.read(lo_name)

    # ----- Identity + reset ------------------------------------------------
    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def scratch(self, val: Optional[int] = None) -> int:
        """Ping test — write then read back if `val` supplied."""
        if val is not None:
            self.regs.write_word("SCRATCH", val)
        return self.regs.read("SCRATCH")

    def clear_stats(self) -> None:
        """Pulse CTRL.clear_stats. Zeros the debug_sram write pointer,
        the sticky error latches, all bus-meter buckets, and the
        latency-histogram bins."""
        self.regs.write("CTRL", clear_stats=1)

    def soft_reset(self) -> None:
        self.regs.write("CTRL", soft_reset=1)

    def freeze_trace(self, on: bool = True) -> None:
        """Latch or unlatch CTRL.freeze_trace.

        NB: freeze_trace also freezes the perf meters/histograms (they
        share the perf_freeze wire from harness_csr). Turn it OFF before
        starting a new run. The other CTRL bits are self-clearing pulses,
        so writing only this field (the rest 0) leaves them inert.
        """
        self.regs.write("CTRL", freeze_trace=1 if on else 0)

    # ----- Controller runtime cfg -----------------------------------------
    def set_controller_cfg(self,
                           memtype:     int = MEMTYPE_DDR2,
                           t_phy_wrlat: int = 0,
                           t_rddata_en: int = 0,
                           rd_in_order: bool = False) -> None:
        """Program the controller's PHY timing + read ordering by name on the
        pumice controller CSR (bridge ddr2_apb window). The rearchitected
        controller no longer takes these as harness signals — config is
        CSR-driven, so this must land BEFORE init is released."""
        self.pumice.set_phy_timing(memtype=memtype, t_phy_wrlat=t_phy_wrlat,
                                   t_rddata_en=t_rddata_en)
        self.pumice.set_scheduler(force_inorder=rd_in_order)

    def set_controller_cap(self, cap_lookahead_max: int,
                           cap_synth_mask: int) -> None:
        self.regs.write("CTRLR_CAP",
                        cap_lookahead_max=cap_lookahead_max & 0xF,
                        cap_synth_mask=cap_synth_mask & 0xF)

    def set_dfi_cmd_delay(self, cmd_delay: int) -> None:
        """Real-time DFI command->write-data alignment (a7ddrphy
        write_latency=0). Sweep live over UART, no rebuild. Set while idle."""
        # rmw: DFI_TUNING also holds rddata_delay — preserve it.
        self.regs.write("DFI_TUNING", rmw=True, cmd_delay=cmd_delay & 0xF)

    def get_dfi_cmd_delay(self) -> int:
        return self.regs.field("DFI_TUNING", "cmd_delay")

    def set_dfi_rddata_delay(self, rddata_delay: int) -> None:
        """Real-time DFI read-data->rddata_valid alignment. The a7ddrphy presents
        read data ~read_latency sys-cycles before its rddata_valid; this delays
        dfi_rddata to meet the late valid so pumice captures the right beats.
        Set to the PHY read_latency (~8 for DDR2/CL3/nphases=2); 0=passthrough.
        Sweep live over UART, no rebuild. Set while idle."""
        # rmw: DFI_TUNING also holds cmd_delay — preserve it.
        self.regs.write("DFI_TUNING", rmw=True, rddata_delay=rddata_delay & 0xF)

    def get_dfi_rddata_delay(self) -> int:
        return self.regs.field("DFI_TUNING", "rddata_delay")

    # ----- Controller runtime knobs -- delegate to the Pumice device -------
    # These all live on the pumice controller CSR; the `Pumice` device
    # (pumice_device.py) owns the single by-name implementation. The driver
    # keeps these thin wrappers so existing callers (pumice_master / pumice_char)
    # are unchanged; `self.pumice.<op>` is equivalent.
    def set_dfi_phase(self, rd_phase: int, wr_phase: int = 0,
                      gear_ratio=None) -> None:
        self.pumice.set_dfi_phase(rd_phase, wr_phase, gear_ratio=gear_ratio)

    def get_dfi_phase(self) -> tuple:
        return self.pumice.get_dfi_phase()

    def set_addr_map_scheme(self, scheme: int) -> None:
        self.pumice.set_addr_map_scheme(scheme)

    def get_synth_scheme_mask(self) -> int:
        return self.pumice.get_synth_scheme_mask()

    def set_page_policy(self, policy: int) -> None:
        self.pumice.set_page_policy(policy)

    def set_refresh(self, *, refpb_policy: Optional[int] = None,
                    refresh_defer: Optional[int] = None,
                    zqcs_freq_hz: Optional[int] = None) -> None:
        self.pumice.set_refresh(refpb_policy=refpb_policy,
                                refresh_defer=refresh_defer,
                                zqcs_freq_hz=zqcs_freq_hz)

    def set_refresh_interval(self, t_refi: int) -> None:
        self.pumice.set_refresh_interval(t_refi)

    def set_scheduler(self, *, lookahead: Optional[int] = None,
                      force_inorder: Optional[bool] = None,
                      happy_enable: Optional[bool] = None,
                      age_max: Optional[int] = None,
                      txn_high_water: Optional[int] = None) -> None:
        self.pumice.set_scheduler(lookahead=lookahead, force_inorder=force_inorder,
                                  happy_enable=happy_enable, age_max=age_max,
                                  txn_high_water=txn_high_water)

    def get_lookahead_max(self) -> int:
        return self.pumice.get_lookahead_max()

    # ----- a7ddrphy calibration CSR (leveling knobs) ----------------------
    def phy_poke(self, knob: int, val: int = 1) -> None:
        """Write `val` to the a7ddrphy CSR word `knob` via the indirect
        passthrough (set ADDR + WDATA, then pulse CTRL). For strobe knobs
        (rdly_dq_inc etc.) the value is a 1-cycle pulse; pass val=1."""
        self.regs.write_word("PHY_CSR_ADDR",  knob & 0x3FF)
        self.regs.write_word("PHY_CSR_WDATA", val & 0xFFFFFFFF)
        self.regs.write("PHY_CSR_CTRL", pulse=1)

    def phy_peek(self, knob: int) -> int:
        """Read the a7ddrphy dat_r for CSR word `knob` (set ADDR, read RDATA)."""
        self.regs.write_word("PHY_CSR_ADDR", knob & 0x3FF)
        return self.regs.read("PHY_CSR_RDATA")

    # ----- Engine programming ---------------------------------------------
    def _program_engine(self, pfx: str, *, start_addr, stride_0, stride_1,
                        wrap_mask_0, wrap_mask_1, burst_len, txn_count, gap,
                        axi_id, id_mode, axi_size, axi_burst, data_mode,
                        lfsr_seed, hash_seed0, hash_seed1, hash_seed2) -> None:
        """Program one pattern engine's cfg registers by name (pfx = WR|RD)."""
        r = self.regs
        r.write_word(f"{pfx}_START_ADDR",  start_addr)
        r.write_word(f"{pfx}_STRIDE_0",    stride_0 & 0xFFFFFFFF)
        r.write_word(f"{pfx}_STRIDE_1",    stride_1 & 0xFFFFFFFF)
        r.write_word(f"{pfx}_WRAP_MASK_0", wrap_mask_0)
        r.write_word(f"{pfx}_WRAP_MASK_1", wrap_mask_1)
        r.write(f"{pfx}_BLEN_TXN", burst_len=burst_len, txn_count=txn_count, gap=gap)
        r.write(f"{pfx}_AXI_ATTR", axi_id=axi_id, id_mode=id_mode,
                axi_size=axi_size, axi_burst=axi_burst,
                data_mode=1 if data_mode else 0)
        r.write_word(f"{pfx}_LFSR_SEED",  lfsr_seed)
        r.write_word(f"{pfx}_HASH_SEED0", hash_seed0)
        r.write_word(f"{pfx}_HASH_SEED1", hash_seed1)
        r.write_word(f"{pfx}_HASH_SEED2", hash_seed2)

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
        self._program_engine(
            "WR", start_addr=start_addr, stride_0=stride_0, stride_1=stride_1,
            wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
            burst_len=burst_len, txn_count=txn_count, gap=gap,
            axi_id=axi_id, id_mode=id_mode, axi_size=axi_size,
            axi_burst=axi_burst, data_mode=data_mode, lfsr_seed=lfsr_seed,
            hash_seed0=hash_seed0, hash_seed1=hash_seed1, hash_seed2=hash_seed2)

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
        self._program_engine(
            "RD", start_addr=start_addr, stride_0=stride_0, stride_1=stride_1,
            wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
            burst_len=burst_len, txn_count=txn_count, gap=gap,
            axi_id=axi_id, id_mode=id_mode, axi_size=axi_size,
            axi_burst=axi_burst, data_mode=data_mode, lfsr_seed=lfsr_seed,
            hash_seed0=hash_seed0, hash_seed1=hash_seed1, hash_seed2=hash_seed2)

    # ----- Run control -----------------------------------------------------
    def start_wr(self) -> None:
        self.regs.write("CTRL", start_wr=1)

    def start_rd(self) -> None:
        self.regs.write("CTRL", start_rd=1)

    def start_both(self) -> None:
        self.regs.write("CTRL", start_wr=1, start_rd=1)

    def status(self) -> Status:
        f = self.regs.field
        s = self.regs.read("STATUS")
        return Status(
            wr_done        = bool(f("STATUS", "wr_done", s)),
            rd_done        = bool(f("STATUS", "rd_done", s)),
            wr_error       = bool(f("STATUS", "wr_error", s)),
            rd_error       = bool(f("STATUS", "rd_error", s)),
            any_error      = bool(f("STATUS", "any_error", s)),
            dbg_clear_busy = bool(f("STATUS", "dbg_clear_busy", s)),
            init_done      = bool(f("STATUS", "init_done", s)),
            init_fail      = bool(f("STATUS", "init_fail", s)),
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
        exp = self.regs.read("CRC_EXPECTED")
        act = self.regs.read("CRC_ACTUAL")
        m   = self.regs.read("CRC_MATCH")
        match = bool(self.regs.field("CRC_MATCH", "match", m))
        valid = bool(self.regs.field("CRC_MATCH", "exp_valid", m)
                     and self.regs.field("CRC_MATCH", "act_valid", m))
        return exp, act, match, valid

    def beats_mismatched(self) -> int:
        return self.regs.read("BEATS_MISM")

    # ----- Timer -----------------------------------------------------------
    def timer_clear(self) -> None:
        self.regs.write("TIMER_CTRL", clear=1)

    def set_timer_expected_beats(self, n: int) -> None:
        self.regs.write_word("TIMER_EXP_BEATS", n & 0xFFFFFFFF)

    def timer(self) -> TimerState:
        st = self.regs.read("TIMER_STATUS")
        return TimerState(
            done    = bool(self.regs.field("TIMER_STATUS", "done", st)),
            running = bool(self.regs.field("TIMER_STATUS", "running", st)),
            passed  = bool(self.regs.field("TIMER_STATUS", "pass", st)),
            cycles  = self._rd64("TIMER_CYCLES_LO", "TIMER_CYCLES_HI"),
            r_first = self._rd64("TIMER_R_FIRST_LO", "TIMER_R_FIRST_HI"),
            r_last  = self._rd64("TIMER_R_LAST_LO",  "TIMER_R_LAST_HI"),
            w_first = self._rd64("TIMER_W_FIRST_LO", "TIMER_W_FIRST_HI"),
            w_last  = self._rd64("TIMER_W_LAST_LO",  "TIMER_W_LAST_HI"),
        )

    # ----- Response-delay knobs (currently unwired on the RTL side; see
    #        harness_csr comment at 0x3C — kept here so a follow-up that
    #        instantiates axi_response_delay has the API in place). ----
    def set_resp_delay(self, rd_cycles: int, wr_cycles: int) -> None:
        self.regs.write("RESP_DELAY",
                        rd_delay=rd_cycles & 0xFFFF,
                        wr_delay=wr_cycles & 0xFFFF)

    # ----- Perf: bus meters -----------------------------------------------
    def perf_meters(self) -> Dict[str, MeterCounts]:
        r = self.regs.read
        rd = MeterCounts(prod=r("OBS_RD_PROD"), bp=r("OBS_RD_BP"),
                         starv=r("OBS_RD_STARV"), idle=r("OBS_RD_IDLE"))
        wr = MeterCounts(prod=r("OBS_WR_PROD"), bp=r("OBS_WR_BP"),
                         starv=r("OBS_WR_STARV"), idle=r("OBS_WR_IDLE"))
        return {"rd": rd, "wr": wr}

    # ----- Perf: latency histograms ---------------------------------------
    def _write_hist_sel(self, bus: int, metric: int, bin_idx: int) -> None:
        self.regs.write("OBS_HIST_SEL",
                        bus=bus & 1, metric=metric & 1, bin=bin_idx & 0xF)

    def perf_hist_bin(self, bus: int, metric: int, bin_idx: int
                      ) -> Tuple[int, int]:
        """Return (count, total) for the requested bin.

        `bus`     = HIST_BUS_RD or HIST_BUS_WR
        `metric`  = HIST_METRIC_0 (AR->firstR / AW->B) or HIST_METRIC_1
                    (AR->RLAST; WR side ignores)
        `bin_idx` = 0..15 (log2 latency bin b covers [2^b, 2^(b+1)) cycles)
        """
        self._write_hist_sel(bus, metric, bin_idx)
        return self.regs.read("OBS_HIST_COUNT"), self.regs.read("OBS_HIST_TOTAL")

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
        return self.regs.read("DBG_WR_PTR")

    def dbg_overflow(self) -> bool:
        return bool(self.regs.field("DBG_OVERFLOW", "overflow"))


def autodetect_port(baud: int = 115200, want: str = None) -> str:
    """Find the ttyUSB the pumice DDR2 char harness is on.

    The USB-UART re-enumerates across reboots/replugs, so never hardcode the
    port. Probe each candidate by reading BUILD_ID; the board that answers with
    the 'DDR2' magic (DDR2CharDriver.BUILD_ID_MAGIC) is ours. `want`: if the
    caller passed --port explicitly (not 'auto'), try it first. Mirrors the
    STREAM/RAPIDS/CDC char autodetect with the pumice identity register.
    """
    import glob
    cands = []
    if want and want != "auto":
        cands.append(want)
    cands += sorted(p for p in glob.glob("/dev/ttyUSB*") if p not in cands)

    for port in cands:
        try:
            d = DDR2CharDriver(port=port, baudrate=baud, timeout=0.4)
            ok = d.build_id() == DDR2CharDriver.BUILD_ID_MAGIC
            ser = getattr(d.bridge, "ser", None)
            if ser is not None:
                ser.close()
            if ok:
                print(f"[autodetect] pumice DDR2 char harness found on {port}")
                return port
        except Exception:
            continue
    raise SystemExit(
        f"[autodetect] no pumice DDR2 char harness responded on any of: "
        f"{cands or '(no /dev/ttyUSB* present)'}. "
        f"Is the board powered and programmed with the pumice DDR2 bitstream?")


# =============================================================================
# Quick CLI for one-shot smoke reads (dump_status.py style)
# =============================================================================
def _cli() -> None:
    import argparse
    p = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    p.add_argument("--port", default="auto")
    p.add_argument("--baud", type=int, default=115200)
    args = p.parse_args()

    args.port = autodetect_port(args.baud, want=args.port)
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
