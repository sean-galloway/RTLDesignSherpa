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

# Pull in the repo's shared UART client. Path setup is delegated to
# `pumice_env`, which locates every layer by searching for a marker file --
# so this module imports whether or not `env_python` has been sourced, and it
# does not name the bridge's directory. It used to demand REPO_ROOT and insert
# `projects/components/converters/bin` by hand; the bridge has since moved into
# the shared FPGA layer, and a hardcoded path would now point at nothing.
sys.path.insert(0, os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bin")))
import pumice_env  # noqa: F401,E402  (import side effect: sys.path setup)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
_REPO_ROOT = pumice_env.repo_root()

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

# PeakRDL-generated regmap for the traffic generators (chargen_regs, APB slave
# at 0x000A0000). Sixteen generators -- eight writers and eight readers, one per
# DRAM bank -- each with its own config block. This used to live in harness_csr
# as a single WR_*/RD_* window; that window configured ONE writer and ONE
# reader and is retired.
CHARGEN_REGMAP = os.path.join(
    _REPO_ROOT, "projects/NexysA7/ddr2-characterization/"
    "ddr2_char_framework/dv/tbclasses/chargen_regs_regmap.py")


# =============================================================================
# Bridge address map (bridge_ddr2_char_axil.toml). 1 master x 6 slaves.
# =============================================================================
DDR2_APB_BASE     = 0x00000000  # pumice controller CSR (APB)
HARNESS_CSR_BASE  = 0x00010000  # harness control / timer / perf / identity
DEBUG_SRAM_BASE   = 0x00040000  # MonBus/DFI trace ring (256 KB @ AXIL64)
DFI_MON_RAM_BASE  = 0x00080000  # DFI cmd-only observability (4 KB)
OBS_APB_BASE      = 0x00090000  # reserved for the external AXI observer
CHARGEN_APB_BASE  = 0x000A0000  # traffic-generator config (chargen_regs)


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
# 3 was PAGE_POLICY_HYBRID -- retired (maps to build default in RTL); the
# adaptive policies are PAGE_POLICY_CFG.policy_mode via set_page_mode().
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
        # Legal-AxLEN quantum (AXI beats per DRAM burst): program_wr/rd_engine
        # rejects a burst_len that is not a nonzero multiple of this, so one AXI
        # burst always maps to an integer number of DRAM bursts (else the HW
        # SLVERRs / partial-transfers and the read-back mismatches). Mirrors the
        # RTL BURST_LEN_MULTIPLE param. Board (BL8 x16 host-64) = 2; 1 disables.
        self.burst_len_multiple = 1
        # pumice controller CSR (APB slave) as its own named Device. Owns the
        # controller runtime knobs (DFI phase, paging, refresh, scheduler) by
        # name; the driver methods below delegate to it. 12-bit APB addr, 32b data.
        self.pumice = Pumice(self.bridge, "pumice", regs_base=DDR2_APB_BASE,
                             regmap_file=PUMICE_REGMAP)
        # Traffic generators as their own named Device. Sixteen of them -- see
        # CHARGEN_REGMAP. Register names carry the index (WR_GEN3_START_ADDR),
        # so the driver builds the name from a generator argument and nothing
        # here computes an offset.
        self.chargen = Device(self.bridge, "chargen",
                              regs_base=CHARGEN_APB_BASE,
                              regmap_file=CHARGEN_REGMAP)
        #: How many generators this bitstream was built with, per direction.
        #: ONE. The array went 8 -> 4 -> 2 -> 1 chasing timing; 2+2 showed
        #: generator count was never the limiter (slice occupancy is), so the
        #: crossbars were deleted. Read from the
        #: hardware by :meth:`gen_config` rather than assumed: a host that
        #: programs more generators than exist silently measures something
        #: other than what it reports.
        self.num_gen = 1

    # ----- Low-level helpers (by name via the register map) ----------------
    def _rd64(self, lo_name: str, hi_name: str) -> int:
        return (self.regs.read(hi_name) << 32) | self.regs.read(lo_name)

    # ----- Identity + reset ------------------------------------------------
    def build_id(self) -> int:
        return self.regs.read("BUILD_ID")

    def build_info(self) -> Dict[str, int]:
        """What this bitstream actually IS, read from the board.

        BUILD_ID says only that the harness is a DDR2 one. Everything a host
        needs in order to drive it correctly -- DFI rate, gear ratio, JEDEC
        burst length, geometry, data widths -- used to be supplied out of band:
        by environment variable in sim, by assumption on silicon. When the
        assumption was wrong the read path returned garbage, which looks like a
        timing bug rather than a configuration mismatch.

        These are elaboration-time constants driven from the harness's own
        parameters, so they cannot drift from the hardware. Reading them turns
        "is this the bitstream I think it is" into a comparison.
        """
        return {
            "build_id":          self.regs.read("BUILD_ID"),
            "version":           self.regs.read("BUILD_VERSION"),
            "dfi_rate":          self.regs.field("BUILD_CONFIG", "dfi_rate"),
            "gear_ratio":        self.regs.field("BUILD_CONFIG", "gear_ratio"),
            "dram_bl":           self.regs.field("BUILD_CONFIG", "dram_bl"),
            "row_width":         self.regs.field("BUILD_CONFIG", "row_width"),
            "bank_width":        self.regs.field("BUILD_CONFIG", "bank_width"),
            "axi_data_width":    self.regs.field("BUILD_DATA_CFG", "axi_data_width"),
            "dram_beat_width":   self.regs.field("BUILD_DATA_CFG", "dram_beat_width"),
            "dram_device_width": self.regs.field("BUILD_DATA_CFG", "dram_device_width"),
        }

    def describe_build(self) -> str:
        """One-line summary of what is on the board, for logs and failures."""
        b = self.build_info()
        tag = "".join(chr((b["build_id"] >> s) & 0xFF) for s in (24, 16, 8, 0))
        return (f"{tag} v{b['version']} "
                f"dfi_rate={b['dfi_rate']} gear={b['gear_ratio']} "
                f"bl={b['dram_bl']} row={b['row_width']} bank={b['bank_width']} "
                f"axi={b['axi_data_width']}b beat={b['dram_beat_width']}b "
                f"dev={b['dram_device_width']}b")

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

    # ----- Build geometry --------------------------------------------------
    # The bitstream is built for ONE DFI rate / burst geometry; the CSRs only
    # tell the controller which one it is running. CTRL.soft_reset wipes the
    # pumice CSRs back to their RTL resets -- which are the 1:4 / BL8 values,
    # NOT this build's -- so every soft_reset silently reverts the geometry
    # unless it is re-programmed. Nine host scripts each re-programmed it (or
    # forgot to) at their own call sites; wide_rd_sweep.py forgot, ran the whole
    # sweep at 1:4/BL8 on a 1:2/BL4 build, and reported the resulting
    # never-completed reads as beats_mismatched=0 -- a clean sweep that measured
    # nothing. So restoring geometry is the driver's job, not the caller's.
    BOARD_GEAR_RATIO = int(os.environ.get("TEST_GEAR_RATIO", "1"))   # log2(1:2)
    BOARD_DRAM_BL    = int(os.environ.get("TEST_DRAM_BL", "4"))      # JEDEC BL4
    BOARD_MR0        = int(os.environ.get("TEST_MR0", "0x0432"), 0)  # BL4/CL3/tWR3
    # One JEDEC DRAM burst in COLUMN-ADDRESS units. The column address is
    # DEVICE-WORD granular (addr_mapper BYTE_OFFSET_WIDTH = clog2(DEVICE/8),
    # the x16 column-stride fix), so a burst spans exactly BL column units --
    # BL is already counted in JEDEC device beats. The old formula here
    # (BL*DEVICE/BEAT, "pumice-beat column units") halved this on the x16
    # board: burst_cols=2 -> bank_lsb=1 put the bank field INSIDE the burst's
    # column span, striping every BL4 burst across banks -- bank_interleave
    # 32000/32000 beats mismatched on silicon (2026-08-25) while the
    # device==beat sim passed, because there the two formulas coincide.
    # Sim repro: test_ddr2_char_char_families_x16.
    BOARD_BURST_COLS = BOARD_DRAM_BL

    def program_geometry(self, rd_phase: int = 0, wr_phase: int = 0,
                         restart_init: bool = True) -> None:
        """Program the DFI/burst geometry this bitstream was built for.

        restart_init pulses CTRL.init_force_restart so the MRS chain re-runs
        with the MR0 just written -- without it the DRAM keeps the burst length
        from the reset-value init that soft_reset already kicked off.
        """
        self.set_dfi_phase(rd_phase=rd_phase, wr_phase=wr_phase,
                           gear_ratio=self.BOARD_GEAR_RATIO,
                           bl=self.BOARD_DRAM_BL)
        self.set_mr0(self.BOARD_MR0)
        if restart_init:
            self.init_restart()

    def soft_reset(self, restore_geometry: bool = True,
                   rd_phase: int = 0, wr_phase: int = 0) -> None:
        """Pulse CTRL.soft_reset, then restore the build geometry.

        Pass restore_geometry=False only to observe the raw reset state.
        """
        self.regs.write("CTRL", soft_reset=1)
        # The reset just reverted every pumice CSR to its RTL default — drop
        # the write-through shadow so subsequent shadowed writes re-seed from
        # the RDL resets instead of pre-reset values.
        self.pumice.invalidate_shadow()
        if restore_geometry:
            time.sleep(0.005)
            self.program_geometry(rd_phase=rd_phase, wr_phase=wr_phase)

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

    def set_mr(self, index: int, value: int) -> None:
        """Program a DDR2 mode-register value (MR0..MR3) for the init MRS chain.
        Applied on the next init run — call init_restart() after to re-run init."""
        self.pumice.set_mr(index, value)

    def set_mr0(self, value: int) -> None:
        self.pumice.set_mr0(value)

    def init_restart(self) -> None:
        """Re-run the JEDEC MRS init WITHOUT a controller reset (CTRL.init_force_
        restart), applying freshly-written MRx.VAL while CSRs are preserved. Use
        to sweep MR0 against an arbitrary board A-lane mapping: set_mr0(v);
        init_restart(); then check reads."""
        self.pumice.init_restart()


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
                      gear_ratio=None, bl=None) -> None:
        # bl = JEDEC burst length (device beats), the single source of truth for
        # the sub-DFI-word framing (task #146). None => preserve the CSR reset.
        self.pumice.set_dfi_phase(rd_phase, wr_phase, gear_ratio=gear_ratio,
                                  bl=bl)

    def get_dfi_phase(self) -> tuple:
        return self.pumice.get_dfi_phase()

    def set_addr_map_scheme(self, scheme: int) -> None:
        self.pumice.set_addr_map_scheme(scheme,
                                        burst_cols=max(1, self.BOARD_BURST_COLS))

    def get_synth_scheme_mask(self) -> int:
        return self.pumice.get_synth_scheme_mask()

    def set_page_policy(self, policy: int) -> None:
        self.pumice.set_page_policy(policy)

    def set_page_mode(self, mode: int, tr_init: Optional[int] = None) -> None:
        self.pumice.set_page_mode(mode, tr_init=tr_init)

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
                      age_max: Optional[int] = None,
                      txn_high_water: Optional[int] = None) -> None:
        self.pumice.set_scheduler(lookahead=lookahead, force_inorder=force_inorder,
                                  age_max=age_max,
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
                        lfsr_seed, hash_seed0, hash_seed1, hash_seed2,
                        gen: int = 0) -> None:
        """Stage one generator's config by name (pfx = WR|RD, gen = 0..7).

        Staging only -- this does NOT start anything. Launch is :meth:`go`,
        which starts every selected generator on one cycle. The two are
        separate because staging takes many bus transactions and launching
        must not: a per-generator start would leave generator 0 running for
        however long it took to program generator 7.
        """
        if not 0 <= gen < self.num_gen:
            raise IndexError(
                f"generator {gen} out of range 0..{self.num_gen - 1}. The "
                f"array is sized to the device's bank count; read gen_config() "
                f"to see what this bitstream was actually built with.")
        q = getattr(self, "burst_len_multiple", 1)
        if q > 1 and (burst_len == 0 or burst_len % q != 0):
            raise ValueError(
                f"{pfx} burst_len={burst_len} must be a nonzero multiple of the "
                f"DRAM-burst quantum ({q} AXI beats/DRAM burst): one AXI burst "
                f"must map to an integer number of DRAM bursts, else the HW "
                f"SLVERRs / partial-transfers. Use a multiple of {q}, or set "
                f"driver.burst_len_multiple=1 to disable this guard.")
        r = self.chargen
        n = f"{pfx}_GEN{gen}"
        r.write_word(f"{n}_START_ADDR",  start_addr)
        r.write_word(f"{n}_STRIDE_0",    stride_0 & 0xFFFFFF)
        r.write_word(f"{n}_STRIDE_1",    stride_1 & 0xFFFFFF)
        r.write_word(f"{n}_WRAP_MASK_0", wrap_mask_0)
        r.write_word(f"{n}_WRAP_MASK_1", wrap_mask_1)
        r.write(f"{n}_BLEN_TXN", burst_len=burst_len, txn_count=txn_count, gap=gap)
        r.write(f"{n}_AXI_ATTR", axi_id=axi_id, id_mode=id_mode,
                axi_size=axi_size, axi_burst=axi_burst,
                data_mode=1 if data_mode else 0)
        r.write_word(f"{n}_LFSR_SEED",  lfsr_seed)
        r.write_word(f"{n}_HASH_SEED0", hash_seed0)
        r.write_word(f"{n}_HASH_SEED1", hash_seed1)
        r.write_word(f"{n}_HASH_SEED2", hash_seed2)

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
                          hash_seed2:    int = 0,
                          gen:           int = 0) -> None:
        self._program_engine(
            "WR", gen=gen,
            start_addr=start_addr, stride_0=stride_0, stride_1=stride_1,
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
                          hash_seed2:    int = 0,
                          gen:           int = 0) -> None:
        self._program_engine(
            "RD", gen=gen,
            start_addr=start_addr, stride_0=stride_0, stride_1=stride_1,
            wrap_mask_0=wrap_mask_0, wrap_mask_1=wrap_mask_1,
            burst_len=burst_len, txn_count=txn_count, gap=gap,
            axi_id=axi_id, id_mode=id_mode, axi_size=axi_size,
            axi_burst=axi_burst, data_mode=data_mode, lfsr_seed=lfsr_seed,
            hash_seed0=hash_seed0, hash_seed1=hash_seed1, hash_seed2=hash_seed2)

    # ----- Run control -----------------------------------------------------
    # Launch is one write to GO in chargen_regs, not the harness CTRL bits
    # (which are retired). Every generator selected in that write starts on the
    # same cycle. The single-generator methods keep their old names and shape so
    # existing bring-up scripts read unchanged; they simply select generator 0.

    def go(self, wr_mask: int = 0, rd_mask: int = 0) -> None:
        """Start the selected generators -- one write, one start edge.

        Masks are bit-per-generator: 0x01 is generator 0, 0xFF is all eight.
        Staging every generator first and then launching them together is the
        whole reason GO exists as one register; a per-generator start puts the
        first generator minutes ahead of the last over a UART, which is how a
        measurement window ends up describing mostly idle time.
        """
        limit = 1 << self.num_gen
        if not 0 <= wr_mask < limit:
            raise ValueError(f"wr_mask 0x{wr_mask:X} exceeds {self.num_gen} generators")
        if not 0 <= rd_mask < limit:
            raise ValueError(f"rd_mask 0x{rd_mask:X} exceeds {self.num_gen} generators")
        fields = {}
        for i in range(self.num_gen):
            if wr_mask >> i & 1:
                fields[f"wr_go{i}"] = 1
            if rd_mask >> i & 1:
                fields[f"rd_go{i}"] = 1
        if not fields:
            return
        # One register write: the bits are separate FIELDS only because
        # singlepulse must be one bit wide, not because they are separate
        # events.
        self.chargen.write("GO", **fields)

    def start_wr(self, mask: int = 0x01) -> None:
        self.go(wr_mask=mask)

    def start_rd(self, mask: int = 0x01) -> None:
        self.go(rd_mask=mask)

    def start_both(self, wr_mask: int = 0x01, rd_mask: int = 0x01) -> None:
        self.go(wr_mask=wr_mask, rd_mask=rd_mask)

    def gen_config(self) -> Dict[str, int]:
        """Generator array shape as BUILT, read from the board.

        Worth reading rather than assuming: the count the host programs and the
        count that was synthesized are different numbers, and when they
        disagree the run measures something other than what it reports.
        """
        v = self.chargen.read("GEN_CONFIG")
        f = self.chargen.field
        return {
            "num_wr_gen": f("GEN_CONFIG", "num_wr_gen", v),
            "num_rd_gen": f("GEN_CONFIG", "num_rd_gen", v),
            "num_banks":  f("GEN_CONFIG", "num_banks",  v),
        }

    def gen_done(self) -> Tuple[int, int]:
        """(wr_done_mask, rd_done_mask) -- one read instead of sixteen."""
        v = self.chargen.read("DONE")
        f = self.chargen.field
        return f("DONE", "wr_done", v), f("DONE", "rd_done", v)

    def gen_errors(self) -> Tuple[int, int]:
        """(writer bresp-error mask, reader any-error mask)."""
        v = self.chargen.read("ERRORS")
        f = self.chargen.field
        return f("ERRORS", "wr_bresp_error", v), f("ERRORS", "rd_any_error", v)

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
    def crc(self, gen: int = 0) -> Tuple[int, int, bool, bool]:
        """Return (expected, actual, match, both_valid) for one matched pair.

        Reads the pair's own CRC registers in chargen_regs. harness_csr's old
        CRC_EXPECTED / CRC_ACTUAL are retired and read 0 -- with eight pairs a
        single pair of registers described nothing.
        """
        exp = self.chargen.read(f"WR_GEN{gen}_EXPECTED_CRC")
        act = self.chargen.read(f"RD_GEN{gen}_ACTUAL_CRC")
        wr_st = self.chargen.read(f"WR_GEN{gen}_STATUS")
        rd_st = self.chargen.read(f"RD_GEN{gen}_STATUS")
        valid = bool(self.chargen.field(f"WR_GEN{gen}_STATUS", "crc_valid", wr_st)
                     and self.chargen.field(f"RD_GEN{gen}_STATUS", "crc_valid", rd_st))
        return exp, act, (exp == act and valid), valid

    def crc_all(self) -> Dict[int, Tuple[int, int, bool, bool]]:
        """Every pair's CRC, keyed by generator index.

        The single-pair `crc()` cannot answer "did the run pass" once more than
        one pair is launched, and a caller that checks only pair 0 will report
        a clean run while seven others corrupted.
        """
        return {g: self.crc(g) for g in range(self.num_gen)}

    def run_crc_match(self) -> bool:
        """Whole-run integrity, as the hardware itself computes it.

        This is harness_csr's CRC_MATCH bit, which the macro drives from a
        comparison of every LAUNCHED pair -- so it covers the pairs that
        actually ran and no others, and it does not depend on the host
        knowing which those were.
        """
        m = self.regs.read("CRC_MATCH")
        return bool(self.regs.field("CRC_MATCH", "match", m))

    def beats_mismatched(self, gen: int = 0) -> int:
        """Mismatching R beats counted by reader `gen`."""
        return self.chargen.read(f"RD_GEN{gen}_BEATS_MISM")

    def stray_beats(self, gen: int = 0) -> int:
        """Extra R beats (no outstanding AR) counted by reader `gen`."""
        return self.chargen.read(f"RD_GEN{gen}_STRAY_BEATS")

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


def _fpga_bin() -> str:
    """The shared board/UART layer, for callers who run these host tools
    without sourcing env_python.

    Delegates to `pumice_env.fpga_bin()` rather than repeating the search. This
    file used to carry its own copy keyed on the literal path `fpga/bin`; when
    the layer moved, the copy broke independently of the original, which is the
    whole argument against a second implementation.
    """
    here = os.path.dirname(os.path.abspath(__file__))
    seq_bin = os.path.abspath(os.path.join(here, "..", "..", "bin"))
    if seq_bin not in sys.path:
        sys.path.insert(0, seq_bin)
    import pumice_env  # noqa: E402  (also sets up sys.path as a side effect)

    return pumice_env.fpga_bin()


def harness_probe():
    """Predicate that answers "is this link the pumice DDR2 char harness?".

    Reads BUILD_ID by name (never a hardcoded offset) and compares it to the
    'DDR2' magic. Exposed so board-aware callers can combine it with a
    USB-serial filter -- `Board.find_uart_port(probe=harness_probe())` -- which
    the bare port scan below cannot do.
    """
    def probe(link) -> bool:
        return DDR2CharDriver(bridge=link.bridge()).build_id() == \
            DDR2CharDriver.BUILD_ID_MAGIC
    return probe


def autodetect_port(baud: int = 115200, want: str = None) -> str:
    """Find the ttyUSB the pumice DDR2 char harness is on.

    The USB-UART re-enumerates across reboots/replugs, so never hardcode the
    port. Thin wrapper over the shared `uart_link.find_port` probe loop (which
    replaced four hand-rolled copies of this scan); the pumice-specific part is
    only `harness_probe()`. Kept as a module-level function because the host
    entrypoints (run_smoke, pumice_master, sweeps) all import it by this name.

    Prefer `Board.find_uart_port(probe=harness_probe())` in new code: it also
    narrows to one board's ports by USB serial, which matters when the Nexys A7
    and the Genesys 2 are both attached.
    """
    if _fpga_bin() not in sys.path:
        sys.path.insert(0, _fpga_bin())
    from uart_link import find_port  # noqa: E402

    return find_port(probe=harness_probe(), want=want, baudrate=baud,
                     label="pumice DDR2 char harness")


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
