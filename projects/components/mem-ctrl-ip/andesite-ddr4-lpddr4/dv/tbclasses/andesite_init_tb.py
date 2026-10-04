# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""P1 integration TB: the init slice against the DFI 4.0 BFM slave.

Mirrors scoria's scoria_core_tb BFM construction (DFIBase + DFISlavePHY +
DramStateModel) at DFIVersion.V4_0 / MemoryType.DDR4 with the vendored
jedec/ddr4-1600.csv profile, plus a DFI-pin command monitor that decodes the
stream with the kmap truth table and hands it to the shared order checker
(tbclasses.andesite_init_sequencer_tb.check_init_order) -- so the anchored
order is proven AT THE BOUNDARY, not just at the sequencer's pins.

The CocoTBFramework import path: the venv carries a shadowing installed copy,
so $RDS_DV/src (RTLDesignSherpa-DV, overridable by env) is forced to the
front of sys.path before any CocoTBFramework import.
"""

import os
import subprocess
import sys

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = _repo_root + "/bin"
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

_RDS_DV_SRC = os.environ.get(
    "RDS_DV_SRC", os.path.join(os.path.dirname(_repo_root),
                               "RTLDesignSherpa-DV", "src"))
if os.path.isdir(_RDS_DV_SRC) and _RDS_DV_SRC not in sys.path:
    sys.path.insert(0, _RDS_DV_SRC)

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Reuse the shared order checker + its constants.
_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV not in sys.path:
    sys.path.insert(0, _DV)
from tbclasses.andesite_init_sequencer_tb import check_init_order, SeqError  # noqa: E402

# kmap truth-table decode (generated/01_ddr4_command_table.md): the keyed
# encodings ACT_n-first that the monitor observes on the DFI pins.
_PIN2OP = {
    (1, 1, 1, 1): 0x00,   # NOP
    (0, 1, 1, 1): 0x01,   # ACT
    (1, 1, 0, 1): 0x02,   # RD
    (1, 1, 0, 0): 0x04,   # WR
    (0, 0, 0, 0): 0x0A,   # MRS
    (0, 0, 0, 1): 0x08,   # REF
    (1, 0, 1, 0): 0x06,   # PRE
    (1, 1, 1, 0): 0x0B,   # ZQ (CS vs CL distinguished by A10, irrelevant here)
}


class AndesiteInitTb:
    def __init__(self, dut):
        self.dut = dut
        self.events = []
        self.geardown_cycles = 0
        self._cycle = 0

    async def setup(self):
        d = self.dut
        cocotb.start_soon(Clock(d.clk, 10, units="ns").start())
        cocotb.start_soon(Clock(d.dfi_clk, 10, units="ns").start())

        # DFI 4.0 + DDR4 at the design point. The timing PROFILE is the
        # vendored ddr4-1600 CSV (Review Focus: no handwritten numbers).
        self.mapping = AddressMapping(
            num_ranks=1, num_banks=16,
            num_rows=1 << 15, num_cols=1 << 10,
            mapping="row|bank|col",
        )
        self.memory = MemoryModel(
            num_lines=16 * (1 << 15) * (1 << 10),
            bytes_per_line=1, log=None,
        )
        self.dfi_base = DFIBase(
            dfi_version=DFIVersion.V4_0,
            memory_type=MemoryType.DDR4,
            timings=builtin_timings("ddr4-1600"),
            mapping=self.mapping,
            beats_per_burst=8,
        )
        self.dfi_slave = DFISlavePHY(
            d, d.dfi_clk, base=self.dfi_base, memory=self.memory,
            dfi_phase_bytes=8, log=None)
        # Default policy: HARD violations raise inside the sim (a red test),
        # SOFT ones are counted and asserted empty at the end.
        cocotb.start_soon(self._monitor())

    async def _monitor(self):
        d = self.dut
        while True:
            await RisingEdge(d.dfi_clk)
            self._cycle += 1
            if int(d.phy_dfi_geardown_en.value) == 1:
                self.geardown_cycles += 1
            if int(d.phy_dfi_cs.value) == 0:
                key = (int(d.phy_dfi_act_n.value), int(d.phy_dfi_ras_n.value),
                       int(d.phy_dfi_cas_n.value), int(d.phy_dfi_we_n.value))
                op = _PIN2OP.get(key)
                if op is not None:
                    self.events.append((self._cycle, op,
                                        int(d.phy_dfi_bank.value),
                                        int(d.phy_dfi_address.value),
                                        int(d.phy_dfi_bg.value)))

    def violations(self):
        return self.dfi_slave.dram.policy.soft_violation_counts

    async def run_init(self, csrs, mr_images, max_cycles=5000):
        self.events.clear()
        self.geardown_cycles = 0
        d = self.dut
        d.tinit1_csr.value = csrs['tinit1']
        d.tinit3_csr.value = csrs['tinit3']
        d.tinit4_csr.value = csrs['tinit4']
        d.tdllk_csr.value = csrs['tdllk']
        d.tzqinit_csr.value = csrs['tzqinit']
        d.tmrd_csr.value = csrs['tmrd']
        d.tmod_csr.value = csrs['tmod']
        d.geardown_en_csr.value = csrs.get('geardown', 0)
        d.parity_en_csr.value = 1
        for m, img in enumerate(mr_images):
            getattr(d, f"mr{m}_image_csr").value = img
        d.reset_n.value = 0
        for _ in range(4):
            await RisingEdge(d.clk)
        d.reset_n.value = 1
        for i in range(max_cycles):
            await RisingEdge(d.clk)
            if int(d.init_done.value) == 1:
                return i
        return None

    def check_order(self, csrs):
        """Decode events through the kmap table and run the shared checker.

        DFI-side order: MRS's must appear as the anchored MR order, reading
        the MR index from {BG0, BA1, BA0}; ZQCL last.
        """
        mrs = []
        zq = None
        for cyc, op, bank, addr, bg in self.events:
            if op == 0x0A:
                mrs.append((cyc, op, (bg << 2) | bank, addr))
            elif op == 0x0B and zq is None:
                # ZQCL vs ZQCS is the A10 address input (kmap anchor).
                zq = (cyc, 0x0C if (addr >> 10) & 1 else 0x0B, bank, addr)
        if not mrs or zq is None:
            raise SeqError(f"missing commands: mrs={len(mrs)} zq={zq}")
        check_init_order(mrs + [zq], None, 0, csrs, self._cycle)
