# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: WrBeatSequencerTB
# Purpose: Unit-level testbench for wr_beat_sequencer.

"""
Testbench class for `wr_beat_sequencer`.

The FUB pulls W beats from a mocked wr CAM (via the beat_pull interface +
wbuf_rd_data/strb) and packs them into DFI_RATE-wide DFI cycles after a
PHY-defined t_phy_wrlat wait.

The TB:
  * Acts as the wr CAM: when `beat_pull_strb_o` is high, drives the next
    beat's data/strb on `wbuf_rd_data_i`/`wbuf_rd_strb_i`, and asserts
    `beat_pull_last_i` on the burst's final beat.
  * Acts as the scheduler: drives `op_valid_i` + slot/len handshakes.
  * Acts as the DFI consumer: every cycle `dfi_wrdata_en_o` is high,
    captures `(dfi_wrdata_o, dfi_wrdata_mask_o)` for later verification.
  * Scoreboards the captured DFI cycles against the expected pack — beats
    are packed `DFI_RATE` per DFI cycle, mask is `~wstrb` per DFI byte,
    tail-of-burst beats are masked off.
  * Verifies `b_complete_strb_o` slot matches the issued slot.
"""

import os
import sys
import random
import subprocess
from collections import deque
from dataclasses import dataclass, field
from typing import Deque, Dict, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Timer

_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


# ---------------------------------------------------------------------------
# Burst / capture records
# ---------------------------------------------------------------------------

@dataclass
class Burst:
    slot: int
    beats: List[int]                 # DRAM_BEAT_WIDTH-wide beats, in order
    strbs: List[int]                 # DRAM_STRB_WIDTH-wide AXI wstrb, per beat
    t_phy_wrlat: int = 0             # PHY-required wait cycles
    issued: bool = False
    pulled_count: int = 0
    completed: bool = False


@dataclass
class DfiCycle:
    data: int
    mask: int


# ---------------------------------------------------------------------------
# TB
# ---------------------------------------------------------------------------

class WrBeatSequencerTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        # Parameters — must match the verilator -G overrides
        self.WR_CAM_DEPTH    = self.convert_to_int(os.environ.get('WR_CAM_DEPTH',    '16'))
        self.W_BUF_PTR_WIDTH = self.convert_to_int(os.environ.get('W_BUF_PTR_WIDTH', '7'))
        self.BURST_LEN_WIDTH = self.convert_to_int(os.environ.get('BURST_LEN_WIDTH', '8'))
        self.DRAM_BEAT_WIDTH = self.convert_to_int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.DFI_RATE        = self.convert_to_int(os.environ.get('DFI_RATE',         '2'))
        self.MAX_BURST_LEN   = self.convert_to_int(os.environ.get('MAX_BURST_LEN',  '256'))

        self.DRAM_STRB_WIDTH = self.DRAM_BEAT_WIDTH // 8
        self.DFI_DATA_WIDTH  = self.DRAM_BEAT_WIDTH * self.DFI_RATE
        self.DFI_STRB_WIDTH  = self.DFI_DATA_WIDTH // 8
        self.WSL             = max(1, (self.WR_CAM_DEPTH - 1).bit_length())

        self.MASK_DATA = (1 << self.DRAM_BEAT_WIDTH) - 1
        self.MASK_STRB = (1 << self.DRAM_STRB_WIDTH) - 1

        # State
        self.current_burst: Optional[Burst] = None
        self.captured_cycles: List[DfiCycle] = []
        self.b_completes:     List[int]      = []

        # Pending op queue for back-to-back tests: each entry is a Burst
        # to issue when op_ready_o is high.
        self.pending_ops: Deque[Burst] = deque()

    # ---------------- setup ----------------

    async def setup_clocks_and_reset(self):
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

        # Background coroutines
        cocotb.start_soon(self._beat_pull_responder())
        cocotb.start_soon(self._dfi_capturer())
        cocotb.start_soon(self._b_complete_monitor())

    def _drive_idle(self):
        self.dut.cwl_i.value             = 4
        self.dut.t_phy_wrlat_i.value     = 0
        self.dut.op_valid_i.value        = 0
        self.dut.op_slot_i.value         = 0
        self.dut.op_len_i.value          = 0
        self.dut.beat_pull_ptr_i.value   = 0
        self.dut.beat_pull_strb_ptr_i.value = 0
        self.dut.beat_pull_last_i.value  = 0
        self.dut.wbuf_rd_data_i.value    = 0
        self.dut.wbuf_rd_strb_i.value    = 0

    # ---------------- background responders ----------------

    async def _beat_pull_responder(self):
        """Acts as the wr CAM + w_buf: drives wbuf_rd_data/strb whenever the
        FUB raises beat_pull_strb_o, and pulses beat_pull_last_i on the
        burst's final beat."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')

            strb = int(self.dut.beat_pull_strb_o.value)
            if strb and self.current_burst is not None:
                b = self.current_burst
                if b.pulled_count >= len(b.beats):
                    # Spurious / extra strobe — drive idle to make the bug
                    # visible in scoreboard.
                    self.dut.wbuf_rd_data_i.value = 0
                    self.dut.wbuf_rd_strb_i.value = 0
                    self.dut.beat_pull_last_i.value = 0
                    continue
                idx = b.pulled_count
                self.dut.wbuf_rd_data_i.value   = b.beats[idx] & self.MASK_DATA
                self.dut.wbuf_rd_strb_i.value   = b.strbs[idx] & self.MASK_STRB
                self.dut.beat_pull_last_i.value = 1 if (idx == len(b.beats) - 1) else 0
                self.dut.beat_pull_ptr_i.value  = idx & ((1 << self.W_BUF_PTR_WIDTH) - 1)
                self.dut.beat_pull_strb_ptr_i.value = idx & ((1 << self.W_BUF_PTR_WIDTH) - 1)
                b.pulled_count += 1
            else:
                self.dut.wbuf_rd_data_i.value   = 0
                self.dut.wbuf_rd_strb_i.value   = 0
                self.dut.beat_pull_last_i.value = 0

    async def _dfi_capturer(self):
        """Captures (dfi_wrdata, dfi_wrdata_mask) every cycle dfi_wrdata_en
        is high. Called from a single background task to keep ordering."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(self.dut.dfi_wrdata_en_o.value):
                self.captured_cycles.append(DfiCycle(
                    data=int(self.dut.dfi_wrdata_o.value),
                    mask=int(self.dut.dfi_wrdata_mask_o.value),
                ))

    async def _b_complete_monitor(self):
        """Captures b_complete_strb_o pulses."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(self.dut.b_complete_strb_o.value):
                self.b_completes.append(int(self.dut.b_complete_slot_o.value))

    # ---------------- op driver ----------------

    async def issue_op(self, burst: Burst) -> None:
        """Drive op_valid handshake for `burst`. Returns when handshake
        completes; the rest of the burst (pull / drive / b_complete) runs
        through the background responders. Caller should `await
        await_burst()` to wait for completion."""
        # Make this the current burst for the responders
        self.current_burst = burst
        self.captured_cycles.clear()
        self.b_completes.clear()

        self.dut.t_phy_wrlat_i.value = burst.t_phy_wrlat
        self.dut.op_slot_i.value     = burst.slot & ((1 << self.WSL) - 1)
        self.dut.op_len_i.value      = len(burst.beats) & ((1 << self.BURST_LEN_WIDTH) - 1)
        self.dut.op_valid_i.value    = 1

        # Wait for handshake (op_ready_o high)
        await Timer(_NBA_SETTLE_PS, units='ps')
        while int(self.dut.op_ready_o.value) == 0:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
        # Both high — handshake on next edge
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.op_valid_i.value = 0
        burst.issued = True

    async def await_burst_complete(self, burst: Burst,
                                    timeout_cycles: int = 4096) -> None:
        """Wait until b_complete_strb_o pulses with the burst's slot."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if self.b_completes and self.b_completes[-1] == burst.slot:
                burst.completed = True
                return
        raise TimeoutError(
            f"b_complete for slot {burst.slot} not seen within "
            f"{timeout_cycles} cycles"
        )

    # ---------------- scoreboard ----------------

    def expected_dfi_cycles(self, burst: Burst) -> List[DfiCycle]:
        """Compute the expected DFI cycle stream for `burst`. Packs
        DFI_RATE DRAM beats into each cycle, masks off tail beats when
        len % DFI_RATE != 0."""
        cycles = []
        n_dfi = (len(burst.beats) + self.DFI_RATE - 1) // self.DFI_RATE
        for dfi_idx in range(n_dfi):
            data = 0
            mask = (1 << self.DFI_STRB_WIDTH) - 1   # start fully masked
            for r in range(self.DFI_RATE):
                beat_idx = dfi_idx * self.DFI_RATE + r
                if beat_idx < len(burst.beats):
                    bd = burst.beats[beat_idx] & self.MASK_DATA
                    bs = burst.strbs[beat_idx] & self.MASK_STRB
                    data |= bd << (r * self.DRAM_BEAT_WIDTH)
                    # DFI mask = ~AXI wstrb, in this beat's lane
                    lane_mask_ones = (1 << self.DRAM_STRB_WIDTH) - 1
                    lane_mask = (~bs) & lane_mask_ones
                    # Clear this lane in `mask`, then OR lane_mask in
                    lane_shift = r * self.DRAM_STRB_WIDTH
                    mask &= ~(lane_mask_ones << lane_shift)
                    mask |= lane_mask << lane_shift
            cycles.append(DfiCycle(data=data, mask=mask))
        return cycles

    def verify_capture(self, burst: Burst) -> None:
        expected = self.expected_dfi_cycles(burst)
        got = self.captured_cycles
        assert len(got) == len(expected), (
            f"DFI cycle count mismatch for slot {burst.slot}: "
            f"got {len(got)} want {len(expected)}"
        )
        for i, (g, e) in enumerate(zip(got, expected)):
            assert g.data == e.data, (
                f"DFI cycle {i} data mismatch: got {g.data:#x} want {e.data:#x}"
            )
            assert g.mask == e.mask, (
                f"DFI cycle {i} mask mismatch: got {g.mask:#x} want {e.mask:#x}"
            )

    # ---------------- convenience ----------------

    def make_burst(self, slot: int, length: int,
                   full_strb: bool = True,
                   t_phy_wrlat: int = 0,
                   seed_tag: int = 0) -> Burst:
        """Generate a deterministic burst with `length` beats."""
        beats = [
            ((seed_tag << 32) | (slot << 24) | (i & 0xFFFF))
            & self.MASK_DATA
            for i in range(length)
        ]
        if full_strb:
            strbs = [self.MASK_STRB] * length
        else:
            # Alternate full/partial to exercise mask packing
            strbs = []
            for i in range(length):
                if (i & 1) == 0:
                    strbs.append(self.MASK_STRB)
                else:
                    strbs.append(0x0F & self.MASK_STRB)
        return Burst(slot=slot, beats=beats, strbs=strbs,
                     t_phy_wrlat=t_phy_wrlat)
