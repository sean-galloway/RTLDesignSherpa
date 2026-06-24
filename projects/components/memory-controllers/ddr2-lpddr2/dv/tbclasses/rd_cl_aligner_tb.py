# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: RdClAlignerTB
# Purpose: Unit-level testbench for rd_cl_aligner.

"""
Testbench class for `rd_cl_aligner`.

The FUB drives `dfi_rddata_en`, captures PHY-returned `dfi_rddata` (DFI_RATE
DRAM beats per cycle) and streams DRAM beats out to `rd_inject_*`.

The TB:
  * Acts as the scheduler: drives `op_valid_i` + slot/id/len.
  * Acts as the PHY: when `dfi_rddata_en_o` goes high, queues a per-burst
    program of DFI cycles. Each cycle is injected as `dfi_rddata_valid_i=1`
    + the DFI-cycle data on `dfi_rddata_i` at a configurable delay
    (`phy_rdlat_min`..`phy_rdlat_max` cycles after the controller asserted
    en, with optional jitter).
  * Acts as the axi_intake R-FSM: holds `rd_inject_ready_i` high (or with
    backpressure for the throttle test) and records each beat the FUB
    emits.
  * Scoreboards: the recorded beat sequence must equal the burst's
    expected DRAM beats; `rd_inject_last_o` must pulse on the final
    handshake; `rd_beat_we_o` must pulse exactly once per accepted beat.
"""

import os
import sys
import random
import subprocess
from collections import deque
from dataclasses import dataclass, field
from typing import Deque, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, Timer

_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


# ---------------------------------------------------------------------------
# Records
# ---------------------------------------------------------------------------

@dataclass
class ReadBurst:
    slot: int
    axi_id: int
    beats: List[int]                # DRAM-beat-wide values, in burst order
    t_rddata_en: int = 0            # PHY wait from OP_RD to dfi_rddata_en assert
    phy_rdlat: int = 0              # cycles from en-asserted to first valid
    completed: bool = False


# ---------------------------------------------------------------------------
# TB
# ---------------------------------------------------------------------------

class RdClAlignerTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        # Parameters — must match the verilator -G overrides
        self.RD_CAM_DEPTH    = self.convert_to_int(os.environ.get('RD_CAM_DEPTH',    '16'))
        self.AXI_ID_WIDTH    = self.convert_to_int(os.environ.get('AXI_ID_WIDTH',     '4'))
        self.BURST_LEN_WIDTH = self.convert_to_int(os.environ.get('BURST_LEN_WIDTH',  '8'))
        self.DRAM_BEAT_WIDTH = self.convert_to_int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.DFI_RATE        = self.convert_to_int(os.environ.get('DFI_RATE',         '2'))
        self.MAX_BURST_LEN   = self.convert_to_int(os.environ.get('MAX_BURST_LEN',  '256'))

        self.DFI_DATA_WIDTH  = self.DRAM_BEAT_WIDTH * self.DFI_RATE
        self.RSL             = max(1, (self.RD_CAM_DEPTH - 1).bit_length())

        self.MASK_DATA = (1 << self.DRAM_BEAT_WIDTH) - 1

        # State
        self.current_burst:    Optional[ReadBurst] = None
        self.captured_beats:   List[int] = []
        # `captured_ids` parallels captured_beats; one entry per
        # rd_inject handshake. Used by verify_capture to catch any
        # regression where `op_id_i` is not forwarded to
        # `rd_inject_id_o` (e.g. tied to 0 — see G-01c at the top
        # level).
        self.captured_ids:     List[int] = []
        self.beat_we_count:    int = 0
        self.last_seen:        bool = False
        self.dfi_cycles_remaining_pending: Deque[Tuple[int, int]] = deque()
        # ^ queue of (dfi_cycle_value, delay_remaining) tuples to inject

        # v2 multi-outstanding: ordered list of bursts in scheduler-issue
        # order. The PHY injector walks this FIFO; when empty, falls back
        # to current_burst for single-burst legacy tests.
        self.pending_bursts:   List[ReadBurst] = []

        # Backpressure control
        self.rd_inject_ready_pattern = 'always'  # 'always' or 'throttle'

    # ---------------- setup ----------------

    async def setup_clocks_and_reset(self):
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

        cocotb.start_soon(self._phy_injector())
        cocotb.start_soon(self._inject_handler())
        cocotb.start_soon(self._beat_we_monitor())

    def _drive_idle(self):
        self.dut.cl_i.value                = 5
        self.dut.al_i.value                = 0
        self.dut.t_rddata_en_i.value       = 0
        self.dut.rd_in_order_i.value       = 0
        self.dut.op_valid_i.value          = 0
        self.dut.op_slot_i.value           = 0
        self.dut.op_id_i.value             = 0
        self.dut.op_len_i.value            = 0
        self.dut.dfi_rddata_i.value        = 0
        self.dut.dfi_rddata_valid_i.value  = 0
        self.dut.rd_inject_ready_i.value   = 1

    # ---------------- background ----------------

    async def _phy_injector(self):
        """Mocks the PHY: when dfi_rddata_en_o is high, schedules an
        injection of a DFI cycle of data after `phy_rdlat` cycles. Then,
        at each scheduled time, drives dfi_rddata_valid_i for one cycle
        with the DFI cycle's data on dfi_rddata_i."""
        # Tracker: which DFI cycle index in current_burst is next to be
        # captured by the PHY (i.e., when we see en, we pull the next
        # DFI cycle from current_burst and schedule it for injection).
        en_seen_count = 0
        # Pending: list of (deliver_at_cycle_offset, dfi_value).
        # We advance the offset by 1 each cycle; when it hits 0, inject.
        pending: List[List[int]] = []   # each elem: [delay, value]
        cycle = 0

        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            cycle += 1

            # Decrement all pending delays; if any reach 0, inject.
            inject_this_cycle = None
            new_pending = []
            for entry in pending:
                entry[0] -= 1
                if entry[0] <= 0 and inject_this_cycle is None:
                    inject_this_cycle = entry[1]
                else:
                    new_pending.append(entry)
            pending = new_pending

            # Capture en pulses → schedule next DFI cycle from the burst.
            en_high = int(self.dut.dfi_rddata_en_o.value) != 0
            if en_high and self.current_burst is not None:
                b = self.current_burst
                # Compute the DFI cycle's packed value from b.beats[en_seen_count*DFI_RATE..+DFI_RATE]
                dfi_idx = en_seen_count
                dfi_val = 0
                for r in range(self.DFI_RATE):
                    beat_idx = dfi_idx * self.DFI_RATE + r
                    if beat_idx < len(b.beats):
                        dfi_val |= (b.beats[beat_idx] & self.MASK_DATA) \
                                   << (r * self.DRAM_BEAT_WIDTH)
                    # else: trailing beat past burst end — leave 0 (the
                    # FUB will not emit it, so the value doesn't matter).
                expected_dfi_cycles = (len(b.beats) + self.DFI_RATE - 1) // self.DFI_RATE
                if en_seen_count < expected_dfi_cycles:
                    pending.append([max(1, b.phy_rdlat), dfi_val])
                    en_seen_count += 1

            # Drive PHY response signals this cycle.
            if inject_this_cycle is not None:
                self.dut.dfi_rddata_i.value       = inject_this_cycle
                self.dut.dfi_rddata_valid_i.value = 1
            else:
                self.dut.dfi_rddata_i.value       = 0
                self.dut.dfi_rddata_valid_i.value = 0

            # Reset between bursts: when current_burst clears, also reset
            # the en counter so the next burst restarts at DFI cycle 0.
            if self.current_burst is None:
                en_seen_count = 0
                pending = []

    async def _inject_handler(self):
        """Combined capturer + ready driver. Reads (valid, ready) at the
        rising edge (the same moment the DUT samples them for the
        handshake decision), then drives ready_i for the NEXT cycle.
        Combining into one coroutine eliminates the cocotb-scheduler
        race that would otherwise let the capturer observe a stale
        ready value relative to the driver's pending NBA write."""
        rng = random.Random(self.SEED ^ 0xBEEF)
        while True:
            await RisingEdge(self.dut.mc_clk)
            # Capture pre-NBA (= the values the DUT saw at this edge).
            v = int(self.dut.rd_inject_valid_o.value)
            r = int(self.dut.rd_inject_ready_i.value)
            if v and r:
                self.captured_beats.append(int(self.dut.rd_inject_data_o.value))
                self.captured_ids.append(int(self.dut.rd_inject_id_o.value))
                if int(self.dut.rd_inject_last_o.value):
                    self.last_seen = True
            # Drive ready_i for the NEXT cycle's edge.
            if self.rd_inject_ready_pattern == 'throttle':
                self.dut.rd_inject_ready_i.value = 1 if rng.random() < 0.5 else 0
            else:
                self.dut.rd_inject_ready_i.value = 1

    async def _beat_we_monitor(self):
        """Records every rd_beat_we_o pulse — should equal captured beat
        count for a clean burst."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.rd_beat_we_o.value):
                self.beat_we_count += 1

    # ---------------- ops ----------------

    async def issue_op(self, burst: ReadBurst) -> None:
        """Drive op_valid handshake for `burst`. Returns when handshake
        completes."""
        self.current_burst = burst
        self.captured_beats.clear()
        self.captured_ids.clear()
        self.beat_we_count = 0
        self.last_seen = False

        self.dut.t_rddata_en_i.value = burst.t_rddata_en
        self.dut.op_slot_i.value     = burst.slot   & ((1 << self.RSL) - 1)
        self.dut.op_id_i.value       = burst.axi_id & ((1 << self.AXI_ID_WIDTH) - 1)
        self.dut.op_len_i.value      = len(burst.beats) & ((1 << self.BURST_LEN_WIDTH) - 1)
        self.dut.op_valid_i.value    = 1

        await Timer(_NBA_SETTLE_PS, units='ps')
        while int(self.dut.op_ready_o.value) == 0:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.op_valid_i.value = 0

    async def await_burst_complete(self, burst: ReadBurst,
                                    timeout_cycles: int = 4096) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if self.last_seen and len(self.captured_beats) == len(burst.beats):
                burst.completed = True
                # Allow PHY injector to drain before clearing current_burst
                await self.wait_clocks('mc_clk', 4)
                self.current_burst = None
                return
        raise TimeoutError(
            f"Read burst slot={burst.slot} id={burst.axi_id} "
            f"len={len(burst.beats)}: captured {len(self.captured_beats)}/{len(burst.beats)} beats; last_seen={self.last_seen}"
        )

    # ---------------- scoreboard ----------------

    def verify_capture(self, burst: ReadBurst) -> None:
        assert len(self.captured_beats) == len(burst.beats), (
            f"beat count mismatch: got {len(self.captured_beats)} "
            f"want {len(burst.beats)}"
        )
        for i, (g, e) in enumerate(zip(self.captured_beats, burst.beats)):
            e_masked = e & self.MASK_DATA
            assert g == e_masked, (
                f"beat {i}: got {g:#x} want {e_masked:#x}"
            )
        # Every beat must carry the originating AR's id. This catches
        # any regression where op_id_i is dropped or tied to 0 in the
        # rd_inject path (cf. G-01c, which manifested at the top level
        # because rd_snap_id was tied to 0 — but rd_cl_aligner itself
        # is responsible for the per-slot id register, so a unit-level
        # guard here belongs).
        expected_id = burst.axi_id & ((1 << self.AXI_ID_WIDTH) - 1)
        for i, g in enumerate(self.captured_ids):
            assert g == expected_id, (
                f"beat {i}: rd_inject_id_o={g} (got) "
                f"!= op_id_i={expected_id} (want)"
            )
        assert self.beat_we_count == len(burst.beats), (
            f"rd_beat_we count {self.beat_we_count} != len {len(burst.beats)}"
        )
        assert self.last_seen, "rd_inject_last_o never pulsed"

    # ---------------- convenience ----------------

    def make_burst(self, *, slot: int, axi_id: int, length: int,
                   t_rddata_en: int = 0, phy_rdlat: int = 1,
                   seed_tag: int = 0) -> ReadBurst:
        beats = [
            ((seed_tag << 40) | (slot << 32) | (axi_id << 24) | i)
            & self.MASK_DATA
            for i in range(length)
        ]
        return ReadBurst(slot=slot, axi_id=axi_id, beats=beats,
                         t_rddata_en=t_rddata_en, phy_rdlat=phy_rdlat)
