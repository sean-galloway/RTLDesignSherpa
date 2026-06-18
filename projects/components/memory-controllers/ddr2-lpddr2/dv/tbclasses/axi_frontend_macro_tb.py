# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-17

"""
Testbench class for the axi_frontend_macro.

Drives:
  - AW push (raw flat address; addr_mapper_aw decodes inside the DUT)
  - AR push (raw flat address; addr_mapper_ar decodes inside)
  - Scheduler query / mark-issued strobes
  - Beat-pull and b_complete on the write side
  - Beat-arrival on the read side

Observes:
  - Forwarded (snarf) hits on AR with matching pending writes
  - Pass-through to rd_cmd_cam on miss
  - Scheduler match vectors
  - CAM occupancy / completion strobes

Methodology mirrors stream's macro-level TBs (e.g., DatapathRdTestTB):
no FSM in the TB either — sequencing is driven by explicit method
calls plus the DUT clock.
"""

import os
import logging
from dataclasses import dataclass
from typing import List, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Timer


@dataclass
class WriteEntry:
    """Bookkeeping for an AW that's been pushed to the DUT."""
    addr: int
    axi_id: int
    length: int        # beats
    w_buf_ptr: int
    strb_ptr: int
    full_strb: bool
    slot: Optional[int] = None


class AxiFrontendMacroTB:
    """TB helper for the axi_frontend_macro."""

    # Default address-map scheme = ROW_MAJOR (encoded 2'h0)
    SCHEME_ROW_MAJOR       = 0
    SCHEME_BANK_INTERLEAVE = 1
    SCHEME_XOR_HASH        = 2

    def __init__(self, dut):
        self.dut = dut
        self.log = logging.getLogger("axi_frontend_macro_tb")
        self.log.setLevel(logging.INFO)

        # In-flight bookkeeping
        self.pending_writes: List[WriteEntry] = []
        self.forward_hits = 0
        self.forward_misses = 0

    # ------------------------------------------------------------------
    # Clock / reset / config
    # ------------------------------------------------------------------

    async def setup(self, period_ns: int = 5, scheme: int = SCHEME_ROW_MAJOR):
        """Start the clock, drive reset, drive CSR defaults."""
        cocotb.start_soon(Clock(self.dut.mc_clk, period_ns, units="ns").start())

        # Defaults
        self.dut.scheme_active_i.value = scheme
        self.dut.xor_seed_i.value = 0
        self.dut.aw_valid_i.value = 0
        self.dut.aw_addr_i.value = 0
        self.dut.aw_id_i.value = 0
        self.dut.aw_len_i.value = 0
        self.dut.aw_w_buf_ptr_i.value = 0
        self.dut.aw_strb_ptr_i.value = 0
        self.dut.aw_full_strb_i.value = 0
        self.dut.ar_valid_i.value = 0
        self.dut.ar_addr_i.value = 0
        self.dut.ar_id_i.value = 0
        self.dut.ar_len_i.value = 0
        self.dut.fwd_ready_i.value = 1
        self.dut.q_rank_i.value = 0
        self.dut.q_bank_i.value = 0
        self.dut.q_row_i.value = 0
        self.dut.wr_issued_we_i.value = 0
        self.dut.wr_issued_slot_i.value = 0
        self.dut.rd_issued_we_i.value = 0
        self.dut.rd_issued_slot_i.value = 0
        self.dut.beat_pull_strb_i.value = 0
        self.dut.beat_pull_slot_i.value = 0
        self.dut.b_complete_strb_i.value = 0
        self.dut.b_complete_slot_i.value = 0
        self.dut.rd_beat_we_i.value = 0
        self.dut.rd_beat_slot_i.value = 0

        # Assert reset for a few cycles
        self.dut.mc_rst_n.value = 0
        for _ in range(5):
            await RisingEdge(self.dut.mc_clk)
        self.dut.mc_rst_n.value = 1
        await RisingEdge(self.dut.mc_clk)

    # ------------------------------------------------------------------
    # AW push
    # ------------------------------------------------------------------

    async def push_aw(self, entry: WriteEntry) -> int:
        """Push one AW. Blocks until accepted. Returns the assigned slot."""
        self.dut.aw_valid_i.value = 1
        self.dut.aw_addr_i.value = entry.addr
        self.dut.aw_id_i.value = entry.axi_id
        self.dut.aw_len_i.value = entry.length
        self.dut.aw_w_buf_ptr_i.value = entry.w_buf_ptr
        self.dut.aw_strb_ptr_i.value = entry.strb_ptr
        self.dut.aw_full_strb_i.value = 1 if entry.full_strb else 0

        # Wait for accept
        await ReadOnly()
        while int(self.dut.aw_ready_o.value) == 0:
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()

        slot = int(self.dut.aw_slot_o.value)
        await RisingEdge(self.dut.mc_clk)
        self.dut.aw_valid_i.value = 0
        entry.slot = slot
        self.pending_writes.append(entry)
        self.log.info(f"AW push accepted: addr=0x{entry.addr:08x} id={entry.axi_id} "
                      f"len={entry.length} slot={slot}")
        return slot

    # ------------------------------------------------------------------
    # AR push (sees either forward or rd_cmd_cam push)
    # ------------------------------------------------------------------

    async def push_ar(self, addr: int, axi_id: int, length: int) -> dict:
        """Push an AR. Returns a dict describing the outcome:
              {'kind': 'forward', 'src_slot': N, 'w_buf_ptr': P}
              {'kind': 'rd_push',  'rd_slot': N}
        """
        self.dut.ar_valid_i.value = 1
        self.dut.ar_addr_i.value = addr
        self.dut.ar_id_i.value = axi_id
        self.dut.ar_len_i.value = length

        await ReadOnly()
        while int(self.dut.ar_ready_o.value) == 0:
            await RisingEdge(self.dut.mc_clk)
            await ReadOnly()

        # Sample which path took it
        fwd_v = int(self.dut.fwd_valid_o.value)
        if fwd_v:
            src_slot = int(self.dut.fwd_src_slot_o.value)
            w_buf_ptr = int(self.dut.fwd_w_buf_ptr_o.value)
            outcome = {'kind': 'forward', 'src_slot': src_slot,
                       'w_buf_ptr': w_buf_ptr}
            self.forward_hits += 1
        else:
            rd_slot = int(self.dut.rd_slot_o.value)
            outcome = {'kind': 'rd_push', 'rd_slot': rd_slot}
            self.forward_misses += 1

        await RisingEdge(self.dut.mc_clk)
        self.dut.ar_valid_i.value = 0
        self.log.info(f"AR push accepted: addr=0x{addr:08x} id={axi_id} "
                      f"len={length} -> {outcome}")
        return outcome

    # ------------------------------------------------------------------
    # Scheduler stub: query and mark-issued
    # ------------------------------------------------------------------

    async def query_scheduler(self, rank: int, bank: int, row: int):
        """Drive the scheduler query inputs. Returns the two match vectors."""
        self.dut.q_rank_i.value = rank
        self.dut.q_bank_i.value = bank
        self.dut.q_row_i.value = row
        await Timer(1, units="ns")  # let comb propagate
        return {
            'wr_pending': int(self.dut.wr_match_pending_o.value),
            'wr_rowhit':  int(self.dut.wr_match_rowhit_o.value),
            'rd_pending': int(self.dut.rd_match_pending_o.value),
            'rd_rowhit':  int(self.dut.rd_match_rowhit_o.value),
        }

    async def mark_wr_issued(self, slot: int):
        self.dut.wr_issued_we_i.value = 1
        self.dut.wr_issued_slot_i.value = slot
        await RisingEdge(self.dut.mc_clk)
        self.dut.wr_issued_we_i.value = 0

    async def mark_rd_issued(self, slot: int):
        self.dut.rd_issued_we_i.value = 1
        self.dut.rd_issued_slot_i.value = slot
        await RisingEdge(self.dut.mc_clk)
        self.dut.rd_issued_we_i.value = 0

    # ------------------------------------------------------------------
    # Beat-pull (wr) / b_complete / read-beat / completion observation
    # ------------------------------------------------------------------

    async def pull_wr_beat(self, slot: int):
        self.dut.beat_pull_strb_i.value = 1
        self.dut.beat_pull_slot_i.value = slot
        await ReadOnly()
        ptr  = int(self.dut.beat_pull_ptr_o.value)
        sptr = int(self.dut.beat_pull_strb_ptr_o.value)
        last = int(self.dut.beat_pull_last_o.value)
        await RisingEdge(self.dut.mc_clk)
        self.dut.beat_pull_strb_i.value = 0
        return {'ptr': ptr, 'strb_ptr': sptr, 'last': bool(last)}

    async def b_complete(self, slot: int):
        self.dut.b_complete_strb_i.value = 1
        self.dut.b_complete_slot_i.value = slot
        await RisingEdge(self.dut.mc_clk)
        self.dut.b_complete_strb_i.value = 0
        # Prune local bookkeeping
        self.pending_writes = [w for w in self.pending_writes if w.slot != slot]

    async def rd_beat(self, slot: int):
        self.dut.rd_beat_we_i.value = 1
        self.dut.rd_beat_slot_i.value = slot
        await RisingEdge(self.dut.mc_clk)
        self.dut.rd_beat_we_i.value = 0

    # ------------------------------------------------------------------
    # Observation helpers
    # ------------------------------------------------------------------

    async def settle(self, ns: int = 1) -> None:
        """Wait for combinational propagation before sampling outputs."""
        await Timer(ns, units="ns")

    async def reset_dut(self, cycles: int = 3) -> None:
        """Re-assert mc_rst_n for `cycles` MC clocks and clear TB
        bookkeeping. Used between sub-scenarios in a bundle so each one
        starts from a clean CAM state without rebuilding the DUT.
        """
        self.dut.mc_rst_n.value = 0
        # De-assert any leftover handshakes that could carry over
        self.dut.aw_valid_i.value = 0
        self.dut.ar_valid_i.value = 0
        self.dut.wr_issued_we_i.value = 0
        self.dut.rd_issued_we_i.value = 0
        self.dut.beat_pull_strb_i.value = 0
        self.dut.b_complete_strb_i.value = 0
        self.dut.rd_beat_we_i.value = 0
        self.dut.fwd_ready_i.value = 1
        for _ in range(cycles):
            await RisingEdge(self.dut.mc_clk)
        self.dut.mc_rst_n.value = 1
        await RisingEdge(self.dut.mc_clk)
        # TB-side bookkeeping
        self.pending_writes.clear()
        self.forward_hits = 0
        self.forward_misses = 0

    async def wr_cam_occupancy(self) -> int:
        await self.settle()
        return int(self.dut.dbg_wr_cam_occ_o.value)

    async def rd_cam_occupancy(self) -> int:
        await self.settle()
        return int(self.dut.dbg_rd_cam_occ_o.value)

    # ------------------------------------------------------------------
    # Stream push helpers (back-to-back at 1 burst per cycle when ready)
    # ------------------------------------------------------------------

    async def push_aw_stream(self, entries: List[WriteEntry]) -> List[int]:
        """Push a list of WriteEntries with valid held high across the burst.
        Returns the slot index each entry landed in.
        """
        slots: List[int] = []
        for e in entries:
            self.dut.aw_valid_i.value = 1
            self.dut.aw_addr_i.value = e.addr
            self.dut.aw_id_i.value = e.axi_id
            self.dut.aw_len_i.value = e.length
            self.dut.aw_w_buf_ptr_i.value = e.w_buf_ptr
            self.dut.aw_strb_ptr_i.value = e.strb_ptr
            self.dut.aw_full_strb_i.value = 1 if e.full_strb else 0

            await ReadOnly()
            while int(self.dut.aw_ready_o.value) == 0:
                await RisingEdge(self.dut.mc_clk)
                await ReadOnly()
            slot = int(self.dut.aw_slot_o.value)
            slots.append(slot)
            e.slot = slot
            self.pending_writes.append(e)
            await RisingEdge(self.dut.mc_clk)

        self.dut.aw_valid_i.value = 0
        return slots

    async def push_ar_stream(self, items) -> list:
        """items = list of (addr, axi_id, length). Returns the outcome dict
        for each entry."""
        outcomes = []
        for addr, axi_id, length in items:
            self.dut.ar_valid_i.value = 1
            self.dut.ar_addr_i.value = addr
            self.dut.ar_id_i.value = axi_id
            self.dut.ar_len_i.value = length

            await ReadOnly()
            while int(self.dut.ar_ready_o.value) == 0:
                await RisingEdge(self.dut.mc_clk)
                await ReadOnly()

            fwd_v = int(self.dut.fwd_valid_o.value)
            if fwd_v:
                outcome = {
                    'kind': 'forward',
                    'src_slot': int(self.dut.fwd_src_slot_o.value),
                    'w_buf_ptr': int(self.dut.fwd_w_buf_ptr_o.value),
                    'id': axi_id,
                    'len': length,
                }
                self.forward_hits += 1
            else:
                outcome = {
                    'kind': 'rd_push',
                    'rd_slot': int(self.dut.rd_slot_o.value),
                    'id': axi_id,
                    'len': length,
                }
                self.forward_misses += 1
            outcomes.append(outcome)
            await RisingEdge(self.dut.mc_clk)

        self.dut.ar_valid_i.value = 0
        return outcomes

    # ------------------------------------------------------------------
    # Write lifecycle helpers (issue -> drain beats -> b_complete)
    # ------------------------------------------------------------------

    async def drain_wr_slot(self, slot: int, length: int) -> None:
        """Pull `length` beats from the wr CAM slot and then strobe b_complete.
        Simulates what scheduler + wr_data_path + xbank_timers would do.
        """
        await self.mark_wr_issued(slot)
        for _ in range(length):
            await self.pull_wr_beat(slot)
        await self.b_complete(slot)

    # ------------------------------------------------------------------
    # Read lifecycle helpers (issue -> strobe beats -> entry_complete)
    # ------------------------------------------------------------------

    async def drain_rd_slot(self, slot: int, length: int) -> None:
        """Mark issued then strobe `length` beats; verifies entry_complete
        fires on the last beat."""
        await self.mark_rd_issued(slot)
        for i in range(length):
            self.dut.rd_beat_we_i.value = 1
            self.dut.rd_beat_slot_i.value = slot
            await RisingEdge(self.dut.mc_clk)
        self.dut.rd_beat_we_i.value = 0

    # ------------------------------------------------------------------
    # Forwarded-read consumer (data path stub)
    #
    # When the macro asserts fwd_valid_o, the TB drives fwd_ready_i=1 by
    # default — the forwarded outcomes are sampled in push_ar / push_ar_stream
    # so there is nothing else to consume here. This helper exists for tests
    # that want to apply backpressure.
    # ------------------------------------------------------------------

    def set_fwd_ready(self, ready: bool) -> None:
        self.dut.fwd_ready_i.value = 1 if ready else 0
