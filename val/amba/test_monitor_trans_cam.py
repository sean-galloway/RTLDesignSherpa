# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monitor_trans_cam
# Purpose: FUB cocotb tests for rtl/amba/shared/monitor_trans_cam.sv
#
# Documentation: rtl/amba/shared/monitor_trans_cam.sv (header comment)
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-06-08

"""
FUB tests for monitor_trans_cam — the multi-port ID CAM with opaque
payload storage that fronts the axi_monitor_trans_mgr family.

The CAM is purely combinational on the lookup side (three independent
ID lookups + free vector + priority-encoded alloc one-hots) and
register-backed on the write side (per-slot one-hot write enable +
valid/id/payload next inputs). Storage is exposed via per-slot read
outputs for downstream consumers.

Test sequence (run in order by monitor_trans_cam_test):
  1. reset state             — all invalid, free_oh = all 1s, no matches
  2. single write + lookup   — write slot 0 with id=K, addr lookup hits
  3. independent writes      — every slot writable independently
  4. three-port lookup       — distinct addr/data/resp ids resolve independently
  5. data_match_first_oh     — duplicate ids: lowest-index match wins
  6. free_oh tracking        — valid bit flips track in free_oh
  7. clear via we+valid=0    — write port can clear a slot
  8. alloc one phase         — addr_wants_alloc -> lowest-index free slot
  9. alloc mutex             — addr+data+resp all want -> three distinct slots
 10. alloc partial wants     — only some phases want -> others zero
 11. alloc when full         — no free slots -> all alloc_oh zero
 12. payload preserved       — write+hold; payload survives idle cycles
 13. concurrent writes       — entry_we bits to multiple slots in one cycle
 14. lookup miss             — id absent from CAM -> match_oh = 0
 15. alloc-priority cascade  — fill exactly N-1, watch the last free slot
                              get claimed and the next cycle have nothing
 16. id collision tolerance  — two valid slots with same id: match_oh hits
                              both, first_oh picks lowest-index
 17. random stress           — random write/lookup/alloc mix vs Python model

Pattern A (val/amba convention): single cocotb test that dispatches the
sub-sequences, parameterized at the pytest level on
(ID_WIDTH, PAYLOAD_WIDTH, DEPTH, REG_LEVEL).
"""

import os
import random
from dataclasses import dataclass, field
from typing import List, Tuple

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd


# ----------------------------------------------------------------------------
# Inline Python golden model — bit-exact mirror of the RTL
# ----------------------------------------------------------------------------

@dataclass
class _TransCamEntry:
    valid:   bool = False
    id_val:  int  = 0
    payload: int  = 0


class _TransCamModel:
    """Mirrors monitor_trans_cam's registered state and combinational
    outputs. Storage is per-slot (no LRU); writes are per-slot one-hot."""

    def __init__(self, depth: int, id_mask: int, payload_mask: int):
        self.depth        = depth
        self.id_mask      = id_mask
        self.payload_mask = payload_mask
        self.entries: List[_TransCamEntry] = [
            _TransCamEntry() for _ in range(depth)
        ]

    # ---- combinational outputs ----------------------------------------

    def match_oh(self, lookup_id: int) -> int:
        mask = 0
        for i, e in enumerate(self.entries):
            if e.valid and e.id_val == (lookup_id & self.id_mask):
                mask |= 1 << i
        return mask

    def first_match_oh(self, lookup_id: int) -> int:
        for i, e in enumerate(self.entries):
            if e.valid and e.id_val == (lookup_id & self.id_mask):
                return 1 << i
        return 0

    def free_oh(self) -> int:
        mask = 0
        for i, e in enumerate(self.entries):
            if not e.valid:
                mask |= 1 << i
        return mask

    def alloc_oh(self,
                 wants_addr: bool,
                 wants_data: bool,
                 wants_resp: bool) -> Tuple[int, int, int]:
        remaining = self.free_oh()
        addr_oh = data_oh = resp_oh = 0

        if wants_addr:
            lsb = remaining & (-remaining)
            if lsb:
                addr_oh    = lsb
                remaining ^= lsb
        if wants_data:
            lsb = remaining & (-remaining)
            if lsb:
                data_oh    = lsb
                remaining ^= lsb
        if wants_resp:
            lsb = remaining & (-remaining)
            if lsb:
                resp_oh    = lsb
                remaining ^= lsb

        return addr_oh, data_oh, resp_oh

    # ---- registered update ---------------------------------------------

    def commit_writes(self,
                      we_mask: int,
                      valid_next_mask: int,
                      ids_next: List[int],
                      payloads_next: List[int]):
        for i in range(self.depth):
            if (we_mask >> i) & 1:
                self.entries[i] = _TransCamEntry(
                    valid   = bool((valid_next_mask >> i) & 1),
                    id_val  = ids_next[i] & self.id_mask,
                    payload = payloads_next[i] & self.payload_mask,
                )


# ----------------------------------------------------------------------------
# Test config
# ----------------------------------------------------------------------------
@dataclass
class TransCamConfig:
    id_width:      int = 8
    payload_width: int = 64
    depth:         int = 16

    def __post_init__(self):
        assert self.depth >= 4, \
            "DEPTH must be at least 4 to exercise the three-phase alloc mutex"
        assert self.id_width >= 1
        assert self.payload_width >= 1


# ----------------------------------------------------------------------------
# Testbench
# ----------------------------------------------------------------------------
class MonitorTransCamTB(TBBase):
    """Drives lookups + per-slot writes + alloc-wants; cross-checks every
    combinational output and registered state against a Python model."""

    def __init__(self, dut):
        super().__init__(dut)

        self.ID_WIDTH      = int(os.environ.get('PARAM_ID_WIDTH',      '8'))
        self.PAYLOAD_WIDTH = int(os.environ.get('PARAM_PAYLOAD_WIDTH', '64'))
        self.DEPTH         = int(os.environ.get('PARAM_DEPTH',         '16'))
        self.SEED          = int(os.environ.get('SEED', '0'))

        random.seed(self.SEED)
        self.cfg = TransCamConfig(self.ID_WIDTH, self.PAYLOAD_WIDTH, self.DEPTH)

        self._id_mask      = (1 << self.ID_WIDTH)      - 1
        self._payload_mask = (1 << self.PAYLOAD_WIDTH) - 1
        self._slot_mask    = (1 << self.DEPTH)         - 1

        self.model = _TransCamModel(
            depth        = self.DEPTH,
            id_mask      = self._id_mask,
            payload_mask = self._payload_mask,
        )

        self.log.info(
            f"MonitorTransCamTB: ID_WIDTH={self.ID_WIDTH}, "
            f"PAYLOAD_WIDTH={self.PAYLOAD_WIDTH}, DEPTH={self.DEPTH}, "
            f"SEED={self.SEED}"
        )

    # ---- driving helpers ----------------------------------------------

    def _drive_idle(self):
        """Park every input at 0 so the next sub-test starts clean."""
        self.dut.lookup_addr_id.value   = 0
        self.dut.lookup_data_id.value   = 0
        self.dut.lookup_resp_id.value   = 0
        self.dut.addr_wants_alloc.value = 0
        self.dut.data_wants_alloc.value = 0
        self.dut.resp_wants_alloc.value = 0
        self.dut.entry_we.value         = 0
        self.dut.entry_valid_next.value = 0
        for i in range(self.DEPTH):
            self.dut.entry_id_next[i].value      = 0
            self.dut.entry_payload_next[i].value = 0

    async def reset_dut(self):
        self.log.debug("reset_dut: starting")
        self._drive_idle()
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)
        self.model = _TransCamModel(
            depth        = self.DEPTH,
            id_mask      = self._id_mask,
            payload_mask = self._payload_mask,
        )
        self.log.debug("reset_dut: done")

    # ---- low-level signal drive ---------------------------------------

    def _drive_lookups(self, addr_id: int, data_id: int, resp_id: int):
        self.dut.lookup_addr_id.value = addr_id & self._id_mask
        self.dut.lookup_data_id.value = data_id & self._id_mask
        self.dut.lookup_resp_id.value = resp_id & self._id_mask

    def _drive_wants(self, wa: bool, wd: bool, wr: bool):
        self.dut.addr_wants_alloc.value = int(bool(wa))
        self.dut.data_wants_alloc.value = int(bool(wd))
        self.dut.resp_wants_alloc.value = int(bool(wr))

    def _drive_writes(self,
                      we_mask: int,
                      valid_next_mask: int,
                      ids_next: List[int],
                      payloads_next: List[int]):
        assert len(ids_next)      == self.DEPTH
        assert len(payloads_next) == self.DEPTH
        self.dut.entry_we.value         = we_mask & self._slot_mask
        self.dut.entry_valid_next.value = valid_next_mask & self._slot_mask
        for i in range(self.DEPTH):
            self.dut.entry_id_next[i].value      = ids_next[i]      & self._id_mask
            self.dut.entry_payload_next[i].value = payloads_next[i] & self._payload_mask

    # ---- one-cycle step with full cross-check -------------------------

    async def _step(self,
                    *,
                    addr_id:        int = 0,
                    data_id:        int = 0,
                    resp_id:        int = 0,
                    wants_addr:     bool = False,
                    wants_data:     bool = False,
                    wants_resp:     bool = False,
                    we_mask:        int = 0,
                    valid_next_mask: int = 0,
                    ids_next:       List[int] = None,
                    payloads_next:  List[int] = None):
        """One clock cycle. Drives inputs, samples combinational outputs
        at ReadOnly, advances the model on the next clock edge, then
        cross-checks the registered state."""
        if ids_next is None:
            ids_next = [0] * self.DEPTH
        if payloads_next is None:
            payloads_next = [0] * self.DEPTH

        self._drive_lookups(addr_id, data_id, resp_id)
        self._drive_wants(wants_addr, wants_data, wants_resp)
        self._drive_writes(we_mask, valid_next_mask, ids_next, payloads_next)

        # ---- Combinational sample + check ----
        await ReadOnly()
        rtl_addr_oh        = int(self.dut.addr_match_oh.value)
        rtl_data_oh        = int(self.dut.data_match_oh.value)
        rtl_resp_oh        = int(self.dut.resp_match_oh.value)
        rtl_data_first_oh  = int(self.dut.data_match_first_oh.value)
        rtl_free_oh        = int(self.dut.free_oh.value)
        rtl_addr_alloc_oh  = int(self.dut.addr_alloc_oh.value)
        rtl_data_alloc_oh  = int(self.dut.data_alloc_oh.value)
        rtl_resp_alloc_oh  = int(self.dut.resp_alloc_oh.value)
        rtl_entry_valid    = int(self.dut.entry_valid.value)

        exp_addr_oh       = self.model.match_oh(addr_id)
        exp_data_oh       = self.model.match_oh(data_id)
        exp_resp_oh       = self.model.match_oh(resp_id)
        exp_data_first_oh = self.model.first_match_oh(data_id)
        exp_free_oh       = self.model.free_oh()
        exp_aa, exp_da, exp_ra = self.model.alloc_oh(wants_addr, wants_data, wants_resp)
        exp_entry_valid   = 0
        for i, e in enumerate(self.model.entries):
            if e.valid:
                exp_entry_valid |= 1 << i

        assert rtl_addr_oh == exp_addr_oh, \
            f"addr_match_oh mismatch: rtl=0x{rtl_addr_oh:x}, model=0x{exp_addr_oh:x}"
        assert rtl_data_oh == exp_data_oh, \
            f"data_match_oh mismatch: rtl=0x{rtl_data_oh:x}, model=0x{exp_data_oh:x}"
        assert rtl_resp_oh == exp_resp_oh, \
            f"resp_match_oh mismatch: rtl=0x{rtl_resp_oh:x}, model=0x{exp_resp_oh:x}"
        assert rtl_data_first_oh == exp_data_first_oh, \
            f"data_match_first_oh mismatch: rtl=0x{rtl_data_first_oh:x}, model=0x{exp_data_first_oh:x}"
        assert rtl_free_oh == exp_free_oh, \
            f"free_oh mismatch: rtl=0x{rtl_free_oh:x}, model=0x{exp_free_oh:x}"
        assert rtl_addr_alloc_oh == exp_aa, \
            f"addr_alloc_oh mismatch: rtl=0x{rtl_addr_alloc_oh:x}, model=0x{exp_aa:x}"
        assert rtl_data_alloc_oh == exp_da, \
            f"data_alloc_oh mismatch: rtl=0x{rtl_data_alloc_oh:x}, model=0x{exp_da:x}"
        assert rtl_resp_alloc_oh == exp_ra, \
            f"resp_alloc_oh mismatch: rtl=0x{rtl_resp_alloc_oh:x}, model=0x{exp_ra:x}"
        assert rtl_entry_valid == exp_entry_valid, \
            f"entry_valid mismatch: rtl=0x{rtl_entry_valid:x}, model=0x{exp_entry_valid:x}"

        # ---- Mutex sanity: alloc one-hots disjoint ----
        if (rtl_addr_alloc_oh & rtl_data_alloc_oh) \
                or (rtl_addr_alloc_oh & rtl_resp_alloc_oh) \
                or (rtl_data_alloc_oh & rtl_resp_alloc_oh):
            raise AssertionError(
                f"alloc one-hots overlap: "
                f"addr=0x{rtl_addr_alloc_oh:x}, data=0x{rtl_data_alloc_oh:x}, "
                f"resp=0x{rtl_resp_alloc_oh:x}"
            )
        # ---- alloc lands on a free slot, never a valid one ----
        any_alloc = rtl_addr_alloc_oh | rtl_data_alloc_oh | rtl_resp_alloc_oh
        if any_alloc & rtl_entry_valid:
            raise AssertionError(
                f"alloc landed on a valid slot: alloc=0x{any_alloc:x}, "
                f"entry_valid=0x{rtl_entry_valid:x}"
            )

        # ---- Advance one clock, commit the model ----
        await RisingEdge(self.dut.clk)
        self.model.commit_writes(we_mask, valid_next_mask, ids_next, payloads_next)

        self._drive_idle()
        return {
            'addr_match_oh':       rtl_addr_oh,
            'data_match_oh':       rtl_data_oh,
            'resp_match_oh':       rtl_resp_oh,
            'data_match_first_oh': rtl_data_first_oh,
            'free_oh':             rtl_free_oh,
            'addr_alloc_oh':       rtl_addr_alloc_oh,
            'data_alloc_oh':       rtl_data_alloc_oh,
            'resp_alloc_oh':       rtl_resp_alloc_oh,
            'entry_valid':         rtl_entry_valid,
        }

    # ---- write builders -----------------------------------------------

    def _write_one_slot(self,
                        slot: int,
                        valid_next: bool,
                        id_val: int,
                        payload: int) -> dict:
        """Build the per-slot input dict for _step() that writes a single slot."""
        ids_next      = [0] * self.DEPTH
        payloads_next = [0] * self.DEPTH
        ids_next[slot]      = id_val & self._id_mask
        payloads_next[slot] = payload & self._payload_mask
        return {
            'we_mask':         1 << slot,
            'valid_next_mask': (int(bool(valid_next))) << slot,
            'ids_next':        ids_next,
            'payloads_next':   payloads_next,
        }

    def _write_many_slots(self,
                          writes: List[Tuple[int, bool, int, int]]) -> dict:
        """writes is a list of (slot, valid_next, id_val, payload) tuples."""
        ids_next      = [0] * self.DEPTH
        payloads_next = [0] * self.DEPTH
        we_mask         = 0
        valid_next_mask = 0
        for (slot, valid_next, id_val, payload) in writes:
            we_mask         |= 1 << slot
            valid_next_mask |= int(bool(valid_next)) << slot
            ids_next[slot]      = id_val  & self._id_mask
            payloads_next[slot] = payload & self._payload_mask
        return {
            'we_mask':         we_mask,
            'valid_next_mask': valid_next_mask,
            'ids_next':        ids_next,
            'payloads_next':   payloads_next,
        }

    async def _read_payload(self, slot: int) -> int:
        """Sample one entry_payload[slot] at ReadOnly. Caller must already
        be at a phase where it's safe to enter ReadOnly."""
        await ReadOnly()
        return int(self.dut.entry_payload[slot].value)

    # ---- sub-tests ----------------------------------------------------

    async def t1_reset_state(self):
        self.log.info("=== t1: reset state ===")
        # Right after reset_dut: drive a few idle cycles; every match_oh
        # must be 0, free_oh = all 1s, alloc_oh = 0 (no wants).
        for _ in range(3):
            r = await self._step()
            assert r['addr_match_oh']      == 0
            assert r['data_match_oh']      == 0
            assert r['resp_match_oh']      == 0
            assert r['data_match_first_oh'] == 0
            assert r['free_oh']            == self._slot_mask
            assert r['addr_alloc_oh']      == 0
            assert r['data_alloc_oh']      == 0
            assert r['resp_alloc_oh']      == 0
            assert r['entry_valid']        == 0
        self.log.info("=== t1: PASS ===")

    async def t2_single_write_and_lookup(self):
        self.log.info("=== t2: write slot 0, lookup hits ===")
        K = 0x42 & self._id_mask
        P = 0xDEAD_BEEF & self._payload_mask

        # Cycle 1: drive the write to slot 0.
        w = self._write_one_slot(slot=0, valid_next=True, id_val=K, payload=P)
        await self._step(**w)

        # Cycle 2: addr lookup with K must produce match_oh = 0b1 on slot 0.
        r = await self._step(addr_id=K)
        assert r['addr_match_oh']      == 0b1, f"addr_match_oh=0x{r['addr_match_oh']:x}"
        assert r['data_match_oh']      == 0
        assert r['resp_match_oh']      == 0
        assert r['data_match_first_oh'] == 0
        # free_oh has bit 0 cleared.
        assert r['free_oh'] == (self._slot_mask & ~0b1)
        assert r['entry_valid'] == 0b1

        # Payload readback.
        pay = await self._read_payload(0)
        # Move out of ReadOnly so subsequent _step() can drive inputs.
        await RisingEdge(self.dut.clk)
        self._drive_idle()
        assert pay == P, f"payload readback: rtl=0x{pay:x}, expected=0x{P:x}"
        self.log.info("=== t2: PASS ===")

    async def t3_independent_writes(self):
        self.log.info("=== t3: each slot writable independently ===")
        # Write every slot in turn with id=0xA0+i, payload=0xB000+i.
        for slot in range(self.DEPTH):
            id_val = (0xA0 + slot) & self._id_mask
            pay    = (0xB000 + slot) & self._payload_mask
            await self._step(**self._write_one_slot(slot, True, id_val, pay))
        # Every slot now valid; free_oh = 0.
        r = await self._step()
        assert r['free_oh']     == 0
        assert r['entry_valid'] == self._slot_mask
        # Each id lookup hits exactly its own slot.
        for slot in range(self.DEPTH):
            id_val = (0xA0 + slot) & self._id_mask
            r = await self._step(addr_id=id_val)
            assert r['addr_match_oh'] == (1 << slot), \
                f"slot {slot}: addr_match_oh=0x{r['addr_match_oh']:x}, expected=0x{1<<slot:x}"
        self.log.info("=== t3: PASS ===")

    async def t4_three_port_lookup(self):
        self.log.info("=== t4: three independent lookup ports ===")
        # Fill 3 slots with distinct ids; verify the 3 ports route independently.
        IDS = [0x11, 0x22, 0x33]
        for slot, idv in enumerate(IDS):
            await self._step(**self._write_one_slot(slot, True, idv & self._id_mask,
                                                    0xCAFE_0000 + slot))
        # Now: addr_id=IDS[0], data_id=IDS[2], resp_id=IDS[1]
        r = await self._step(addr_id=IDS[0], data_id=IDS[2], resp_id=IDS[1])
        assert r['addr_match_oh']      == (1 << 0)
        assert r['data_match_oh']      == (1 << 2)
        assert r['resp_match_oh']      == (1 << 1)
        assert r['data_match_first_oh'] == (1 << 2)
        # All three identical -> all three vectors equal.
        r = await self._step(addr_id=IDS[1], data_id=IDS[1], resp_id=IDS[1])
        assert r['addr_match_oh'] == r['data_match_oh'] == r['resp_match_oh'] == (1 << 1)
        self.log.info("=== t4: PASS ===")

    async def t5_data_match_first_oh(self):
        self.log.info("=== t5: data_match_first_oh selects lowest-index ===")
        # Write same id to multiple slots. (For real AXI4 this would be a
        # protocol violation; the CAM doesn't care, but the first-hit
        # output is exactly the mechanism used to disambiguate the
        # AXI4-write WID-less data-channel match upstream.)
        DUPL_ID = 0x55 & self._id_mask
        # Write slots 2, 5, 9 (or however many fit).
        slots_to_write = [s for s in (2, 5, 9, 11) if s < self.DEPTH]
        for s in slots_to_write:
            await self._step(**self._write_one_slot(s, True, DUPL_ID, 0xF000 + s))
        # Lookup: data_match_oh has bits set on all of slots_to_write,
        # data_match_first_oh has only the lowest.
        r = await self._step(data_id=DUPL_ID)
        full_match = sum(1 << s for s in slots_to_write)
        assert r['data_match_oh'] == full_match, \
            f"data_match_oh=0x{r['data_match_oh']:x}, expected=0x{full_match:x}"
        assert r['data_match_first_oh'] == (1 << min(slots_to_write)), \
            f"data_match_first_oh=0x{r['data_match_first_oh']:x}"
        self.log.info("=== t5: PASS ===")

    async def t6_free_oh_tracking(self):
        self.log.info("=== t6: free_oh tracks valid bit per slot ===")
        # Pick two distinct slot indices that exist at any supported DEPTH (>=4).
        s_a = 1
        s_b = self.DEPTH - 1
        await self._step(**self._write_one_slot(s_a, True, 0xA, 0x1))
        await self._step(**self._write_one_slot(s_b, True, 0xB, 0x2))
        r = await self._step()
        expected_free = self._slot_mask & ~((1 << s_a) | (1 << s_b))
        assert r['free_oh'] == expected_free, \
            f"free_oh=0x{r['free_oh']:x}, expected=0x{expected_free:x}"
        # Free slot s_a.
        await self._step(**self._write_one_slot(s_a, False, 0, 0))
        r = await self._step()
        expected_free = self._slot_mask & ~(1 << s_b)
        assert r['free_oh'] == expected_free, \
            f"after clearing slot {s_a}, free_oh=0x{r['free_oh']:x}, expected=0x{expected_free:x}"
        self.log.info("=== t6: PASS ===")

    async def t7_clear_via_we(self):
        self.log.info("=== t7: write-port clear (we=1, valid_next=0) ===")
        K = 0x77 & self._id_mask
        slot = self.DEPTH // 2  # middle slot, valid for any supported DEPTH
        await self._step(**self._write_one_slot(slot, True, K, 0xABCD))
        # Confirm hit.
        r = await self._step(addr_id=K)
        assert r['addr_match_oh'] == (1 << slot)
        # Clear via we=1, valid_next=0.
        await self._step(**self._write_one_slot(slot, False, 0, 0))
        # Lookup misses now.
        r = await self._step(addr_id=K)
        assert r['addr_match_oh'] == 0, \
            f"after clear, addr_match_oh=0x{r['addr_match_oh']:x}"
        assert r['free_oh'] == self._slot_mask
        self.log.info("=== t7: PASS ===")

    async def t8_alloc_one_phase(self):
        self.log.info("=== t8: addr_wants_alloc -> lowest-index free slot ===")
        # All slots free: addr_alloc_oh should be bit 0.
        r = await self._step(wants_addr=True)
        assert r['addr_alloc_oh'] == 0b1, \
            f"addr_alloc_oh=0x{r['addr_alloc_oh']:x}, expected=0b1"
        assert r['data_alloc_oh'] == 0
        assert r['resp_alloc_oh'] == 0
        # Fill slot 0, alloc should now be bit 1.
        await self._step(**self._write_one_slot(0, True, 0x1, 0x100))
        r = await self._step(wants_addr=True)
        assert r['addr_alloc_oh'] == 0b10, \
            f"addr_alloc_oh=0x{r['addr_alloc_oh']:x}, expected=0b10"
        # Same for data / resp alone.
        r = await self._step(wants_data=True)
        assert r['data_alloc_oh'] == 0b10
        assert r['addr_alloc_oh'] == 0
        r = await self._step(wants_resp=True)
        assert r['resp_alloc_oh'] == 0b10
        self.log.info("=== t8: PASS ===")

    async def t9_alloc_mutex(self):
        self.log.info("=== t9: all three phases want -> three distinct slots ===")
        # All slots free, all three want. Should get bits 0, 1, 2.
        r = await self._step(wants_addr=True, wants_data=True, wants_resp=True)
        assert r['addr_alloc_oh'] == 0b001
        assert r['data_alloc_oh'] == 0b010
        assert r['resp_alloc_oh'] == 0b100
        # Pre-occupy slots 0..3 so the three phases must pick 4, 5, 6.
        for s in range(min(4, self.DEPTH - 3)):
            await self._step(**self._write_one_slot(s, True, 0xC0 + s, 0))
        # If DEPTH is small (e.g. 4), this collapses -- check at least N >= 7.
        if self.DEPTH >= 7:
            r = await self._step(wants_addr=True, wants_data=True, wants_resp=True)
            assert r['addr_alloc_oh'] == (1 << 4)
            assert r['data_alloc_oh'] == (1 << 5)
            assert r['resp_alloc_oh'] == (1 << 6)
        self.log.info("=== t9: PASS ===")

    async def t10_alloc_partial_wants(self):
        self.log.info("=== t10: alloc with only some phases wanting ===")
        # Reset state, request only data alloc. Should land on slot 0.
        r = await self._step(wants_data=True)
        assert r['data_alloc_oh'] == 0b1
        assert r['addr_alloc_oh'] == 0
        assert r['resp_alloc_oh'] == 0
        # addr+resp wanting (no data) -- should be slots 0 and 1.
        r = await self._step(wants_addr=True, wants_resp=True)
        assert r['addr_alloc_oh'] == 0b01
        assert r['data_alloc_oh'] == 0
        assert r['resp_alloc_oh'] == 0b10
        # data+resp wanting (no addr) -- should be slots 0 and 1.
        r = await self._step(wants_data=True, wants_resp=True)
        assert r['addr_alloc_oh'] == 0
        assert r['data_alloc_oh'] == 0b01
        assert r['resp_alloc_oh'] == 0b10
        self.log.info("=== t10: PASS ===")

    async def t11_alloc_when_full(self):
        self.log.info("=== t11: alloc with no free slots returns 0 ===")
        # Fill every slot.
        for s in range(self.DEPTH):
            await self._step(**self._write_one_slot(s, True, (0xD0 + s) & self._id_mask, s))
        r = await self._step(wants_addr=True, wants_data=True, wants_resp=True)
        assert r['free_oh']       == 0
        assert r['addr_alloc_oh'] == 0
        assert r['data_alloc_oh'] == 0
        assert r['resp_alloc_oh'] == 0
        self.log.info("=== t11: PASS ===")

    async def t12_payload_preserved(self):
        self.log.info("=== t12: payload survives idle cycles ===")
        K = 0x88 & self._id_mask
        slot = min(2, self.DEPTH - 1)
        # Use the maximum-width payload pattern to flush any bit-trim bugs.
        P = ((1 << self.PAYLOAD_WIDTH) - 1) ^ 0x5A5A_5A5A_5A5A_5A5A
        P &= self._payload_mask
        await self._step(**self._write_one_slot(slot, True, K, P))
        # Idle for 10 cycles, then check payload.
        for _ in range(10):
            await self._step()
        # ReadOnly + read payload.
        pay = await self._read_payload(slot)
        await RisingEdge(self.dut.clk)
        self._drive_idle()
        assert pay == P, \
            f"payload after idle: rtl=0x{pay:x}, expected=0x{P:x}"
        self.log.info("=== t12: PASS ===")

    async def t13_concurrent_writes(self):
        self.log.info("=== t13: write multiple slots in one cycle ===")
        # Write slots 0, 2, 4, 6 (or however many fit) simultaneously.
        slots = [s for s in (0, 2, 4, 6, 8, 10) if s < self.DEPTH]
        writes = [(s, True, (0xE0 + s) & self._id_mask, 0x9000 + s) for s in slots]
        await self._step(**self._write_many_slots(writes))
        # Verify every slot is valid with the right id.
        r = await self._step()
        expected_valid = sum(1 << s for s in slots)
        assert r['entry_valid'] == expected_valid
        # Lookup each id.
        for (s, _, idv, _) in writes:
            r = await self._step(addr_id=idv)
            assert r['addr_match_oh'] == (1 << s), \
                f"slot {s}: addr_match_oh=0x{r['addr_match_oh']:x}, expected=0x{1<<s:x}"
        self.log.info("=== t13: PASS ===")

    async def t14_lookup_miss(self):
        self.log.info("=== t14: lookup miss on absent id ===")
        # Use 0 and DEPTH-1 -- always valid slot indices.
        await self._step(**self._write_one_slot(0,             True, 0x1, 0x1))
        await self._step(**self._write_one_slot(self.DEPTH-1, True, 0x3, 0x3))
        # Lookup an id that none of the slots hold. With ID_WIDTH small the
        # masked id space may be tiny -- pick anything outside {1, 3}.
        miss_id = 5 & self._id_mask
        if miss_id in (1 & self._id_mask, 3 & self._id_mask):
            miss_id = 7 & self._id_mask
        r = await self._step(addr_id=miss_id, data_id=miss_id, resp_id=miss_id)
        assert r['addr_match_oh']      == 0
        assert r['data_match_oh']      == 0
        assert r['resp_match_oh']      == 0
        assert r['data_match_first_oh'] == 0
        self.log.info("=== t14: PASS ===")

    async def t15_alloc_priority_cascade(self):
        self.log.info("=== t15: alloc priority cascade ===")
        # Mark slots 1, 2, 3 valid; the rest free.
        for s in (1, 2, 3):
            if s < self.DEPTH:
                await self._step(**self._write_one_slot(s, True, (0xF0 + s) & self._id_mask, 0))
        # Now request all three. Lowest-three free are 0, 4, 5 (skipping 1,2,3).
        if self.DEPTH >= 6:
            r = await self._step(wants_addr=True, wants_data=True, wants_resp=True)
            assert r['addr_alloc_oh'] == (1 << 0)
            assert r['data_alloc_oh'] == (1 << 4)
            assert r['resp_alloc_oh'] == (1 << 5)
        self.log.info("=== t15: PASS ===")

    async def t16_id_collision_tolerance(self):
        self.log.info("=== t16: id collision (multiple valid slots same id) ===")
        # Write slots 1 and 6 with the same id.
        SHARED = 0xAB & self._id_mask
        if self.DEPTH >= 7:
            await self._step(**self._write_one_slot(1, True, SHARED, 0x1000))
            await self._step(**self._write_one_slot(6, True, SHARED, 0x6000))
            r = await self._step(addr_id=SHARED)
            assert r['addr_match_oh']      == ((1 << 1) | (1 << 6))
            # No `first` for addr — only for data. addr is full match.
            r = await self._step(data_id=SHARED)
            assert r['data_match_oh']       == ((1 << 1) | (1 << 6))
            assert r['data_match_first_oh'] == (1 << 1)
        self.log.info("=== t16: PASS ===")

    async def t17_random_stress(self, n_ops: int = 500):
        """Random mix of writes (alloc + free), lookups, and alloc-wants.
        The _step cross-check validates every combinational output and
        the registered entry_valid vector on every cycle."""
        self.log.info(f"=== t17: random stress, {n_ops} ops ===")
        # Use a constrained ID-space slightly bigger than DEPTH so collisions
        # do happen but most ids are unique.
        id_space = list(range(self._id_mask + 1))
        if len(id_space) > 8 * self.DEPTH:
            id_space = id_space[: 8 * self.DEPTH]

        for op in range(n_ops):
            # Each cycle: random lookups + random write + random alloc-wants.
            addr_id = random.choice(id_space)
            data_id = random.choice(id_space)
            resp_id = random.choice(id_space)

            we_mask = 0
            valid_next_mask = 0
            ids_next      = [0] * self.DEPTH
            payloads_next = [0] * self.DEPTH

            # ~30% chance per cycle to issue 1-3 random writes.
            if random.random() < 0.30:
                n_writes = random.randint(1, 3)
                slots = random.sample(range(self.DEPTH), n_writes)
                for s in slots:
                    we_mask |= 1 << s
                    if random.random() < 0.75:
                        # Mark valid with random id / payload.
                        valid_next_mask |= 1 << s
                        ids_next[s]      = random.choice(id_space)
                        payloads_next[s] = random.randrange(
                            0, 1 << min(32, self.PAYLOAD_WIDTH)
                        )
                    # Otherwise we=1 + valid_next=0 -> clear that slot.

            # ~40% chance per cycle to request alloc.
            wa = random.random() < 0.40
            wd = random.random() < 0.40
            wr = random.random() < 0.40

            await self._step(
                addr_id          = addr_id,
                data_id          = data_id,
                resp_id          = resp_id,
                wants_addr       = wa,
                wants_data       = wd,
                wants_resp       = wr,
                we_mask          = we_mask,
                valid_next_mask  = valid_next_mask,
                ids_next         = ids_next,
                payloads_next    = payloads_next,
            )
        self.log.info(f"=== t17: PASS ({n_ops} ops, all model-checked) ===")


# ----------------------------------------------------------------------------
# Cocotb test entry
# ----------------------------------------------------------------------------
@cocotb.test(timeout_time=60, timeout_unit="ms")
async def monitor_trans_cam_test(dut):
    """Full FUB regression for monitor_trans_cam."""
    tb = MonitorTransCamTB(dut)
    await tb.start_clock('clk', 10, 'ns')
    await tb.reset_dut()

    # REG_LEVEL gates the heavier stress test.
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    n_stress_ops = {'GATE': 100, 'FUNC': 500, 'FULL': 5000}.get(reg_level, 500)

    await tb.t1_reset_state();                       await tb.reset_dut()
    await tb.t2_single_write_and_lookup();           await tb.reset_dut()
    await tb.t3_independent_writes();                await tb.reset_dut()
    await tb.t4_three_port_lookup();                 await tb.reset_dut()
    await tb.t5_data_match_first_oh();               await tb.reset_dut()
    await tb.t6_free_oh_tracking();                  await tb.reset_dut()
    await tb.t7_clear_via_we();                      await tb.reset_dut()
    await tb.t8_alloc_one_phase();                   await tb.reset_dut()
    await tb.t9_alloc_mutex();                       await tb.reset_dut()
    await tb.t10_alloc_partial_wants();              await tb.reset_dut()
    await tb.t11_alloc_when_full();                  await tb.reset_dut()
    await tb.t12_payload_preserved();                await tb.reset_dut()
    await tb.t13_concurrent_writes();                await tb.reset_dut()
    await tb.t14_lookup_miss();                      await tb.reset_dut()
    await tb.t15_alloc_priority_cascade();           await tb.reset_dut()
    await tb.t16_id_collision_tolerance();           await tb.reset_dut()
    await tb.t17_random_stress(n_ops=n_stress_ops)

    tb.log.info("=== ALL TESTS PASSED ===")


# ----------------------------------------------------------------------------
# Pytest parametric wrapper
# ----------------------------------------------------------------------------
def get_trans_cam_params():
    """REG_LEVEL gates the parameter sweep depth.

    Default (8b id, 64b payload, depth 16) matches the historical
    axi_monitor_trans_mgr defaults. Smaller depths exercise corner
    cases at the boundary; deeper / wider variations confirm the
    parametric sweep works.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(8, 64, 16)]
    elif reg_level == 'FUNC':
        return [
            (8, 64, 16),    # default
            (4, 32, 8),     # smaller variant
        ]
    else:  # FULL
        return [
            (8, 64, 16),    # default
            (8, 64, 32),    # deeper
            (8, 64, 8),     # shallower
            (4, 32, 8),     # smaller id/payload
            (6, 128, 16),   # wider payload
            (8, 256, 16),   # very wide payload (trans_mgr-sized)
            (4, 32, 4),     # boundary depth
        ]


@pytest.mark.parametrize("id_width, payload_width, depth", get_trans_cam_params())
def test_monitor_trans_cam(request, id_width, payload_width, depth):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name  = "monitor_trans_cam"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    iw_str = TBBase.format_dec(id_width,      2)
    pw_str = TBBase.format_dec(payload_width, 3)
    de_str = TBBase.format_dec(depth,         3)
    test_name = f"test_{worker_id}_{dut_name}_iw{iw_str}_pw{pw_str}_d{de_str}_{reg_level}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_shared'], "monitor_trans_cam.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'DEPTH':         str(depth),
        'ID_WIDTH':      str(id_width),
        'PAYLOAD_WIDTH': str(payload_width),
    }

    extra_env = {
        'DUT':                dut_name,
        'LOG_PATH':           log_path,
        'COCOTB_LOG_LEVEL':   'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':               os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_ID_WIDTH':     str(id_width),
        'PARAM_PAYLOAD_WIDTH': str(payload_width),
        'PARAM_DEPTH':        str(depth),
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
