# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: MonbusCompressorTB
# Purpose: Testbench for monbus_compressor
# Subsystem: framework
#
# Extracted from val/amba/test_monbus_compressor.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from typing import List, Tuple
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from TBClasses.shared.tbbase import TBBase
from TBClasses.monbus.monbus_compressor import Encoder


class MonbusCompressorTB(TBBase):
    """Drive records in, capture slots out, cross-check against Python golden."""

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)
        self.captured_slots: List[int] = []

    async def reset_dut(self):
        self.dut.in_valid.value     = 0
        self.dut.in_packet.value    = 0
        self.dut.in_source_ts.value = 0
        self.dut.out_ready.value    = 1
        self.dut.clear.value        = 0
        self.dut.rst_n.value        = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value        = 1
        await self.wait_clocks('clk', 2)
        self.captured_slots.clear()

    async def drive_record(self, packet: int, source_ts: int):
        """Drive a single record through the valid/ready handshake.

        Pattern: assert valid, sample in_ready at ReadOnly (pre-edge),
        loop until ready is high, then advance ONE edge (handshake
        fires at that edge) and deassert valid immediately so the
        same record isn't double-handshook on subsequent IDLE cycles.
        """
        self.dut.in_packet.value    = packet
        self.dut.in_source_ts.value = source_ts
        self.dut.in_valid.value     = 1
        while True:
            await ReadOnly()
            if int(self.dut.in_ready.value) == 1:
                break
            await RisingEdge(self.dut.clk)
        # Next rising edge handshakes; deassert valid immediately after.
        await RisingEdge(self.dut.clk)
        self.dut.in_valid.value = 0

    async def capture_loop(self, n_slots_expected: int):
        """Sample one slot per cycle whenever out_valid && out_ready."""
        while len(self.captured_slots) < n_slots_expected:
            await ReadOnly()
            if (int(self.dut.out_valid.value) == 1
                    and int(self.dut.out_ready.value) == 1):
                self.captured_slots.append(int(self.dut.out_slot.value))
            await RisingEdge(self.dut.clk)

    async def run_records_through(self,
                                  records: List[Tuple[int, int]],
                                  expected_slots: List[int]):
        """Drive all records and assert the captured slots match exactly."""
        # Always ready to absorb outputs (no backpressure).
        self.dut.out_ready.value = 1
        # Start the capture in parallel with the driver.
        cap = cocotb.start_soon(self.capture_loop(len(expected_slots)))
        for pkt, ts in records:
            await self.drive_record(pkt, ts)
        # Wait for the capture to finish (or time out).
        await cap
        # Compare lengths first, then slot-by-slot.
        assert len(self.captured_slots) == len(expected_slots), (
            f"slot count mismatch: rtl={len(self.captured_slots)}, "
            f"golden={len(expected_slots)}"
        )
        for i, (rtl, golden) in enumerate(zip(self.captured_slots, expected_slots)):
            assert rtl == golden, (
                f"slot {i} mismatch: rtl=0x{rtl:016x}, golden=0x{golden:016x}"
            )

    async def verify_stats(self, enc: Encoder):
        """After all records drive through, the RTL's stat counters
        should match the Python encoder's per-tier counts."""
        await ReadOnly()
        rtl_a    = int(self.dut.stat_tier1_a.value)
        rtl_b    = int(self.dut.stat_tier1_b.value)
        rtl_c    = int(self.dut.stat_tier1_c.value)
        rtl_t0   = int(self.dut.stat_tier0.value)
        assert rtl_a  == enc.stats.tier1_a_hits, \
            f"tier1_a mismatch: rtl={rtl_a}, py={enc.stats.tier1_a_hits}"
        assert rtl_b  == enc.stats.tier1_b_hits, \
            f"tier1_b mismatch: rtl={rtl_b}, py={enc.stats.tier1_b_hits}"
        assert rtl_c  == enc.stats.tier1_c_hits, \
            f"tier1_c mismatch: rtl={rtl_c}, py={enc.stats.tier1_c_hits}"
        assert rtl_t0 == enc.stats.tier0_escapes, \
            f"tier0 mismatch: rtl={rtl_t0}, py={enc.stats.tier0_escapes}"
        # Leave the ReadOnly phase so the next phase can drive signals.
        await RisingEdge(self.dut.clk)
