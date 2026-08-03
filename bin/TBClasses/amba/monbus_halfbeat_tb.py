# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: MonbusHalfbeatTB
# Purpose: Testbench for monbus_halfbeat
# Subsystem: framework
#
# Extracted from val/amba/test_monbus_halfbeat.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from typing import List, Tuple
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from TBClasses.shared.tbbase import TBBase
from TBClasses.monbus.monbus_compressor import Encoder


class MonbusHalfbeatTB(TBBase):
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
        self.dut.rst_n.value        = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value        = 1
        await self.wait_clocks('clk', 2)
        self.captured_slots.clear()

    async def drive_records_gapless(self, records: List[Tuple[int, int]]):
        """Hold in_valid high; advance to the next record on each accepted
        cycle (no inter-record bubbles). Matches a high-rate trace stream and
        keeps the packer from flushing mid-stream."""
        idx = 0
        while idx < len(records):
            pkt, ts = records[idx]
            self.dut.in_packet.value    = pkt
            self.dut.in_source_ts.value = ts
            self.dut.in_valid.value     = 1
            await ReadOnly()
            if int(self.dut.in_ready.value) == 1:
                idx += 1
            await RisingEdge(self.dut.clk)
        self.dut.in_valid.value = 0   # go idle -> packer flushes trailing half

    async def capture_loop(self, n_slots_expected: int):
        while len(self.captured_slots) < n_slots_expected:
            await ReadOnly()
            if (int(self.dut.out_valid.value) == 1
                    and int(self.dut.out_ready.value) == 1):
                self.captured_slots.append(int(self.dut.out_slot.value))
            await RisingEdge(self.dut.clk)

    async def _backpressure(self):
        """Toggle out_ready (1 on / 2 off) to stress the compressor's output
        backpressure path -- reproduces the group's write-FIFO stalls."""
        import itertools
        for v in itertools.cycle([1, 0, 0]):
            self.dut.out_ready.value = v
            await RisingEdge(self.dut.clk)

    async def run_records_through(self, records, expected_slots):
        bp = int(os.environ.get('BP', '0'))
        if bp:
            self.dut.out_ready.value = 0
            cocotb.start_soon(self._backpressure())
        else:
            self.dut.out_ready.value = 1
        cap = cocotb.start_soon(self.capture_loop(len(expected_slots)))
        await self.drive_records_gapless(records)
        await cap
        assert len(self.captured_slots) == len(expected_slots), (
            f"slot count mismatch: rtl={len(self.captured_slots)}, "
            f"golden={len(expected_slots)}"
        )
        for i, (rtl, golden) in enumerate(zip(self.captured_slots, expected_slots)):
            assert rtl == golden, (
                f"slot {i} mismatch: rtl=0x{rtl:016x}, golden=0x{golden:016x}"
            )

    async def verify_stats(self, enc: Encoder):
        await ReadOnly()
        assert int(self.dut.stat_tier1_a.value) == enc.stats.tier1_a_hits
        assert int(self.dut.stat_tier1_b.value) == enc.stats.tier1_b_hits
        assert int(self.dut.stat_tier1_c.value) == enc.stats.tier1_c_hits
        assert int(self.dut.stat_tier0.value)   == enc.stats.tier0_escapes
        await RisingEdge(self.dut.clk)
