# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CamPipeTB
# Purpose: Testbench for monbus_cam_pipe
# Subsystem: framework
#
# Extracted from val/amba/test_monbus_cam_pipe.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from typing import List
from cocotb.triggers import RisingEdge, ReadOnly
from TBClasses.shared.tbbase import TBBase


class CamPipeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

    async def reset(self):
        self.dut.en.value = 0
        self.dut.key.value = 0
        self.dut.new_data.value = 0
        self.dut.new_ts.value = 0
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)

    async def run_stream(self, accesses: List[tuple]):
        """accesses = list of (en, key, new_data, new_ts).
        Captures the reference result on each en=1 cycle and the pipelined
        result on each pipe_valid cycle, then asserts the two sequences match."""
        ref_seq = []
        pipe_seq = []
        # Drive, plus a few trailing idle cycles to flush the pipe.
        seq = list(accesses) + [(0, 0, 0, 0)] * 4
        for (en, key, nd, nts) in seq:
            self.dut.en.value = en
            self.dut.key.value = key
            self.dut.new_data.value = nd
            self.dut.new_ts.value = nts
            await ReadOnly()
            if en:
                ref_seq.append((int(self.dut.ref_hit.value), int(self.dut.ref_idx.value),
                                int(self.dut.ref_old_data.value), int(self.dut.ref_old_ts.value)))
            if int(self.dut.pipe_valid.value) == 1:
                pipe_seq.append((int(self.dut.pipe_hit.value), int(self.dut.pipe_idx.value),
                                 int(self.dut.pipe_old_data.value), int(self.dut.pipe_old_ts.value)))
            await RisingEdge(self.dut.clk)

        assert len(ref_seq) == len(pipe_seq), \
            f"count mismatch: ref={len(ref_seq)} pipe={len(pipe_seq)}"
        for i, (r, p) in enumerate(zip(ref_seq, pipe_seq)):
            assert r == p, f"access {i}: ref={r} pipe={p}"
        return len(ref_seq)
