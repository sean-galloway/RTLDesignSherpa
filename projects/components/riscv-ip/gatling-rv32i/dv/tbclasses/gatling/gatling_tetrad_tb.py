# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gatling_tetrad_tb
# Purpose: cocotb TB class for gatling_tetrad on gatling_tetrad_tb_top: the
#          barrel's program loading and RVFI capture (GatlingTB), plus the
#          cell seams the Xcell instructions reach -- a per-cell input-memory
#          feeder, a result-memory drain, a FLUSH acceptor and a KICK monitor,
#          all driven from one per-cycle loop with seeded random gaps.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-11-26

"""TB class for gatling sequencing its tetrad.

The cell blocks are real (cell_mem_in, alu_infer_top, cell_mem_out); what
the TB models is the rest of the cell, at its seams:

- the rx demux: ``feed(c, lines)`` queues input lines for cell ``c``; the
  loop writes them at the cell's tail, one per cycle at most, honoring
  ``min_wr_ready`` and a random gap (``fill_gap``).
- the packetizer: the loop reads cell ``c``'s result memory in order when it
  holds a line (``drain_gap``), and records every line.
- the drain controller: ``flush_ready`` with a random gap; every accepted
  command is recorded.
- the tetrad MonBus: every KICK pulse is recorded with its cycle.

Everything is sampled on the falling edge, where every DUT output is settled.
"""

import random

from cocotb.triggers import FallingEdge, RisingEdge

from gatling.gatling_tb import GatlingTB


class _Vec:
    """A packed per-cell input vector: cell c in bits [c*w +: w]."""

    def __init__(self, sig, n: int, w: int):
        self.sig, self.n, self.w = sig, n, w
        self.vals = [0] * n
        self.flush()

    def set(self, c: int, v: int):
        self.vals[c] = v & ((1 << self.w) - 1)

    def flush(self):
        word = 0
        for c, v in enumerate(self.vals):
            word |= v << (c * self.w)
        self.sig.value = word


def field(sig, c: int, w: int) -> int:
    return (int(sig.value) >> (c * w)) & ((1 << w) - 1)


class GatlingTetradTB(GatlingTB):
    """Drive gatling_tetrad_tb_top."""

    def __init__(self, dut, reset_addr: int = 0, seed: int = 1):
        super().__init__(dut, reset_addr)
        n = self.num_harts
        self.rng = random.Random(seed)
        self.in_depth = 1 << len(dut.min_wr_addr) // n
        self.out_depth = 1 << len(dut.mout_rd_addr) // n
        self.in_aw = len(dut.min_wr_addr) // n
        self.out_aw = len(dut.mout_rd_addr) // n
        self.in_occ_w = len(dut.min_occupancy) // n
        self.out_occ_w = len(dut.mout_occupancy) // n
        self.cfg_func = _Vec(dut.cfg_func_sel, n, 9)
        self.cfg_lines = _Vec(dut.cfg_op_lines, n, 2)
        self.cfg_thr = _Vec(dut.cfg_threshold, n, 16)
        self.cfg_cb = _Vec(dut.cfg_credit_batch, n, 32)
        self.wr_valid = _Vec(dut.min_wr_valid, n, 1)
        self.wr_addr = _Vec(dut.min_wr_addr, n, self.in_aw)
        self.wr_data = _Vec(dut.min_wr_data, n, 32)
        self.rd_valid = _Vec(dut.mout_rd_valid, n, 1)
        self.rd_addr = _Vec(dut.mout_rd_addr, n, self.out_aw)
        self.f_ready = _Vec(dut.flush_ready, n, 1)
        self.reset_seams()

    def reset_seams(self):
        n = self.num_harts
        self.pending = [[] for _ in range(n)]     # lines still to feed
        self.in_tail = [0] * n
        self.out_head = [0] * n
        self.rd_inflight = [False] * n
        self.results = [[] for _ in range(n)]     # result lines, in order
        self.flushes = [[] for _ in range(n)]     # (cycle, dest, tag)
        self.kicks = [[] for _ in range(n)]       # (cycle, value)
        self.stall_seen = [set() for _ in range(n)]
        self.fill_gap = 0.0
        self.drain_gap = 0.0
        self.flush_gap = 0.0
        self.drain_enable = [True] * n
        self.flush_enable = [True] * n
        self.cycle = 0

    # ------------------------------------------------------------------
    # Configuration and stimulus
    # ------------------------------------------------------------------

    def configure(self, c: int, func_sel: int, op_lines: int = 1,
                  threshold: int = 0, credit_batch: int = 1):
        self.cfg_func.set(c, func_sel)
        self.cfg_lines.set(c, op_lines)
        self.cfg_thr.set(c, threshold)
        self.cfg_cb.set(c, credit_batch)
        for v in (self.cfg_func, self.cfg_lines, self.cfg_thr, self.cfg_cb):
            v.flush()

    def feed(self, c: int, lines):
        self.pending[c].extend(int(x) & 0xFFFF_FFFF for x in lines)

    def consumed(self, c: int) -> int:
        return field(self.dut.consumed_cnt, c, 16)

    def min_occupancy(self, c: int) -> int:
        return field(self.dut.min_occupancy, c, self.in_occ_w)

    def mout_occupancy(self, c: int) -> int:
        return field(self.dut.mout_occupancy, c, self.out_occ_w)

    def done_mask(self) -> int:
        return int(self.dut.done.value)

    # ------------------------------------------------------------------
    # The per-cycle loop
    # ------------------------------------------------------------------

    def _gap(self, p: float) -> bool:
        return p > 0 and self.rng.random() < p

    def _step_seams(self):
        """At a falling edge: sample what the last rising edge produced, then
        drive the next cycle's seam inputs."""
        dut = self.dut
        n = self.num_harts
        kv = int(dut.kick_valid.value)
        fv = int(dut.flush_valid.value)
        stalled = int(dut.ctx_stalled.value)
        for c in range(n):
            # result-memory read issued last cycle: data is on rd_data now
            if self.rd_inflight[c]:
                self.results[c].append(field(dut.mout_rd_data, c, 32))
                self.rd_inflight[c] = False
            if (kv >> c) & 1:
                self.kicks[c].append((self.cycle, field(dut.kick_value, c, 32)))
            if (stalled >> c) & 1:
                self.stall_seen[c].add(field(dut.ctx_stall_op, c, 3))

        wr_ready = int(dut.min_wr_ready.value)
        for c in range(n):
            # input-memory fill
            if self.pending[c] and (wr_ready >> c) & 1 and not self._gap(self.fill_gap):
                self.wr_valid.set(c, 1)
                self.wr_addr.set(c, self.in_tail[c])
                self.wr_data.set(c, self.pending[c].pop(0))
                self.in_tail[c] = (self.in_tail[c] + 1) % self.in_depth
            else:
                self.wr_valid.set(c, 0)
            # result-memory drain (the read decrements occupancy at the edge)
            if (self.drain_enable[c] and self.mout_occupancy(c) > 0
                    and not self._gap(self.drain_gap)):
                self.rd_valid.set(c, 1)
                self.rd_addr.set(c, self.out_head[c])
                self.out_head[c] = (self.out_head[c] + 1) % self.out_depth
                self.rd_inflight[c] = True
            else:
                self.rd_valid.set(c, 0)
            # drain controller: the command offered now (flush_valid is a
            # flop, stable until the edge) transfers at the next edge if
            # the ready driven now is high
            ready = int(self.flush_enable[c] and not self._gap(self.flush_gap))
            self.f_ready.set(c, ready)
            if ready and (fv >> c) & 1:
                self.flushes[c].append((self.cycle, field(dut.flush_dest, c, 15),
                                        field(dut.flush_tag, c, 4)))
        for v in (self.wr_valid, self.wr_addr, self.wr_data, self.rd_valid,
                  self.rd_addr, self.f_ready):
            v.flush()

    async def run_until_done(self, mask: int, max_cycles: int = 200_000,
                             post_cycles: int = 16, on_cycle=None,
                             settle_results=None):
        """Step the seams and sample RVFI every cycle until every context in
        ``mask`` has halted (done or locked) and the result memories hold no
        line (``settle_results`` names cells whose drain must finish; default
        every cell in ``mask``)."""
        dut = self.dut
        if settle_results is None:
            settle_results = mask
        for _ in range(max_cycles):
            await FallingEdge(dut.clk)
            self._step_seams()
            self._sample(self.cycle, None)
            if on_cycle is not None:
                on_cycle(self.cycle)
            self.cycle += 1
            if (self.halted_mask() & mask) == mask and all(
                    self.mout_occupancy(c) == 0 and not self.rd_inflight[c]
                    for c in range(self.num_harts) if (settle_results >> c) & 1):
                break
        else:
            raise AssertionError(
                f"not done after {max_cycles} cycles: halted {self.halted_mask():#x} "
                f"of {mask:#x}, stalled {int(dut.ctx_stalled.value):#x}, "
                f"pending fill {[len(p) for p in self.pending]}")
        for _ in range(post_cycles):
            await FallingEdge(dut.clk)
            self._step_seams()
            self._sample(self.cycle, None)
            self.cycle += 1
            for c in range(self.num_harts):
                if (mask >> c) & 1 and int(dut.rvfi_valid.value):
                    assert int(dut.rvfi_ctx.value) != c, f"ctx {c} retired after its halt"

    async def idle(self, cycles: int):
        for _ in range(cycles):
            await FallingEdge(self.dut.clk)
            self._step_seams()
            self._sample(self.cycle, None)
            self.cycle += 1

    async def restart(self):
        """Global reset with every context held, seams cleared."""
        await self.assert_reset()
        self.reset_seams()
        for v in (self.wr_valid, self.rd_valid, self.f_ready):
            for c in range(self.num_harts):
                v.set(c, 0)
            v.flush()
        self.clear_traces()
        await self.release_reset()
        await RisingEdge(self.dut.clk)
