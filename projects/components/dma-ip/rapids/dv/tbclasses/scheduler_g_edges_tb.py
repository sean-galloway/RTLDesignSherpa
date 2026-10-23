# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: scheduler_g_edges_tb
# Purpose: scheduler_g's command port on its own (rapids TASK-034): the
#          testbench is the firmware. Every command is tried in every state;
#          the legal edges must be taken and every other command ignored and
#          counted.
#
# Author: sean galloway
# Created: 2026-10-21

"""Edge-table testbench for scheduler_g.

The firmware never sends an illegal edge on purpose, so the equivalence bench
cannot tell whether the table rejects one. Here cocotb drives the sequencer
window directly (seq_wr_*, seq_rd_*), the descriptor input and nothing else:
the engines stay idle, and descriptors are zero-length, so XFER_DATA completes
as soon as it is entered.
"""

import os

import cocotb
from cocotb.triggers import FallingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase

ST = {'IDLE': 0x01, 'FETCH': 0x02, 'XFER': 0x04, 'COMPLETE': 0x08, 'NEXT': 0x10, 'ERROR': 0x20}
FLAG = {'STAGE': 0x400, 'ARM': 0x800, 'ARM_NEXT': 0x1000, 'GEN_OK': 0x2000, 'DECLINE': 0x4000,
        'STAGE_ARM': 0x8000, 'STAGE_ARM_NEXT': 0x10000}
W_CMD, R_STATUS, R_FIFO, R_HEAD_SUM = 0, 0, 13, 21
W_FW_ERROR, W_PKT_LO, W_FW_DEBUG = 1, 7, 8


class SchedulerGEdgesTB(TBBase):
    """scheduler_g, with the testbench as its firmware."""

    INPUTS_ZERO = ('cfg_channel_reset', 'cfg_sched_timeout_enable', 'descriptor_valid',
                   'descriptor_packet', 'descriptor_ext_packet', 'descriptor_error',
                   'sched_rd_done_strobe', 'sched_rd_beats_done', 'sched_wr_done_strobe',
                   'sched_wr_beats_done', 'sched_wr_commit_strobe', 'sched_wr_commit_beats',
                   'sched_rd_error', 'sched_wr_error', 'ctrlrd_error', 'ctrlwr_error',
                   'seq_wr_en', 'seq_wr_addr', 'seq_wr_data', 'seq_rd_addr', 'seq_fault',
                   'i_mon_time', 'cfg_sched_timeout_cycles', 'cfg_sched_timeout_limit')
    INPUTS_ONE = ('cfg_channel_enable', 'sched_rd_pkt_ready', 'sched_wr_pkt_ready', 'sched_wr_ready',
                  'ctrlrd_ready', 'ctrlrd_idle', 'ctrlwr_ready', 'ctrlwr_idle', 'mon_ready',
                  'tile_adv_done')

    def __init__(self, dut):
        super().__init__(dut)
        self.expected_errs = 0
        self.mon = []                           # raw MonBus packets the port sent

    async def _mon_capture(self):
        # sampled mid-cycle: what the next rising edge consumes (a firmware
        # packet's valid is combinational and drops on the edge it goes)
        while True:
            await FallingEdge(self.dut.clk)
            await ReadOnly()
            if int(self.dut.mon_valid.value) and int(self.dut.mon_ready.value):
                self.mon.append(int(self.dut.mon_packet.value))

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        for n in self.INPUTS_ZERO:
            getattr(self.dut, n).value = 0
        for n in self.INPUTS_ONE:
            getattr(self.dut, n).value = 1
        self.dut.tile_dest_legal.value = (1 << len(self.dut.tile_dest_legal)) - 1
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)
        cocotb.start_soon(self._mon_capture())

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # -- the firmware's side of the window -----------------------------------
    async def write(self, addr: int, data: int):
        await FallingEdge(self.dut.clk)
        self.dut.seq_wr_en.value = 1
        self.dut.seq_wr_addr.value = addr
        self.dut.seq_wr_data.value = data
        await FallingEdge(self.dut.clk)
        self.dut.seq_wr_en.value = 0

    async def read(self, addr: int) -> int:
        await FallingEdge(self.dut.clk)
        self.dut.seq_rd_addr.value = addr
        await ReadOnly()
        return int(self.dut.seq_rd_data.value)

    async def state(self) -> int:
        return (await self.read(R_STATUS)) & 0x7F

    async def errs(self) -> int:
        return ((await self.read(R_FIFO)) >> 8) & 0xFF

    async def head_sum(self) -> int:
        return (await self.read(R_HEAD_SUM)) & 0xF

    async def fw_pending(self) -> int:
        return ((await self.read(R_FIFO)) >> 16) & 1

    async def give_descriptor(self, valid: bool = True, last: bool = True, next_ptr: int = 0):
        """A zero-length descriptor into the skid (it completes on entry to XFER)."""
        await FallingEdge(self.dut.clk)
        pkt = (0x1000) | (0x2000 << 64) | (next_ptr << 160) | (int(valid) << 192) | (int(last) << 194)
        self.dut.descriptor_packet.value = pkt
        self.dut.descriptor_valid.value = 1
        for _ in range(20):
            await ReadOnly()
            took = int(self.dut.descriptor_ready.value)
            await FallingEdge(self.dut.clk)
            if took:
                break
        self.dut.descriptor_valid.value = 0

    async def channel_reset(self):
        """Pulse the channel reset (out of ReadOnly first) and re-arm the count."""
        await FallingEdge(self.dut.clk)
        self.dut.cfg_channel_reset.value = 1
        await self.wait_clocks('clk', 3)
        self.dut.cfg_channel_reset.value = 0
        await self.wait_clocks('clk', 3)
        self.expected_errs = 0

    async def flag(self, names, legal: bool, expect: str) -> bool:
        """Send CMD flag bits (no state); check the state and the count."""
        data = 0
        for n in names.split('|'):
            data |= FLAG[n]
        await self.write(W_CMD, data)
        for _ in range(8):                      # room for an automatic sequence
            await self.wait_clocks('clk', 1)
        st, n = await self.state(), await self.errs()
        if not legal:
            self.expected_errs += 1
        ok = (st == ST[expect]) and (n == self.expected_errs)
        level = self.log.info if ok else self.log.error
        level(f"  {'legal  ' if legal else 'illegal'} flag {names:<12}: state 0x{st:02x} "
              f"(want {expect}), CMD_ERR {n} (want {self.expected_errs}) {'ok' if ok else 'FAIL'}")
        return ok

    async def command(self, name: str, legal: bool, expect: str) -> bool:
        """Send the command for state `name`; check the state and the count."""
        await self.write(W_CMD, ST[name])
        for _ in range(4):                      # a pending start, or a no-op
            await self.wait_clocks('clk', 1)
        st, n = await self.state(), await self.errs()
        if not legal:
            self.expected_errs += 1
        ok = (st == ST[expect]) and (n == self.expected_errs)
        level = self.log.info if ok else self.log.error
        level(f"  {'legal  ' if legal else 'illegal'} -> {name:<8}: state 0x{st:02x} "
              f"(want {expect}), CMD_ERR {n} (want {self.expected_errs}) {'ok' if ok else 'FAIL'}")
        return ok
