# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: icache_tb
# Purpose: Unit TB for peregrine_icache (PRD P9, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_icache unit TB.

The fetch side is driven exactly as peregrine_core and peregrine_top drive
it: a registered PC (fetch_addr), the next PC as if the core were not held
(fetch_addr_next_nw), and the hold (the core's mem_wait): the cache's own
stall, ORed with random holds from elsewhere (the D side) when a phase asks
for them.  The PC advances only on a cycle without a hold.  The refill master is answered by the house
AXI4 slave-read BFM over a MemoryModel, so every refill reads the model.

Checks, every cycle:
  * when stall is low, fetch_rdata equals the model's word at the PC;
  * the AR is one whole-line INCR burst from the line's first byte;
  * inv_ack is never raised while a refill is in flight.
Counts (asserted by the directed phases): AR bursts per phase, so a hit
that should not miss, or a miss that should not hit, is a failure.
"""

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel

OPTIONAL = ("lock", "cache", "prot", "qos", "region", "user")


class IcacheTB:
    PROFILES = {
        "fast":   {"ready": ([(0, 0)], [1.0]), "resp": ([(0, 0)], [1.0])},
        "normal": {"ready": ([(0, 2), (3, 5)], [0.7, 0.3]),
                   "resp":  ([(0, 2), (3, 6)], [0.6, 0.4])},
    }

    def __init__(self, dut, size_bytes=4096, line_bytes=64, axi_dw=64,
                 mem_bytes=1 << 16, seed=1) -> None:
        self.dut = dut
        self.log = dut._log
        self.size = size_bytes
        self.line = line_bytes
        self.dw = axi_dw
        self.mem_bytes = mem_bytes
        self.rng = random.Random(seed)
        self.mem = MemoryModel(num_lines=mem_bytes // (axi_dw // 8),
                               bytes_per_line=axi_dw // 8, log=self.log)
        for a in range(0, mem_bytes, 4):
            self.mem.write(a, bytearray(self.rng.getrandbits(32).to_bytes(4, "little")))
        rd = create_axi4_slave_rd(dut=dut, clock=dut.clk, prefix="m_axi_", log=self.log,
                                  id_width=4, addr_width=32, data_width=axi_dw,
                                  user_width=1, memory_model=self.mem,
                                  optional_fields=OPTIONAL)
        self.ar = rd["AR"]
        self.r = rd["R"]
        self.pc = 0
        self.ars = 0
        self.checked = 0
        self.inv_acks = 0

    def word(self, addr: int) -> int:
        return int.from_bytes(self.mem.read(addr % self.mem_bytes, 4), "little")

    def set_profile(self, name: str) -> None:
        cfg = self.PROFILES[name]
        self.ar.set_randomizer(FlexRandomizer({"ready_delay": cfg["ready"]}))
        self.r.set_randomizer(FlexRandomizer({"valid_delay": cfg["resp"]}))

    async def setup_clocks_and_reset(self) -> None:
        cocotb.start_soon(Clock(self.dut.clk, 10, unit="ns").start())
        self.dut.fetch_addr.value = 0
        self.dut.fetch_addr_next_nw.value = 0
        self.dut.hold.value = 0
        self.dut.inv_req.value = 0
        await self.assert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.clk)
        await self.deassert_reset()
        cocotb.start_soon(self._monitor())

    async def assert_reset(self) -> None:
        self.dut.rst_n.value = 0

    async def deassert_reset(self) -> None:
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)

    async def _monitor(self) -> None:
        d = self.dut
        beats = self.line // (self.dw // 8)
        while True:
            # Mid-cycle (after the falling-edge drives): the values the next
            # rising edge acts on.  Sampling after the rising edge misses
            # every handshake (the valid has already dropped).
            await FallingEdge(d.clk)
            await Timer(2, unit="ps")
            await ReadOnly()
            busy = int(d.m_axi_rready.value) or int(d.m_axi_arvalid.value)
            if int(d.inv_ack.value):
                assert not busy, "inv_ack raised during a refill"
            if int(d.m_axi_arvalid.value) and int(d.m_axi_arready.value):
                self.ars += 1
                addr = int(d.m_axi_araddr.value)
                assert addr % self.line == 0, f"AR 0x{addr:x} not line-aligned"
                assert int(d.m_axi_arlen.value) == beats - 1, "AR is not one whole line"
                assert int(d.m_axi_arburst.value) == 1, "AR is not INCR"

    async def fetch(self, stream, inv_at=(), inv_when_busy=False,
                    hold_pct=0, max_cycles=400_000) -> None:
        """Fetch every address of ``stream`` in order, as the core would:
        the PC advances only on a cycle without a hold.  The hold is the
        cache's stall, or (``hold_pct`` percent of cycles) a hold from
        elsewhere, which the cache must ride out with its output kept.

        inv_req is held from fetch index k (k in ``inv_at``) until acked;
        with ``inv_when_busy`` it is raised only once a refill is in flight
        at that index, so the invalidate lands mid-refill."""
        d = self.dut
        it = iter(stream)
        nxt = next(it, None)
        inv_set = set(inv_at)
        k = 0
        seen_busy = False
        for _ in range(max_cycles):
            await FallingEdge(d.clk)
            d.fetch_addr.value = self.pc
            d.fetch_addr_next_nw.value = self.pc if nxt is None else nxt
            busy = int(d.m_axi_arvalid.value) or int(d.m_axi_rready.value)
            seen_busy = seen_busy or bool(busy)
            d.inv_req.value = int(k in inv_set and (seen_busy or not inv_when_busy))
            await Timer(1, unit="ps")
            stall = int(d.stall.value)
            if not stall:
                got = int(d.fetch_rdata.value)
                want = self.word(self.pc)
                assert got == want, (f"pc 0x{self.pc:x}: fetched 0x{got:08x}, "
                                     f"memory 0x{want:08x}")
                self.checked += 1
            if int(d.inv_ack.value):
                self.inv_acks += 1
                inv_set.discard(k)
            hold = stall or (hold_pct and self.rng.randrange(100) < hold_pct)
            d.hold.value = int(bool(hold))
            if not hold:
                if nxt is None:
                    d.inv_req.value = 0
                    return
                self.pc = nxt
                nxt = next(it, None)
                k += 1
                seen_busy = False
        raise AssertionError("fetch did not finish")
