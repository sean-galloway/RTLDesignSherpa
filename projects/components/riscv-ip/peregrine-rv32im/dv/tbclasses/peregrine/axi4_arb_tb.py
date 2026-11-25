# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi4_arb_tb
# Purpose: Unit TB for peregrine_axi4_arb (PRD P7, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_axi4_arb unit TB.

Three house AXI4 masters (read + write each) on the harness's s0/s1/s2
ports, one house AXI4 slave (read + write) on the fabric port over a shared
MemoryModel.  Each master owns its own address region, so its writes and
reads need no cross-master ordering; each keeps a byte model of its region
and checks every read burst against it.  All three run concurrently, so
reads of different masters are in flight together and their R beats must
route by id; writes interleave at the AW grant and W must follow AW.

Fabric-side checks (monitor, every cycle mid-cycle):
  * the fabric id's master field names a master that has an AR (AW)
    outstanding, and R (B) goes back to that master only;
  * W beats on the fabric belong to the master whose AW was granted last,
    and the beat count matches its AWLEN + 1.
"""

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_rd, create_axi4_master_wr,
    create_axi4_slave_rd, create_axi4_slave_wr)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel

MASTER_OPT = ("lock", "cache", "prot", "qos", "region", "user")
SLAVE_OPT = ("user",)
NM = 3
REGION = 0x4000


class Axi4ArbTB:
    def __init__(self, dut, axi_dw=64, axi_iw=4, seed=1) -> None:
        self.dut = dut
        self.log = dut._log
        self.dw = axi_dw
        self.bb = axi_dw // 8
        self.iw = axi_iw
        self.rng = random.Random(seed)
        self.mem = MemoryModel(num_lines=(NM * REGION) // self.bb,
                               bytes_per_line=self.bb, log=self.log)
        self.model = [bytearray(REGION) for _ in range(NM)]
        for m in range(NM):
            self.mem.write(m * REGION, bytearray(REGION))
        kw = dict(id_width=axi_iw, addr_width=32, data_width=axi_dw, user_width=1)
        self.rd, self.wr = [], []
        for m in range(NM):
            self.rd.append(create_axi4_master_rd(dut=dut, clock=dut.clk, prefix=f"s{m}_axi_",
                                                 log=self.log, ifc_name=f"m{m}rd",
                                                 optional_fields=MASTER_OPT, **kw)["interface"])
            self.wr.append(create_axi4_master_wr(dut=dut, clock=dut.clk, prefix=f"s{m}_axi_",
                                                 log=self.log, ifc_name=f"m{m}wr",
                                                 optional_fields=MASTER_OPT, **kw)["interface"])
        skw = dict(id_width=axi_iw + 2, addr_width=32, data_width=axi_dw, user_width=1)
        self.srd = create_axi4_slave_rd(dut=dut, clock=dut.clk, prefix="m_axi_", log=self.log,
                                        memory_model=self.mem, optional_fields=SLAVE_OPT,
                                        **skw)
        self.swr = create_axi4_slave_wr(dut=dut, clock=dut.clk, prefix="m_axi_", log=self.log,
                                        memory_model=self.mem, optional_fields=SLAVE_OPT,
                                        **skw)
        self.ar_out = [0] * NM
        self.aw_out = [0] * NM
        self.w_owner = []        # [master, beats left] per accepted AW, in order
        self.counts = {"ar": [0] * NM, "aw": [0] * NM, "r": [0] * NM, "b": [0] * NM}

    def set_slow(self) -> None:
        self.srd["AR"].set_randomizer(FlexRandomizer({"ready_delay": ([(0, 2), (3, 6)], [0.7, 0.3])}))
        self.srd["R"].set_randomizer(FlexRandomizer({"valid_delay": ([(0, 2), (3, 6)], [0.6, 0.4])}))
        self.swr["AW"].set_randomizer(FlexRandomizer({"ready_delay": ([(0, 2), (3, 6)], [0.7, 0.3])}))
        self.swr["W"].set_randomizer(FlexRandomizer({"ready_delay": ([(0, 1), (2, 4)], [0.7, 0.3])}))

    async def setup_clocks_and_reset(self) -> None:
        cocotb.start_soon(Clock(self.dut.clk, 10, unit="ns").start())
        await self.assert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.clk)
        await self.deassert_reset()
        cocotb.start_soon(self._monitor())

    async def assert_reset(self) -> None:
        self.dut.rst_n.value = 0

    async def deassert_reset(self) -> None:
        self.dut.rst_n.value = 1
        for _ in range(4):
            await RisingEdge(self.dut.clk)

    async def _monitor(self) -> None:
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            await Timer(2, unit="ps")
            await ReadOnly()
            mi_shift = self.iw
            if int(d.m_axi_arvalid.value) and int(d.m_axi_arready.value):
                m = int(d.m_axi_arid.value) >> mi_shift
                assert m < NM, f"AR with master field {m}"
                self.ar_out[m] += 1
                self.counts["ar"][m] += 1
            if int(d.m_axi_rvalid.value) and int(d.m_axi_rready.value):
                m = int(d.m_axi_rid.value) >> mi_shift
                assert self.ar_out[m] > 0, f"R for master {m} with no AR outstanding"
                for j in range(NM):
                    v = int(getattr(d, f"s{j}_axi_rvalid").value)
                    assert v == int(j == m), \
                        f"R beat for master {m}: master {j} rvalid={v} (expected {int(j == m)})"
                if int(d.m_axi_rlast.value):
                    self.ar_out[m] -= 1
                    self.counts["r"][m] += 1
            if int(d.m_axi_awvalid.value) and int(d.m_axi_awready.value):
                m = int(d.m_axi_awid.value) >> mi_shift
                assert m < NM, f"AW with master field {m}"
                self.aw_out[m] += 1
                self.counts["aw"][m] += 1
                self.w_owner.append([m, int(d.m_axi_awlen.value) + 1])
            if int(d.m_axi_wvalid.value) and int(d.m_axi_wready.value):
                assert self.w_owner, "W beat on the fabric before its AW"
                m, left = self.w_owner[0]
                assert int(getattr(d, f"s{m}_axi_wready").value), \
                    f"fabric W beat not from master {m}, the AW owner"
                last = int(d.m_axi_wlast.value)
                assert last == int(left == 1), f"master {m}: wlast on beat with {left} left"
                self.w_owner[0][1] -= 1
                if left == 1:
                    self.w_owner.pop(0)
            if int(d.m_axi_bvalid.value) and int(d.m_axi_bready.value):
                m = int(d.m_axi_bid.value) >> mi_shift
                assert self.aw_out[m] > 0, f"B for master {m} with no AW outstanding"
                for j in range(NM):
                    v = int(getattr(d, f"s{j}_axi_bvalid").value)
                    assert v == int(j == m), \
                        f"B for master {m}: master {j} bvalid={v} (expected {int(j == m)})"
                self.aw_out[m] -= 1
                self.counts["b"][m] += 1

    async def master_traffic(self, m: int, ops: int) -> int:
        """Random bursts within master m's region; every read checked."""
        rng = random.Random(self.rng.getrandbits(32) ^ m)
        base = m * REGION
        checked = 0
        for _ in range(ops):
            beats = rng.randint(1, 8)
            off = rng.randrange(0, REGION - beats * self.bb, self.bb)
            tid = rng.randrange(1 << self.iw)
            if rng.random() < 0.5:
                data = [rng.getrandbits(self.dw) for _ in range(beats)]
                await self.wr[m].write_transaction(base + off, data, burst_len=beats, id=tid)
                for i, w in enumerate(data):
                    self.model[m][off + i * self.bb: off + (i + 1) * self.bb] = \
                        w.to_bytes(self.bb, "little")
            else:
                got = await self.rd[m].read_transaction(base + off, burst_len=beats, id=tid)
                for i, w in enumerate(got):
                    want = int.from_bytes(self.model[m][off + i * self.bb:
                                                        off + (i + 1) * self.bb], "little")
                    assert w == want, (f"master {m} read 0x{base + off + i * self.bb:x}: "
                                       f"0x{w:x}, model 0x{want:x}")
                    checked += 1
        return checked
