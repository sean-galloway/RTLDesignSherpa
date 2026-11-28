# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: amber_buserr_tb
# Purpose: TB class for amber's bus-error reporting (cache-ip/amber-mesi-l1
#          TASK-008): amber_top at BUS_ERR_EN=1 on the house AXI4 slave BFMs
#          with error windows, CPU port on the house GAXI BFMs.
#
# Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/01_l1_control.md
# Subsystem: amber
#
# Author: sean galloway
# Created: 2026-11-27

"""amber_top bus-error TB (TASK-008).

Memory side: the house AXI4 slave-read / slave-write BFMs over one
MemoryModel.  Error windows by address bits 19:16:

  0xE  every R beat DECERR, and writes SLVERR
  0xD  every R beat SLVERR, and writes SLVERR
  0xC  reads OKAY, writes SLVERR (a dirty line there fails its write-back)

Reads take the BFM's ``resp_override``; writes go through a thin proxy of
the MemoryModel whose ``in_range`` is False in the write-error windows (the
BFM's out-of-range contract answers SLVERR and writes nothing), so the
memory a failed write-back targeted keeps its old data.  ``extra_bad``
lines fail reads too, on demand (the upgrade case: a line filled OKAY, then
its CleanUnique fails).

CPU side: one request at a time; ``access`` returns (rdata, err) from the
response, err being cpu_rsp_rd_data[BUS_WIDTH].

Scoreboard: ``shadow`` holds the value every 64-bit word must read: the
memory's, updated by every write the cache answered OKAY.  When a dirty
line is dropped (its write-back failed) its words revert to the memory's.
Every OKAY read is checked against it.  The AR / AW handshakes are counted
so a phase can assert that a line was (or was not) installed.
"""

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_factories import (create_axi4_slave_rd,
                                                            create_axi4_slave_wr)
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel

OPTIONAL = ("lock", "cache", "prot", "qos", "region", "user")
MEM_BYTES = 1 << 20
RD_DECERR, RD_SLVERR, WR_ONLY = 0xE, 0xD, 0xC


def window(addr: int) -> int:
    return (addr >> 16) & 0xF


class _WriteMemory:
    """The MemoryModel as the write BFM sees it: out of range (SLVERR,
    nothing written) in the write-error windows."""

    def __init__(self, mem: MemoryModel) -> None:
        self._mem = mem

    def in_range(self, offset: int, span: int) -> bool:
        if window(offset) in (RD_DECERR, RD_SLVERR, WR_ONLY):
            return False
        return self._mem.in_range(offset, span)

    def __getattr__(self, name):
        return getattr(self._mem, name)


class AmberBusErrTB:
    PROFILES = {
        "fast":   {"ready": ([(0, 0)], [1.0]), "resp": ([(0, 0)], [1.0])},
        "normal": {"ready": ([(0, 2), (3, 5)], [0.7, 0.3]),
                   "resp":  ([(0, 2), (3, 6)], [0.6, 0.4])},
    }

    def __init__(self, dut, sets: int, ways: int, line: int, bus: int, seed: int) -> None:
        self.dut = dut
        self.log = dut._log
        self.sets, self.ways, self.line, self.bus = sets, ways, line, bus
        self.strb = bus // 8
        self.rng = random.Random(seed)
        self.mem = MemoryModel(num_lines=MEM_BYTES // self.strb,
                               bytes_per_line=self.strb, log=self.log)
        for a in range(0, MEM_BYTES, 8):
            self.mem.write(a, bytearray(self.rng.getrandbits(64).to_bytes(8, "little")))
        self.shadow: dict = {}
        self.extra_bad: set = set()
        self.ars = 0
        self.aws = 0
        self.checks = 0
        self._rsp = []

    # -- address helpers ------------------------------------------------
    def addr(self, win: int, set_idx: int, tag: int = 0, off: int = 0) -> int:
        """An address in window ``win`` (bits 19:16), set ``set_idx``."""
        set_bits = (self.sets - 1).bit_length()
        off_bits = (self.line - 1).bit_length()
        low = (tag << (off_bits + set_bits)) | (set_idx << off_bits) | off
        assert low < (1 << 16), "tag out of the 64 KiB window"
        return (win << 16) | low

    def mem_word(self, a: int) -> int:
        return int.from_bytes(self.mem.read(a - a % 8, 8), "little")

    def want(self, a: int) -> int:
        w = a - a % 8
        return self.shadow.get(w, self.mem_word(w))

    def drop_line(self, a: int) -> None:
        base = a - a % self.line
        for w in range(base, base + self.line, 8):
            self.shadow.pop(w, None)

    # -- setup ----------------------------------------------------------
    def _resp_override(self, addr: int):
        if (addr - addr % self.line) in self.extra_bad:
            return 2
        win = window(addr)
        if win == RD_DECERR:
            return 3
        if win == RD_SLVERR:
            return 2
        return None

    async def setup(self) -> None:
        d = self.dut
        cocotb.start_soon(Clock(d.aclk, 10, unit="ns").start())
        for name, val in (("cpu_req_wr_valid", 0), ("cpu_req_wr_data", 0),
                          ("cpu_rsp_rd_ready", 1), ("m_axi_ruser", 0),
                          ("m_axi_buser", 0), ("m_axi_acaddr", 0),
                          ("m_axi_acsnoop", 0), ("m_axi_acprot", 0),
                          ("m_axi_acvalid", 0), ("m_axi_crready", 1),
                          ("m_axi_cdready", 1), ("i_mon_time", 0),
                          ("mon_ready", 1), ("wb_err_clear", 0)):
            getattr(d, name).value = val
        d.aresetn.value = 0
        req_w = 1 + 32 + 1 + self.strb + self.bus
        req_fields = FieldConfig.from_dict(
            field_dict={"data": {"bits": req_w, "default": 0}}, lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={"data": {"bits": self.bus + 1, "default": 0}}, lsb_first=True)
        self.master = GAXIMaster(
            dut=d, title="cpu_req", prefix="", clock=d.aclk, field_config=req_fields,
            timeout_cycles=20000, mode="skid", bus_name="cpu_req_wr", pkt_prefix="",
            multi_sig=False, randomizer=FlexRandomizer({"valid_delay": ([(0, 0)], [1])}),
            log=self.log)
        self.slave = GAXISlave(
            dut=d, title="cpu_rsp", prefix="", clock=d.aclk, field_config=rsp_fields,
            timeout_cycles=20000, mode="skid", bus_name="cpu_rsp_rd", pkt_prefix="",
            multi_sig=False, randomizer=FlexRandomizer({"ready_delay": ([(0, 0)], [1])}),
            log=self.log)
        self.slave.set_ready_policy("always")
        self.slave.add_callback(lambda p: self._rsp.append(int(p.fields.get("data", 0))
                                                           if hasattr(p, "fields")
                                                           else int(p.data)))
        rd = create_axi4_slave_rd(dut=d, clock=d.aclk, prefix="m_axi_", log=self.log,
                                  id_width=8, addr_width=32, data_width=self.bus,
                                  user_width=1, memory_model=self.mem,
                                  optional_fields=OPTIONAL,
                                  resp_override=self._resp_override)
        wr = create_axi4_slave_wr(dut=d, clock=d.aclk, prefix="m_axi_", log=self.log,
                                  id_width=8, addr_width=32, data_width=self.bus,
                                  user_width=1, memory_model=_WriteMemory(self.mem),
                                  optional_fields=OPTIONAL)
        self.chans = [rd["AR"], rd["R"], wr["AW"], wr["W"], wr["B"]]
        for _ in range(5):
            await RisingEdge(d.aclk)
        d.aresetn.value = 1
        for _ in range(4):
            await RisingEdge(d.aclk)
        while int(d.init_busy.value):
            await RisingEdge(d.aclk)
        cocotb.start_soon(self._count())

    def set_profile(self, name: str) -> None:
        cfg = self.PROFILES[name]
        ar, r, aw, w, b = self.chans
        for c in (ar, aw, w):
            c.set_randomizer(FlexRandomizer({"ready_delay": cfg["ready"]}))
        for c in (r, b):
            c.set_randomizer(FlexRandomizer({"valid_delay": cfg["resp"]}))

    async def _count(self) -> None:
        d = self.dut
        while True:
            await FallingEdge(d.aclk)
            await Timer(1, unit="ps")
            await ReadOnly()
            self.ars += int(d.m_axi_arvalid.value) & int(d.m_axi_arready.value)
            self.aws += int(d.m_axi_awvalid.value) & int(d.m_axi_awready.value)

    # -- the CPU port ---------------------------------------------------
    async def access(self, a: int, we: int = 0, be: int = 0, wdata: int = 0,
                     maint: int = 0) -> tuple:
        """One request; returns (rdata, err)."""
        beat = a - a % self.strb
        data = ((maint << (32 + 1 + self.strb + self.bus))
                | ((beat & 0xFFFF_FFFF) << (1 + self.strb + self.bus))
                | (we << (self.strb + self.bus)) | (be << self.bus)
                | (wdata & ((1 << self.bus) - 1)))
        n = len(self._rsp)
        pkt = self.master.create_packet(data=data)
        await self.master.send(pkt)
        for _ in range(100000):
            if len(self._rsp) > n:
                break
            await RisingEdge(self.dut.aclk)
        else:
            raise AssertionError(f"no response to 0x{a:x}")
        rsp = self._rsp[n]
        return rsp & ((1 << self.bus) - 1), (rsp >> self.bus) & 1

    async def read(self, a: int, err: int = 0) -> int:
        got, e = await self.access(a)
        assert e == err, f"read 0x{a:x}: err={e}, expected {err}"
        if not e:
            want = self.want(a)
            assert got == want, f"read 0x{a:x}: 0x{got:016x}, expected 0x{want:016x}"
            self.checks += 1
        return got

    async def write(self, a: int, value: int, be: int = 0xFF, err: int = 0) -> None:
        _, e = await self.access(a, we=1, be=be, wdata=value)
        assert e == err, f"write 0x{a:x}: err={e}, expected {err}"
        if not e:
            w = a - a % 8
            old = self.want(w)
            mask = sum(0xFF << (8 * i) for i in range(8) if (be >> i) & 1)
            self.shadow[w] = (old & ~mask) | (value & mask)

    async def clean_all(self) -> None:
        _, e = await self.access(0, maint=1)
        assert e == 0, "clean-all answered with the error bit"

    def wb_err(self) -> tuple:
        d = self.dut
        return (int(d.wb_err_valid.value), int(d.wb_err_addr.value),
                int(d.wb_err_ovf.value))

    async def clear(self) -> None:
        await FallingEdge(self.dut.aclk)
        self.dut.wb_err_clear.value = 1
        await FallingEdge(self.dut.aclk)
        self.dut.wb_err_clear.value = 0
