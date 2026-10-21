# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""fb_data_fabric testbench: one TB for every leg of the data fabric under test.

The DUT is whichever `fb_data_fabric` the leg's filelist compiled (bridge or
Xilinx AXI Crossbar); this TB cannot tell them apart and must not. Every port
of PRD.md section 4 is driven by the framework BFMs: AXI4 masters on M0..M3,
AXI4 slaves over MemoryModels at the Table 5.1 windows on S0..S3.

What a pass means, for either leg:
  - every read returns its endpoint's bytes, every write lands where it was aimed,
    with all four masters running at once (contention through the arbiters)
  - responses come back on the issuing ID
  - at each slave, the ID is {master slot, master-local ID}, zero-extended to
    the slave-side width, and the slot is a master connected to that slave.
    The local part is the leg's: leg B1 keeps the master's own ID (and the TB
    checks it is one that master has in flight); leg A's bridge remaps an ID
    wider than a slot to a remap slot (bridge TASK-018), so its local part is
    $clog2(max_outstanding) bits. The width comes from the pytest wrapper
    (FB_LOCAL_ID_W). Nothing downstream keys on it: the endpoints take the
    channel from the address (fb_endpoints CH_SEL_ADDR=1).
  - a master reaching a slave it is not connected to gets DECERR, as does an
    unmapped address
"""
from __future__ import annotations

import os
import random
from dataclasses import dataclass

import cocotb
from cocotb.triggers import FallingEdge

from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_rd, create_axi4_master_wr, create_axi4_slave_rd, create_axi4_slave_wr)
from CocoTBFramework.components.shared.memory_model import MemoryModel
from TBClasses.shared.tbbase import TBBase

DW = 128
BYTES = DW // 8
MID = 8                      # master ID width
SID = 10                     # slave-side ID width: {slot, local id}, zero-extended
SLOT_W = 2                   # master-slot bits: four masters
MEM_BYTES = 0x10000          # modelled span of each endpoint (low end of its window)
RESP_DECERR = 3


@dataclass(frozen=True)
class Window:
    name: str
    base: int
    rd: bool
    wr: bool


# Table 5.1 / PRD section 4, slave order = TOML order.
SLAVES = (Window("ddr", 0x0000_0000, True, True),
          Window("desc_ram", 0x8000_0000, True, False),
          Window("lfsr_src", 0x9000_0000, True, False),
          Window("crc_snk", 0xA000_0000, False, True))
# master name -> (slot, rd, wr); slot = TOML order
MASTERS = {"stream_desc": (0, True, False), "stream_rd": (1, True, False),
           "stream_wr": (2, False, True), "inj_wr": (3, False, True)}

# Regions so concurrent writers never overlap and readers read preloaded bytes.
DDR_RD = 0x0000_0000         # preloaded, read by stream_rd
DDR_WR_STREAM = 0x0000_4000  # written by stream_wr
DDR_WR_INJ = 0x0000_8000     # written by inj_wr


class FbFabricTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.leg = os.environ.get('FB_LEG', 'unknown')
        # master-local ID bits at the slaves; MID means the leg keeps the ID
        self.local_w = int(os.environ.get('FB_LOCAL_ID_W', str(MID)))
        self.rng = random.Random(int(os.environ.get('SEED', '0')))
        self.errors: list[str] = []
        self.stats = {'rd': 0, 'wr': 0, 'rd_beats': 0, 'wr_beats': 0, 'decerr': 0, 'ids': 0}
        clk = dut.aclk
        self.mem = {}
        self.slv = {}
        for w in SLAVES:
            mm = MemoryModel(num_lines=MEM_BYTES // BYTES, bytes_per_line=BYTES, log=self.log)
            self.mem[w.name] = mm
            kw = dict(dut=dut, clock=clk, prefix=w.name, log=self.log, id_width=SID,
                      addr_width=32, data_width=DW, user_width=1, memory_model=mm,
                      base_addr=w.base)
            if w.rd:
                self.slv[w.name + '_rd'] = create_axi4_slave_rd(**kw)
            if w.wr:
                self.slv[w.name + '_wr'] = create_axi4_slave_wr(**kw)
        self.mst = {}
        for name, (_, rd, wr) in MASTERS.items():
            kw = dict(dut=dut, clock=clk, prefix=name, log=self.log, id_width=MID,
                      addr_width=32, data_width=DW, user_width=1)
            self.mst[name] = (create_axi4_master_rd(**kw) if rd else create_axi4_master_wr(**kw))['interface']
        # golden bytes per endpoint: what every read must return / every write must leave
        self.golden: dict[str, dict[int, int]] = {w.name: {} for w in SLAVES}
        # IDs each master has in flight: the slave-side check needs them
        self.inflight: dict[str, list[int]] = {m: [] for m in MASTERS}

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._watch_slave_ids())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- stimulus -----------------------------------------------------------
    def preload(self):
        """Fill every readable endpoint with seeded bytes and record them."""
        for w in SLAVES:
            if not w.rd:
                continue
            data = bytearray(self.rng.getrandbits(8) for _ in range(MEM_BYTES))
            self.mem[w.name].write(0, data)
            self.golden[w.name] = dict(enumerate(data))

    def _word(self, ep: str, off: int) -> int:
        return sum(self.golden[ep].get(off + i, 0) << (8 * i) for i in range(BYTES))

    async def _reader(self, master: str, plan: list[tuple[str, int, int]]):
        bfm = self.mst[master]
        for n, (ep, off, beats) in enumerate(plan):
            base = next(w.base for w in SLAVES if w.name == ep)
            txn_id = self.rng.randrange(1 << MID)
            self.inflight[master].append(txn_id)
            data = await bfm.read_transaction(base + off, burst_len=beats, id=txn_id)
            self.inflight[master].remove(txn_id)
            self.stats['rd'] += 1
            self.stats['rd_beats'] += beats
            for i, got in enumerate(data):
                want = self._word(ep, off + i * BYTES)
                if got != want:
                    self.errors.append(f"{master} rd {ep}+0x{off + i * BYTES:X}: "
                                       f"0x{got:032X} want 0x{want:032X}")
                    return

    async def _writer(self, master: str, plan: list[tuple[str, int, int]]):
        bfm = self.mst[master]
        for ep, off, beats in plan:
            base = next(w.base for w in SLAVES if w.name == ep)
            words = [self.rng.getrandbits(DW) for _ in range(beats)]
            txn_id = self.rng.randrange(1 << MID)
            self.inflight[master].append(txn_id)
            res = await bfm.write_transaction(base + off, words, burst_len=beats, id=txn_id)
            self.inflight[master].remove(txn_id)
            self.stats['wr'] += 1
            self.stats['wr_beats'] += beats
            if res.get('response') != 0:
                self.errors.append(f"{master} wr {ep}+0x{off:X}: resp {res.get('response')} "
                                   f"({res.get('error')})")
                return
            if res.get('id') != txn_id:
                self.errors.append(f"{master} wr {ep}+0x{off:X}: BID {res.get('id')} want {txn_id}")
            for i, word in enumerate(words):
                for b in range(BYTES):
                    self.golden[ep][off + i * BYTES + b] = (word >> (8 * b)) & 0xFF

    def _plan(self, n: int, targets: list[tuple[str, int]], span: int) -> list[tuple[str, int, int]]:
        plan = []
        for k in range(n):
            ep, region = targets[k % len(targets)]
            beats = self.rng.choice((1, 2, 4, 8, 16))
            off = region + self.rng.randrange(0, (span - beats * BYTES) // BYTES) * BYTES
            plan.append((ep, off, beats))
        return plan

    async def run_traffic(self, n: int) -> bool:
        """All four masters at once, each to every slave it is connected to."""
        span = 0x4000
        jobs = [
            # 32-byte descriptors fetched as 2 x 128-bit beats, as the 256->128
            # converter in front of M0 issues them
            cocotb.start_soon(self._reader('stream_desc', [('desc_ram', self.rng.randrange(MEM_BYTES // 32) * 32, 2)
                                                           for _ in range(n)])),
            cocotb.start_soon(self._reader('stream_rd', self._plan(n, [('ddr', DDR_RD), ('lfsr_src', 0)], span))),
            cocotb.start_soon(self._writer('stream_wr', self._plan(n, [('ddr', DDR_WR_STREAM), ('crc_snk', 0)], span))),
            cocotb.start_soon(self._writer('inj_wr', self._plan(n, [('ddr', DDR_WR_INJ)], span))),
        ]
        for j in jobs:
            await j
        return not self.errors

    def check_memory(self) -> bool:
        """Every written byte is in its endpoint's memory, nothing else moved."""
        for w in SLAVES:
            if not w.wr:
                continue
            got = self.mem[w.name].read(0, MEM_BYTES)
            for off, want in self.golden[w.name].items():
                if got[off] != want:
                    self.errors.append(f"{w.name}+0x{off:X}: byte 0x{got[off]:02X} want 0x{want:02X}")
                    return False
        return True

    async def run_decerr(self) -> bool:
        """Unconnected and unmapped targets must answer DECERR, never hang or hit a slave."""
        cases = [('stream_desc', 0x0000_1000, 'rd', 'unconnected (desc -> ddr)'),
                 ('stream_rd', 0xC000_0000, 'rd', 'unmapped'),
                 ('inj_wr', 0xA000_0000, 'wr', 'unconnected (injector -> crc sink)'),
                 ('stream_wr', 0x9000_0000, 'wr', 'unconnected (write -> lfsr source)')]
        for master, addr, kind, why in cases:
            bfm = self.mst[master]
            if kind == 'rd':
                try:
                    await bfm.read_transaction(addr, burst_len=2, id=0x5A)
                    self.errors.append(f"{master} rd 0x{addr:08X} ({why}): answered OKAY")
                except RuntimeError as e:
                    if 'DECERR' not in str(e):
                        self.errors.append(f"{master} rd 0x{addr:08X} ({why}): {e}")
                    else:
                        self.stats['decerr'] += 1
            else:
                res = await bfm.write_transaction(addr, [0, 0], burst_len=2, id=0x5A)
                if res.get('response') != RESP_DECERR:
                    self.errors.append(f"{master} wr 0x{addr:08X} ({why}): resp {res.get('response')}")
                else:
                    self.stats['decerr'] += 1
        return not self.errors

    async def _watch_slave_ids(self):
        """At every slave address handshake the ID must be {slot, local id},
        zero-extended to SID.

        The slot names a master connected to this slave in this direction.
        Where the leg keeps the master's ID (local_w == MID) the local part
        must be an ID that master has in flight right now; where it remaps
        (leg A), it is a remap slot and only its width is checked.
        """
        d = self.dut
        by_slot = {slot: m for m, (slot, _, _) in MASTERS.items()}
        legal = {}
        for w in SLAVES:
            for kind, ok in (('ar', w.rd), ('aw', w.wr)):
                if ok:
                    legal[(w.name, kind)] = {slot for m, (slot, rd, wr) in MASTERS.items()
                                             if (rd if kind == 'ar' else wr)}
        # Sampled mid-cycle: the BFMs and the RTL both move on the rising edge,
        # so at the falling edge valid & ready are exactly the handshake the
        # next rising edge will take.
        while True:
            await FallingEdge(d.aclk)
            for (ep, kind), slots in legal.items():
                if not (int(getattr(d, f'{ep}_{kind}valid').value)
                        and int(getattr(d, f'{ep}_{kind}ready').value)):
                    continue
                sid = int(getattr(d, f'{ep}_{kind}id').value)
                slot, low = sid >> self.local_w, sid & ((1 << self.local_w) - 1)
                self.stats['ids'] += 1
                if slot >> SLOT_W:
                    self.errors.append(f"{ep} {kind}id 0x{sid:03X}: bits above the "
                                       f"{self.local_w + SLOT_W}-bit fabric ID are not 0")
                elif slot not in slots:
                    self.errors.append(f"{ep} {kind}id 0x{sid:03X}: slot {slot} is not a "
                                       f"connected master ({sorted(slots)})")
                elif self.local_w == MID and low not in self.inflight[by_slot[slot]]:
                    self.errors.append(f"{ep} {kind}id 0x{sid:03X}: low bits 0x{low:02X} are not "
                                       f"an ID {by_slot[slot]} has in flight")

    def report(self) -> bool:
        self.log.info(f"[{self.leg}] {self.stats}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
