# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""build-xil: the host side of the AMD/Xilinx masters on bridge_bs_xil.

    h = StressHarness(bridge, build)
    h.vendor = XilVendors(h)          # before h.run(...)

Both masters reach only the memories (mig, bram), and both move the image
the stress masters keep there (bstress MEM_TAG, hashed modulo 2^MEM_LG2), so
everything they write is checked twice: by the stress masters' reads during
the run and by the read sweep after it (StressHarness.sweep).

Traffic generator (axi_traffic_gen, AXI4 Advanced mode, PG125), on ext0:
    N_CMD write and N_CMD read commands per run, by seed: INCR bursts of
    1..16 64-bit beats at random 8-byte-aligned offsets of either memory,
    on IDs 0..3. Write data comes from its master RAM, which the host loads
    with the image of each write's target; reads land in a second region of
    it. It loops the list until the run ends (Master Control LOOP), then the
    host stops it, reads its Error Status (it checks RID / BID against its
    outstanding IDs, BRESP / RRESP and RLAST itself) and compares every read
    byte with the image.
DMA (axi_cdma, simple mode, DRE), on ext1:
    copies between the memories at equal offsets (the two images agree
    there), random length and alignment, one after another while the run is
    live (tick() from StressHarness.wait_done); each must end Idle with no
    DMAIntErr / DMASlvErr / DMADecErr.

PG125 register map used here: 0x00 Master Control ([20] MSTEN, [19] LOOP),
0x08 Error Status (W1C), 0x0C Error Enable, CMDRAM read commands at 0x8000
and write commands at 0x9000 (16 bytes each), master RAM at 0xC000. A
command list ends at the first entry without its valid bit.
"""
from __future__ import annotations

import random
import time
from typing import Callable, Dict, List, Optional, Tuple

from bstress import MEM_LG2, MEM_TAG, StressHarness
from TBClasses.amba import axi_stress_model as M

ATG_BASE = 0x0010_0000
CDMA_BASE = 0x0011_0000

ATG_MCTL, ATG_ERR, ATG_ERR_EN = 0x00, 0x08, 0x0C
ATG_CMD_RD, ATG_CMD_WR, ATG_MSTRAM = 0x8000, 0x9000, 0xC000
ATG_MSTEN, ATG_LOOP = 1 << 20, 1 << 19
ATG_ERRS = {16: 'RLENER', 17: 'RERRSP', 18: 'WRSPER', 19: 'WIDER', 20: 'RIDER',
            0: 'SWLENER', 1: 'SWSTRB'}
ATG_BEAT = 8                       # its master port is 64-bit
N_CMD = 8                          # commands per direction
CMD_BYTES = 16 * ATG_BEAT          # master RAM per command: up to 16 beats
RD_REGION = N_CMD * CMD_BYTES      # read data lands after the write data

CDMA_CR, CDMA_SR, CDMA_SA, CDMA_DA, CDMA_BTT = 0x00, 0x04, 0x18, 0x20, 0x28
CDMA_IDLE = 1 << 1
CDMA_ERRS = {4: 'DMAIntErr', 5: 'DMASlvErr', 6: 'DMADecErr'}
CDMA_MAX = 2048                    # bytes per copy


class XilVendors:
    def __init__(self, h: StressHarness, log: Callable[[str], None] = print):
        self.h, self.bus, self.log = h, h.bridge, log
        # Every memory holds the same image at equal offsets, so the targets
        # and the copies use the span they all share: the smallest one's.
        # One memory (a run with --exclude mig) is fine: copies stay inside it.
        self.mems = list(h.build.memories)
        if not self.mems:
            raise ValueError('build-xil has no memory to aim the vendor masters at')
        self.span = 1 << min(m.mem_lg2 for m in self.mems)
        self.seed = self.hash_seed = 0
        self.rd_cmds: List[Tuple[int, int]] = []
        self.active = False
        self.copies = self.copy_bytes = 0
        self.problems: List[str] = []
        self._copy: Optional[Tuple[int, int, int]] = None

    # ---- helpers -------------------------------------------------------------
    def _w(self, base: int, off: int, v: int) -> None:
        self.bus.write(base + off, v & M.M32)

    def _r(self, base: int, off: int) -> int:
        return self.bus.read(base + off)

    def _image(self, addr: int, n: int) -> bytes:
        return bytes(M.mem_byte(addr + i, self.hash_seed, MEM_TAG, MEM_LG2) for i in range(n))

    @staticmethod
    def _cmd(addr: int, beats: int, cid: int, ram_off: int) -> List[int]:
        """One PG125 command entry, four 32-bit words."""
        w1 = ((beats - 1) & 0xFF) | (1 << 10) | (3 << 12) | ((cid & 0x3F) << 15) | (1 << 31)
        w2 = ram_off & 0x1FFF        # master RAM BYTE address (13 bits = its 8 KB)
        w3 = 0b001                                  # expected response: OKAY
        return [addr & M.M32, w1, w2, w3]

    def _target(self, rng: random.Random) -> Tuple[int, int]:
        """(address, beats): an 8-byte-aligned INCR inside the shared span,
        not crossing 4 KB."""
        mem = rng.choice(self.mems)
        beats = rng.randint(1, CMD_BYTES // ATG_BEAT)
        while True:
            off = rng.randrange(0, self.span - beats * ATG_BEAT, ATG_BEAT)
            if (off & 0xFFF) + beats * ATG_BEAT <= 0x1000:
                return mem.base + off, beats

    # ---- the run -------------------------------------------------------------
    def start(self, prof, seed: int) -> None:
        self.seed = seed
        self.hash_seed = self.h.ctl.read('HASH_SEED')
        self.problems, self.copies, self.copy_bytes, self._copy = [], 0, 0, None
        rng = random.Random(seed * 0x2545_F491 + 0xA7)
        # traffic generator: stop, clear, load
        self._w(ATG_BASE, ATG_MCTL, 0)
        self._w(ATG_BASE, ATG_ERR, M.M32)
        self._w(ATG_BASE, ATG_ERR_EN, 0x8000_0000 | sum(1 << b for b in ATG_ERRS))
        self.rd_cmds = []
        for k in range(N_CMD):
            addr, beats = self._target(rng)
            ram = k * CMD_BYTES
            img = self._image(addr, beats * ATG_BEAT)
            for j in range(0, len(img), 4):
                self._w(ATG_BASE, ATG_MSTRAM + ram + j, int.from_bytes(img[j:j + 4], 'little'))
            for j, v in enumerate(self._cmd(addr, beats, k & 3, ram)):
                self._w(ATG_BASE, ATG_CMD_WR + 16 * k + 4 * j, v)
            addr, beats = self._target(rng)
            ram = RD_REGION + k * CMD_BYTES
            self.rd_cmds.append((addr, beats, ram))
            for j, v in enumerate(self._cmd(addr, beats, k & 3, ram)):
                self._w(ATG_BASE, ATG_CMD_RD + 16 * k + 4 * j, v)
        for base in (ATG_CMD_WR, ATG_CMD_RD):         # end of each list
            for j in range(4):
                self._w(ATG_BASE, base + 16 * N_CMD + 4 * j, 0)
        # DMA: never soft-reset it. Writing CDMACR.Reset resets its register
        # slave with the write still open: the B never comes, and the
        # configuration bridge waits for it forever (seen on the board,
        # axi_cdma v4.1, 2026-10-20). It leaves board reset idle; a run that
        # finds it in error stops using it instead.
        sr = self._r(CDMA_BASE, CDMA_SR)
        if not sr & CDMA_IDLE or any(sr >> b & 1 for b in CDMA_ERRS):
            self.problems.append(f'cdma: not idle and clean at the start (CDMASR {sr:#010x}); '
                                 f'reprogram the board')
        self._rng = rng
        self._w(ATG_BASE, ATG_MCTL, ATG_MSTEN | ATG_LOOP)
        self.active = not self.problems
        # the first copy goes before GO: a short run can end before the host's
        # first ALL_DONE poll, and so before any tick()
        self.tick()

    def _retire(self) -> bool:
        """The copy in flight, if it has ended: count it or record its error.
        False while it is still running."""
        if self._copy is None:
            return True
        sr = self._r(CDMA_BASE, CDMA_SR)
        if not sr & CDMA_IDLE:
            return False
        errs = [n for b, n in CDMA_ERRS.items() if sr >> b & 1]
        if errs:
            sa, da, n = self._copy
            self.problems.append(f'cdma {sa:#010x} -> {da:#010x} ({n} B): {errs}')
            self.active = False                          # an error halts it (see start)
        else:
            self.copies += 1
            self.copy_bytes += self._copy[2]
        self._copy = None
        return True

    def tick(self) -> None:
        """Advance the DMA: retire the copy in flight, start the next."""
        if not self.active or not self._retire() or not self.active:
            return
        rng = self._rng
        n = rng.randint(1, CDMA_MAX)
        off = rng.randrange(0, self.span - n)
        src, dst = rng.choice(self.mems), rng.choice(self.mems)
        self._copy = (src.base + off, dst.base + off, n)
        self._w(CDMA_BASE, CDMA_SA, src.base + off)
        self._w(CDMA_BASE, CDMA_DA, dst.base + off)
        self._w(CDMA_BASE, CDMA_BTT, n)                  # starts it

    def finish(self, sleep: Callable[[float], None] = time.sleep) -> List[str]:
        # the DMA: let the copy in flight end, and count it
        self.active = False
        for _ in range(200):
            if self._retire():
                break
            sleep(0.005)
        else:
            self.problems.append(f'cdma: copy {self._copy} never went idle')
        why = list(self.problems)
        # the traffic generator: end the loop, wait for the list to drain
        self._w(ATG_BASE, ATG_MCTL, ATG_MSTEN)
        for _ in range(400):
            if not self._r(ATG_BASE, ATG_MCTL) & ATG_MSTEN:
                break
            sleep(0.005)
        else:
            why.append('atg: did not finish its command list')
        err = self._r(ATG_BASE, ATG_ERR)
        bad = [n for b, n in ATG_ERRS.items() if err >> b & 1]
        if bad:
            why.append(f'atg: Error Status {err:#010x} {bad}')
        if not err >> 31 & 1:
            why.append(f'atg: Error Status {err:#010x}: MSTDONE never set')
        for addr, beats, ram in self.rd_cmds:
            exp = self._image(addr, beats * ATG_BEAT)
            for j in range(0, len(exp), 4):
                got = self._r(ATG_BASE, ATG_MSTRAM + ram + j)
                want = int.from_bytes(exp[j:j + 4], 'little')
                if got != want:
                    why.append(f'atg read {addr + j:#010x}: {got:#010x}, expected {want:#010x}')
                    break
        if self.copies == 0:
            why.append('cdma: no copy completed during the run')
        self.log(f'  vendor: atg {N_CMD}+{N_CMD} commands looped, cdma {self.copies} copies '
                 f'({self.copy_bytes} B)')
        return why
