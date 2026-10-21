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
    1..16 64-bit beats at random 8-byte-aligned offsets of ONE memory per
    run (DDR and BRAM alternate by seed), on IDs 0..3. Aimed at two memories
    at once it does not finish its list: every response arrives (the
    protocol checker on its link, bs_pc_atg, passes them all; an ILA on its
    port shows nothing outstanding), it raises no error, and MSTDONE never
    sets. Its completion pointer advances only on a one-cycle completion
    vector (the `| vec_ff` term is commented out in the shipped source), so a
    command that completes ahead of its predecessor -- two slaves, two
    latencies -- is lost. One memory answers in order. A run that finds it
    still busy from an earlier one leaves it alone (reloading its RAMs under
    it corrupts what it writes) and says so.
    The list runs once per start (no Master Control LOOP): in loop mode its
    read-completion pointer resets at the end of each pass, and with the
    stress masters' traffic varying the latencies it lost a completion and
    never finished. The host restarts the list each time it finishes while
    the run is live (tick()) and counts the passes. Write data comes from its master RAM, which the host loads
    with the image of each write's target; reads land in a second region of
    it. The host restarts the list while the run is live, then the
    host lets the last pass finish, reads its Error Status (it checks RID / BID against its
    outstanding IDs, BRESP / RRESP and RLAST itself) and compares every read
    byte with the image.
DMA (axi_cdma, simple mode, DRE), on ext1:
    copies between the memories at equal offsets (the two images agree
    there), random length and alignment, one after another while the run is
    live (tick() from StressHarness.wait_done); each must end Idle with no
    DMAIntErr / DMASlvErr / DMADecErr.

PG125 register map used here: 0x00 Master Control ([20] MSTEN; [19] LOOP, unused here),
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

# AXI Protocol Checkers (PG101) on the memory links. The top brings their
# status in on control EXT_STS (bs_genesys2_xil_top): EXT_STS0 [3] bs_pc_ddr,
# [4] bs_pc_bram, [11] bs_pc_atg asserted; EXT_STS1/2 bs_pc_ddr pc_status
# [63:0]; EXT_STS3 bs_pc_bram pc_status [31:0]. The flags hold until reset,
# so a run reports the ones that rose during it. Bit names: the checker's own
# ASSIGN_MARKED_DEBUG table (axi_protocol_checker v2.0).
PC_NAMES = (
    'AWADDR_BOUNDARY', 'AWADDR_WRAP_ALIGN', 'AWBURST', 'AWLEN_LOCK', 'AWCACHE',
    'AWLEN_FIXED', 'AWLEN_WRAP', 'AWSIZE', 'AWVALID_RESET', 'AWADDR_STABLE',
    'AWBURST_STABLE', 'AWCACHE_STABLE', 'AWID_STABLE', 'AWLEN_STABLE', 'AWLOCK_STABLE',
    'AWPROT_STABLE', 'AWSIZE_STABLE', 'AWQOS_STABLE', 'AWREGION_STABLE', 'AWVALID_STABLE',
    'RECS_AWREADY_MAX_WAIT', 'WDATA_NUM', 'WSTRB', 'WVALID_RESET', 'WDATA_STABLE',
    'WLAST_STABLE', 'WSTRB_STABLE', 'WVALID_STABLE', 'RECS_WREADY_MAX_WAIT', 'BRESP_WLAST',
    'BRESP_EXOKAY', 'BVALID_RESET', 'BRESP_AW', 'BID_STABLE', 'BRESP_STABLE',
    'BVALID_STABLE', 'RECM_BREADY_MAX_WAIT', 'ARADDR_BOUNDARY', 'ARADDR_WRAP_ALIGN', 'ARBURST',
    'ARLEN_LOCK', 'ARCACHE', 'ARLEN_FIXED', 'ARLEN_WRAP', 'ARSIZE',
    'ARVALID_RESET', 'ARADDR_STABLE', 'ARBURST_STABLE', 'ARCACHE_STABLE', 'ARID_STABLE',
    'ARLEN_STABLE', 'ARLOCK_STABLE', 'ARPROT_STABLE', 'ARSIZE_STABLE', 'ARQOS_STABLE',
    'ARREGION_STABLE', 'ARVALID_STABLE', 'RECS_ARREADY_MAX_WAIT', 'RDATA_NUM', 'RID',
    'RRESP_EXOKAY', 'RVALID_RESET', 'RDATA_STABLE', 'RID_STABLE', 'RLAST_STABLE',
)
PC_ASSERTED = {3: 'pc_ddr', 4: 'pc_bram', 11: 'pc_atg'}
# Flags the checker raises on legal traffic, so a run does not fail on them:
# it pairs each burst's beats with its AW only when the AW arrives first (its
# own source: "This prevents checking of write strobes for write data before
# address"). LiteDRAM takes W ahead of AW, legal AXI (A3.3.1): an ILA capture
# triggered on the flag (2026-10-20) shows a 256-beat burst's W flowing 60
# cycles before its AW handshake, every beat count correct, and WDATA_NUM on
# the cycle that AW landed. These two are judged in sim instead, by the
# framework's AXI4ComplianceChecker on the same links (bs_harness_tb), which
# does pair W before AW. LIMIT: a real WDATA_NUM / WSTRB on the board is
# therefore logged, not failed.
PC_W_BEFORE_AW = {'WDATA_NUM', 'WSTRB'}


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

    def _pc(self) -> Dict[str, int]:
        """The protocol checkers' flags: asserted bits and each pc_status."""
        rd = self.h.ctl.read
        return {'asserted': rd('EXT_STS0') & sum(1 << b for b in PC_ASSERTED),
                'ddr': rd('EXT_STS1') | rd('EXT_STS2') << 32,
                'bram': rd('EXT_STS3')}

    def _pc_new(self) -> List[str]:
        """The checker flags that rose since start(), by name."""
        now, why = self._pc(), []
        rose = now['asserted'] & ~self.pc0['asserted']
        for link in ('ddr', 'bram'):
            bits = now[link] & ~self.pc0[link]
            rose_n = [PC_NAMES[b] if b < len(PC_NAMES) else f'pc_status[{b}]'
                      for b in range(64) if bits >> b & 1]
            soft = [x for x in rose_n if x in PC_W_BEFORE_AW]
            hard = [x for x in rose_n if x not in PC_W_BEFORE_AW]
            if soft:
                self.log(f'  checkers: bs_pc_{link} {soft} (W ahead of AW; not judged on '
                         f'the board, see PC_W_BEFORE_AW)')
            if hard:
                why.append(f'bs_pc_{link}: ' + ', '.join(hard))
        if rose >> 11 & 1:
            why.append('bs_pc_atg: asserted (its pc_status is not brought out)')
        return why

    def _image(self, addr: int, n: int) -> bytes:
        return bytes(M.mem_byte(addr + i, self.hash_seed, MEM_TAG, MEM_LG2) for i in range(n))

    @staticmethod
    def _cmd(addr: int, beats: int, cid: int, ram_off: int) -> List[int]:
        """One PG125 command entry, four 32-bit words."""
        w1 = ((beats - 1) & 0xFF) | (1 << 10) | (3 << 12) | ((cid & 0x3F) << 15) | (1 << 31)
        w2 = ram_off & 0x1FFF        # master RAM BYTE address (13 bits = its 8 KB)
        w3 = 0b001                                  # expected response: OKAY
        return [addr & M.M32, w1, w2, w3]

    def _target(self, rng: random.Random) -> Tuple[int, int, int]:
        """(address, beats, memory index): an 8-byte-aligned INCR inside the
        shared span of this run's memory, not crossing 4 KB."""
        mi = self.atg_mem
        beats = rng.randint(1, CMD_BYTES // ATG_BEAT)
        while True:
            off = rng.randrange(0, self.span - beats * ATG_BEAT, ATG_BEAT)
            if (off & 0xFFF) + beats * ATG_BEAT <= 0x1000:
                return self.mems[mi].base + off, beats, mi

    # ---- the run -------------------------------------------------------------
    def _load_atg(self, rng: random.Random) -> None:
        """Clear the traffic generator's errors and load both command lists
        and the master RAM image the writes carry."""
        self._w(ATG_BASE, ATG_ERR, M.M32)
        self._w(ATG_BASE, ATG_ERR_EN, 0x8000_0000 | sum(1 << b for b in ATG_ERRS))
        self.rd_cmds = []
        for k in range(N_CMD):
            addr, beats, mi = self._target(rng)
            ram = k * CMD_BYTES
            img = self._image(addr, beats * ATG_BEAT)
            for j in range(0, len(img), 4):
                self._w(ATG_BASE, ATG_MSTRAM + ram + j, int.from_bytes(img[j:j + 4], 'little'))
            for j, v in enumerate(self._cmd(addr, beats, k & 3, ram)):
                self._w(ATG_BASE, ATG_CMD_WR + 16 * k + 4 * j, v)
            addr, beats, mi = self._target(rng)
            ram = RD_REGION + k * CMD_BYTES
            self.rd_cmds.append((addr, beats, ram))
            for j, v in enumerate(self._cmd(addr, beats, k & 3, ram)):
                self._w(ATG_BASE, ATG_CMD_RD + 16 * k + 4 * j, v)
        for base in (ATG_CMD_WR, ATG_CMD_RD):         # end of each list
            for j in range(4):
                self._w(ATG_BASE, base + 16 * N_CMD + 4 * j, 0)

    def start(self, prof, seed: int) -> None:
        self.seed = seed
        self.hash_seed = self.h.ctl.read('HASH_SEED')
        self.problems, self.copies, self.copy_bytes, self._copy = [], 0, 0, None
        self.atg_on = False
        self.pc0 = self._pc()
        rng = random.Random(seed * 0x2545_F491 + 0xA7)
        self.atg_mem = seed % len(self.mems)
        self.atg_on = not (self._r(ATG_BASE, ATG_MCTL) & ATG_MSTEN)
        if not self.atg_on:
            self.problems.append('atg: still busy from an earlier run -- left alone this run '
                                 '(reprogram to recover it)')
        if self.atg_on:
            self._load_atg(rng)
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
        self.atg_passes = 0
        if self.atg_on:
            self._w(ATG_BASE, ATG_MCTL, ATG_MSTEN)
        self.active = not any(p.startswith('cdma') for p in self.problems)
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
        """Restart the traffic generator's list when it has finished; advance
        the DMA: retire the copy in flight, start the next."""
        if self.atg_on and self.active:
            if not self._r(ATG_BASE, ATG_MCTL) & ATG_MSTEN:
                self.atg_passes += 1
                self._w(ATG_BASE, ATG_MCTL, ATG_MSTEN)
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
        if self.atg_on:
            # the traffic generator: let the pass in flight finish
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
        why += self._pc_new()
        self.log(f'  vendor: atg {N_CMD}+{N_CMD} commands on {self.mems[self.atg_mem].name} '
                 f'x{self.atg_passes + int(self.atg_on)} passes, cdma {self.copies} copies ({self.copy_bytes} B)')
        return why
