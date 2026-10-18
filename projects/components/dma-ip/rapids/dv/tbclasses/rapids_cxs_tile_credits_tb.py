# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_cxs_tile_credits_tb
# Purpose: rapids_cxs_top built with TILE_HDR = 1, TILE_CREDITS = 1: end-to-end
#          tile credits, the advertisement window and the legal-destination
#          mask (TILE_SPEC 11.9 / 11.10)
#
# Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-18
"""RAPIDS as the tile I/O, with end-to-end credits.

The testbench plays the destinations: after reset each one that is present
sends a `set` credit packet (its input buffer in flits) into the sink port,
and later `add` packets as it consumes. RAPIDS must then
  * send a packet only when its destination's counter covers every flit,
    header included, and charge it that many;
  * when the advertisement window closes, save every destination still at 0
    as illegal, and refuse a descriptor to it.
Counter index (rapids_pkg::tile_dest_index) is {ext, n}: n = cell-level node
{Y[1:0], X[1:0]}, tetrad node 16 + {Y[0], X[0]}, root node 20 + X[0], 22-31
spare; ext = 0 the node itself, ext = 1 what is attached to it, so a cell is
32 + {Y, X}. Every node has both IDs; only one with something attached
advertises an external one.
"""

from typing import Any, Dict, List, Tuple

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_tb import (
    PTYPE_CFG, PTYPE_CREDIT, PTYPE_MEM, RAPIDS_COORD, RapidsCxsTileTB, TileHeader, coord)

OP_ADD, OP_SET = 0, 1
CLASS_SPACE, CLASS_DESC = 0, 1
LEVEL_CELL, LEVEL_TETRAD, LEVEL_ROOT = 0, 1, 2


def dest_index(c: int) -> int:
    """rapids_pkg::tile_dest_index for a coordinate with an index."""
    ext, level, x, y = (c >> 14) & 1, (c >> 12) & 3, (c >> 8) & 0xF, (c >> 4) & 0xF
    if level == LEVEL_CELL:
        n = (y & 3) << 2 | (x & 3)
    elif level == LEVEL_TETRAD:
        n = 16 + ((y & 1) << 1 | (x & 1))
    else:
        n = 20 + (x & 1)
    return ext << 5 | n


def cell(x: int, y: int) -> int:
    """A cell: the external ID of its cell-level node."""
    return coord(LEVEL_CELL, x, y, 0, ext=1)


class RapidsCxsTileCreditsTB(RapidsCxsTileTB):
    """rapids_cxs_top with TILE_HDR = 1 and TILE_CREDITS = 1."""

    # ---- what a destination sends ---------------------------------------
    async def send_credit(self, src: int, count: int, op: int = OP_ADD, cls: int = CLASS_SPACE):
        """A header-only credit packet from `src` to RAPIDS (level 3)."""
        await self.cell_send(0, TileHeader(dst=RAPIDS_COORD, src=src, ptype=PTYPE_CREDIT, op=op,
                                           length=count, target=cls, tag=0))

    async def advertise(self, buffers: Dict[int, int]):
        for c, n in buffers.items():
            await self.send_credit(c, n, op=OP_SET)

    # ---- the window ------------------------------------------------------
    async def adv_status(self) -> Tuple[int, int]:
        done = await self.read_reg('src', 'TILE_CREDIT_STATUS') & 1
        lo = await self.read_reg('src', 'TILE_LEGAL_DEST_LO')
        hi = await self.read_reg('src', 'TILE_LEGAL_DEST_HI')
        return done, hi << 32 | lo

    async def wait_window_closed(self, timeout_cycles: int = 20000) -> bool:
        for _ in range(timeout_cycles // 100):
            if await self.read_reg('src', 'TILE_CREDIT_STATUS') & 1:
                return True
            await self.wait_clocks(self.clk_name, 100)
        return False

    async def open_window(self, buffers: Dict[int, int]) -> List[str]:
        """The boot sequence: the window must still be open, the present
        destinations advertise, and the window closes with exactly them legal."""
        errs = []
        done, legal = await self.adv_status()
        if done:
            return ["the advertisement window closed before the destinations advertised "
                    "(bring-up too long for SRC.TILE_ADV_WINDOW)"]
        if legal:
            errs.append(f"TILE_LEGAL_DEST = 0x{legal:016X} before the window closed, expected 0")
        await self.advertise(buffers)
        if not await self.wait_window_closed():
            return errs + ["the advertisement window never closed"]
        _, legal = await self.adv_status()
        want = sum(1 << dest_index(c) for c, n in buffers.items() if n)
        if legal != want:
            errs.append(f"TILE_LEGAL_DEST = 0x{legal:016X}, expected 0x{want:016X}")
        return errs

    # ---- source traffic --------------------------------------------------
    def flits(self, nbytes: int, op: int = 0) -> int:
        return 1 if op else 1 + -(-nbytes // self.STRB_WIDTH)

    def _src_desc(self, channel: int, k: int, beats: int, dst: int, target: int,
                  ptype: int = PTYPE_MEM, op: int = 0, tag: int = 0x70) -> Tuple[int, TileHeader, List[int]]:
        """Preload a source buffer and return (descriptor, expected header, payload)."""
        src = self.SRC_BASE + channel * self.CHANNEL_OFFSET + k * 0x1_0000
        pat = [] if op else self._pattern(tag + k, channel, beats)
        if pat:
            self.preload_source(src, pat)
        nbytes = beats * self.STRB_WIDTH
        desc = self.create_tile_descriptor(src, nbytes, dst, target, ptype=ptype, op=op,
                                           channel_id=channel)
        return desc, TileHeader(dst, RAPIDS_COORD, ptype, op, nbytes, target, channel), pat

    async def kick(self, channel: int, desc: int):
        addr = self.DESC_BASE + channel * 0x1000 + (len(self.egress_packets(channel)) * 0x40)
        self.register_descriptor(self.desc_src_mem, addr, desc)
        await self.kick_off_channel('src', channel, addr)

    async def settle(self, cycles: int = 1500):
        await self.wait_clocks(self.clk_name, cycles)

    # =====================================================================
    # Scenarios
    # =====================================================================
    async def test_window(self) -> Tuple[bool, Dict[str, Any]]:
        """Boot: the destinations that advertise a non-zero count are legal;
        one that advertises 0, the spares and one that advertises after the
        window are not. A descriptor kicked while the window is open waits for
        it to close, then goes."""
        self.log.info("=== TILE credits: advertisement window and legal mask ===")
        cell_a, cell_b, cell_zero = cell(1, 1), cell(2, 3), cell(3, 0)
        node_a = coord(LEVEL_CELL, 1, 1, 0)             # cell_a's own node: internal
        tetrad, root = coord(LEVEL_TETRAD, 1, 0, 0), coord(LEVEL_ROOT, 0, 0, 0)
        core = coord(LEVEL_TETRAD, 1, 0, 0, ext=1)      # that tetrad's control core
        errors = []
        done, _ = await self.adv_status()
        if done:
            return self._finish(["the window closed before the test could start"], "window")
        # kicked while the window is open: must wait for it
        desc, hdr, pat = self._src_desc(0, 0, 2, cell_a, 0x100)
        await self.kick(0, desc)
        await self.settle(200)
        if self.egress_packets(0):
            errors.append("a tile packet left before the advertisement window closed")
        errors += await self.open_window({cell_a: 64, cell_b: 64, node_a: 4, tetrad: 8, core: 2,
                                          root: 8, cell_zero: 0})
        late = cell(0, 2)
        await self.send_credit(late, 64, op=OP_SET)
        await self.settle(100)
        _, legal = await self.adv_status()
        if legal >> dest_index(late) & 1:
            errors.append("an advertisement after the window made its destination legal")
        if not await self.wait_egress_packets(0, 1):
            errors.append("the descriptor kicked during the window never went out after it closed")
        await self.settle(200)
        pkts = self.egress_packets(0)
        if pkts:
            errors += self.check_packet(pkts[0], hdr, pat, "held descriptor")
        if self.read_sched_error('src') not in (0, -1):
            errors.append(f"src_sched_error=0x{self.read_sched_error('src'):X}")
        return self._finish(errors, "advertisement window")

    async def test_no_oversend(self, beats: int = 4) -> Tuple[bool, Dict[str, Any]]:
        """A cell with room for exactly one packet takes one; the second waits
        until the cell returns credits, then goes. A return of class 1, and
        one from a coordinate with no counter, change nothing."""
        self.log.info("=== TILE credits: never oversend a destination ===")
        dst = cell(2, 1)
        per = self.flits(beats * self.STRB_WIDTH)
        errors = await self.open_window({dst: per})
        d0, h0, p0 = self._src_desc(1, 0, beats, dst, 0x40)
        d1, h1, p1 = self._src_desc(1, 1, beats, dst, 0x80)
        await self.kick(1, d0)
        if not await self.wait_egress_packets(1, 1):
            errors.append("the first packet did not go out against the advertised credits")
        await self.kick(1, d1)
        await self.settle()
        if len(self.egress_packets(1)) != 1:
            errors.append(f"{len(self.egress_packets(1))} packets with credits for 1")
        await self.send_credit(dst, per, cls=CLASS_DESC)                  # wrong class
        await self.send_credit(coord(LEVEL_CELL, 7, 0, 0, ext=1), per)    # no counter
        await self.send_credit(coord(LEVEL_CELL, 2, 1, 0), per)           # the cell's node, not the cell
        await self.settle()
        if len(self.egress_packets(1)) != 1:
            errors.append("a class-1 credit, one from an unindexed coordinate or one for the "
                          "cell's own node released a packet to the cell")
        await self.send_credit(dst, per - 1)                              # one short
        await self.settle()
        if len(self.egress_packets(1)) != 1:
            errors.append("a packet went out with one flit of credit missing")
        await self.send_credit(dst, 1)                                    # exactly enough now
        if not await self.wait_egress_packets(1, 2):
            errors.append("the second packet did not go out once its credits returned")
        await self.settle(200)
        pkts = self.egress_packets(1)
        for k, (hdr, pat) in enumerate(((h0, p0), (h1, p1))):
            if k < len(pkts):
                errors += self.check_packet(pkts[k], hdr, pat, f"packet {k}")
        return self._finish(errors, "no oversend")

    async def test_shared_counter(self, beats: int = 2) -> Tuple[bool, Dict[str, Any]]:
        """Two channels writing one cell share its counter: with room for one
        packet, one channel sends and the other waits for the return."""
        self.log.info("=== TILE credits: concurrent channels share a cell's counter ===")
        dst = cell(0, 3)
        per = self.flits(beats * self.STRB_WIDTH)
        errors = await self.open_window({dst: per})
        d2, _h2, _ = self._src_desc(2, 0, beats, dst, 0x10)
        d3, _h3, _ = self._src_desc(3, 0, beats, dst, 0x20)
        await self.kick(2, d2)
        await self.kick(3, d3)
        await self.settle()
        sent = len(self.egress_packets(2)) + len(self.egress_packets(3))
        if sent != 1:
            errors.append(f"{sent} packets from two channels with credits for one")
        await self.send_credit(dst, per)
        await self.settle()
        sent = len(self.egress_packets(2)) + len(self.egress_packets(3))
        if sent != 2:
            errors.append(f"{sent} packets after the return, expected 2")
        return self._finish(errors, "shared counter")

    async def test_node_destination(self) -> Tuple[bool, Dict[str, Any]]:
        """A tetrad node is an endpoint for what is addressed to it: it
        advertises its buffer, a cfg write to it spends against it, and the
        next waits for its return. A read request spends one flit."""
        self.log.info("=== TILE credits: node-addressed packets ===")
        node = coord(LEVEL_TETRAD, 0, 1, 0)
        errors = await self.open_window({node: 4})
        d0, h0, p0 = self._src_desc(4, 0, 2, node, 0x8, ptype=PTYPE_CFG)     # 3 flits
        d1, _h1, _ = self._src_desc(4, 1, 2, node, 0xC, ptype=PTYPE_CFG)     # 3 more
        await self.kick(4, d0)
        if not await self.wait_egress_packets(4, 1):
            errors.append("the cfg write did not go out against the node's credits")
        await self.kick(4, d1)
        await self.settle()
        if len(self.egress_packets(4)) != 1:
            errors.append("a second cfg write went out with 1 credit left")
        d2, h2, _ = self._src_desc(5, 0, 8, node, 0x0, op=1)                 # read: 1 flit
        await self.kick(5, d2)
        if not await self.wait_egress_packets(5, 1):
            errors.append("a read request (1 flit) did not go out on the last credit")
        await self.send_credit(node, 3)
        if not await self.wait_egress_packets(4, 2):
            errors.append("the second cfg write did not go out after the node returned credits")
        await self.settle(200)
        if self.egress_packets(4):
            errors += self.check_packet(self.egress_packets(4)[0], h0, p0, "cfg write")
        if self.egress_packets(5):
            errors += self.check_packet(self.egress_packets(5)[0], h2, [], "read request")
        return self._finish(errors, "node destination")

    async def test_illegal_refused(self) -> Tuple[bool, Dict[str, Any]]:
        """After the window: a descriptor to a destination that never
        advertised, to one that advertised 0, to a spare index and to a
        coordinate with no index is refused -- its channel errors and sends
        nothing -- while one to a legal destination still goes."""
        self.log.info("=== TILE credits: illegal destinations refused ===")
        good = cell(1, 2)
        zero = cell(3, 3)
        errors = await self.open_window({good: 16, zero: 0})
        bad = {0: cell(0, 0),                       # never advertised
               1: zero,                             # advertised 0
               2: coord(LEVEL_ROOT, 3, 0, 0),       # root past 1: no index
               3: coord(3, 0, 0, 0),                # level 3, the tile I/O itself
               4: coord(LEVEL_CELL, 1, 2, 0)}       # the good cell's own node: internal, never advertised
        for ch, dst in bad.items():
            desc, _, _ = self._src_desc(ch, 0, 1, dst, 0)
            await self.kick(ch, desc)
        desc, hdr, pat = self._src_desc(6, 0, 1, good, 0x4)
        await self.kick(6, desc)
        await self.settle(800)
        se = self.read_sched_error('src')
        want = sum(1 << ch for ch in bad)
        if se != want:
            errors.append(f"src_sched_error=0x{se:X}, expected 0x{want:X}")
        for ch in bad:
            if self.egress_packets(ch):
                errors.append(f"ch{ch} sent {len(self.egress_packets(ch))} packets to an illegal destination")
        if not self.egress_packets(6):
            errors.append("the descriptor to a legal destination did not go out")
        else:
            errors += self.check_packet(self.egress_packets(6)[0], hdr, pat, "legal destination")
        return self._finish(errors, "illegal destinations")
