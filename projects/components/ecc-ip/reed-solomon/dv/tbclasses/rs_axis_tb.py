"""
rs_encoder / rs_decoder (AXI4-Stream tops) testbench

The two cores are already verified through their bare valid/ready ports by
rs_encoder_tb / rs_decoder_tb. This testbench exercises what the AXIS wrappers
ADD, and nothing else:

  stream        end-to-end equivalence through the stream interface: the
                encoder's m_axis beats match reedsolo, the decoder recovers the
                message from a corrupted codeword
  strobe        tstrb carries the symbol keep. At SYMBOL_WIDTH == 8 a byte IS a
                symbol so the two coincide; a partial final beat must come out
                with a partial tstrb, not all ones. This is the mapping most
                likely to be silently wrong, because a design where every beat
                is full never exercises it.
  sideband      tid and tdest are held across every beat of a block. A codeword
                leaves as a different number of beats than it entered as, so
                these cannot ride the datapath and are captured and held --
                which is exactly the kind of thing that works for one block and
                then leaks into the next.
  backpressure  the same under randomized master valid / slave ready, which is
                what proves the two skid wrappers were connected the right way
                round.

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import collections
import os
import random

import cocotb
from cocotb.triggers import RisingEdge

import reedsolo

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axis4.axis_factories import create_axis_master, create_axis_slave
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class RSAxisTB(TBBase):
    """Drives rs_encoder or rs_decoder over AXI4-Stream."""

    BLOCKS = {'gate': 4, 'func': 16, 'full': 48}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'bursty', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.role = os.environ.get('RS_AXIS_ROLE', 'encoder')
        self.m = self.convert_to_int(os.environ.get('SYMBOL_WIDTH', 8))
        self.prim = int(os.environ.get('PRIM_POLY', '0x11D'), 0)
        self.t = self.convert_to_int(os.environ.get('T_SYMBOLS', 8))
        self.n = self.convert_to_int(os.environ.get('N_SYMBOLS', 255))
        self.dw = self.convert_to_int(os.environ.get('DATA_WIDTH', 32))
        self.idw = self.convert_to_int(os.environ.get('AXIS_ID_WIDTH', 4))
        self.destw = self.convert_to_int(os.environ.get('AXIS_DEST_WIDTH', 2))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.s = self.dw // self.m            # symbols per beat
        self.k = self.n - 2 * self.t
        self.checks = 0
        self.mismatches = 0

        reedsolo.init_tables(prim=self.prim, generator=2, c_exp=self.m)
        self.rs = reedsolo

        self._init_bfms()

    def _init_bfms(self):
        # The factories return a dict of views onto one component ('T',
        # 'interface', 'master'/'slave'), not the component itself.
        self.master = create_axis_master(
            self.dut, self.dut.aclk, prefix='s_axis_', data_width=self.dw,
            id_width=self.idw, dest_width=self.destw, user_width=1,
            log=self.log)['master']
        self.slave = create_axis_slave(
            self.dut, self.dut.aclk, prefix='m_axis_', data_width=self.dw,
            id_width=self.idw, dest_width=self.destw, user_width=1,
            log=self.log)['slave']
        # Collect through the slave's documented callback rather than reaching
        # into its queue: the AXIS slave exposes add_callback /
        # get_observed_packets, and there is no _recvQ to poll.
        self._rx = collections.deque()
        self.slave.add_callback(self._rx.append)
        self.slave.set_ready_always()

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', period_ns, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # -- model ---------------------------------------------------------------
    def gold_encode(self, data):
        """The n systematic codeword symbols for k data symbols."""
        return list(self.rs.rs_encode_msg(bytearray(data), 2 * self.t, fcr=0))

    def beats_of(self, symbols):
        """Pack symbols low-symbol-first into (data, strb, last) beats."""
        out = []
        for i in range(0, len(symbols), self.s):
            chunk = symbols[i:i + self.s]
            word = 0
            for j, sym in enumerate(chunk):
                word |= (sym & ((1 << self.m) - 1)) << (j * self.m)
            out.append((word, (1 << len(chunk)) - 1, i + self.s >= len(symbols)))
        return out

    def symbols_of(self, beats):
        """Unpack (data, strb) beats back into symbols, honouring the strobe."""
        syms = []
        mask = (1 << self.m) - 1
        for word, strb in beats:
            for j in range(self.s):
                if (strb >> j) & 1:
                    syms.append((word >> (j * self.m)) & mask)
        return syms

    # -- stimulus ------------------------------------------------------------
    async def _send(self, symbols, tid, tdest):
        for word, strb, last in self.beats_of(symbols):
            # the packet's fields are data/strb/last/id/dest/user -- the AXIS
            # field config drops the 't' prefix the SIGNALS carry
            pkt = self.master.create_packet(
                data=word, strb=strb, last=int(last), id=tid, dest=tdest, user=0)
            await self.master.send(pkt)

    async def _collect(self, want_beats, timeout_cycles):
        """Drain want_beats beats, returning (data, strb, last, tid, tdest) tuples."""
        got = []
        waited = 0
        while len(got) < want_beats and waited < timeout_cycles:
            if self._rx:
                p = self._rx.popleft()
                got.append((int(p.data), int(p.strb), int(p.last),
                            int(p.id), int(p.dest)))
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1
        return got

    def _fail(self, msg):
        self.mismatches += 1
        self.log.error(msg)

    def _score(self, label, got, want_syms, tid, tdest):
        """Check symbols, the final strobe, tlast placement and the sidebands."""
        self.checks += 1
        want_beats = (len(want_syms) + self.s - 1) // self.s
        if len(got) != want_beats:
            self._fail(f"{label}: {len(got)} beats, expected {want_beats}")
            return
        syms = self.symbols_of([(d, st) for d, st, _, _, _ in got])
        if syms != want_syms:
            first = next((i for i, (a, b) in enumerate(zip(syms, want_syms)) if a != b),
                         min(len(syms), len(want_syms)))
            self._fail(f"{label}: symbols differ from symbol {first}: "
                       f"got {syms[first:first + 4]} want {want_syms[first:first + 4]}")
        # The strobe has to be LIVE, not hardwired to all ones. Checking the
        # LAST beat would be wrong: the encoder does not pack parity onto the
        # partial final data beat, so a codeword's last beat is a full parity
        # beat and the partial one sits mid-stream at the end of the data
        # phase. The decoder, emitting only the message, ends partial instead.
        # What holds for both is that a symbol count which is not a multiple of
        # S must produce at least one partial beat somewhere -- and if the
        # strobe were stuck at all ones the symbol comparison above would have
        # extracted too many symbols and already failed.
        full = (1 << self.s) - 1
        partials = [i for i, g in enumerate(got) if g[1] != full]
        if len(want_syms) % self.s and not partials:
            self._fail(f"{label}: {len(want_syms)} symbols over {self.s} per beat needs a "
                       f"partial beat, but every tstrb is 0x{full:X} -- the strobe is "
                       f"not carrying the symbol keep")
        for i in partials:
            if got[i][1] & (got[i][1] + 1):
                self._fail(f"{label}: beat {i} tstrb 0x{got[i][1]:X} is not low-aligned")
        # tlast exactly once, on the last beat
        lasts = [i for i, g in enumerate(got) if g[2]]
        if lasts != [len(got) - 1]:
            self._fail(f"{label}: tlast on beats {lasts}, expected only {len(got) - 1}")
        # tid / tdest held on EVERY beat
        bad_id = [i for i, g in enumerate(got) if g[3] != tid]
        bad_dest = [i for i, g in enumerate(got) if g[4] != tdest]
        if bad_id:
            self._fail(f"{label}: tid wrong on beats {bad_id[:4]} (want {tid})")
        if bad_dest:
            self._fail(f"{label}: tdest wrong on beats {bad_dest[:4]} (want {tdest})")

    # -- scenarios -----------------------------------------------------------
    def set_profile(self, name):
        """Same timing-profile plumbing the core testbenches use."""
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    async def run_stream(self, profile='backtoback'):
        """Blocks end to end through the stream, with the sidebands varied."""
        self.set_profile(profile)
        rnd = random.Random(0xA715 + (sum(map(ord, profile)) * 7919))
        blocks = self.BLOCKS[self.level]
        for b in range(blocks):
            msg = [rnd.randrange(1 << self.m) for _ in range(self.k)]
            cw = self.gold_encode(msg)
            tid = rnd.randrange(1 << self.idw) if self.idw else 0
            tdest = rnd.randrange(1 << self.destw) if self.destw else 0
            if self.role == 'encoder':
                await self._send(msg, tid, tdest)
                want = cw
            else:
                rx = list(cw)
                e = rnd.randint(0, self.t)
                for p in rnd.sample(range(self.n), e):
                    rx[p] ^= rnd.randrange(1, 1 << self.m)
                await self._send(rx, tid, tdest)
                want = msg
            got = await self._collect((len(want) + self.s - 1) // self.s,
                                      timeout_cycles=40 * self.n + 4000)
            self._score(f"{profile} block {b}", got, want, tid, tdest)
        return self.mismatches == 0

    async def run_backpressure(self):
        """The same blocks under randomized valid/ready on both sides.

        This is what proves the two skid wrappers are connected the right way
        round: a swapped ready compares clean at full rate and only breaks once
        either side stalls.
        """
        ok = True
        for profile in self.PROFILES[self.level]:
            if profile == 'backtoback':
                continue
            ok &= await self.run_stream(profile)
        return ok

    def get_test_report(self):
        return {'role': self.role, 'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"RS({self.n},{self.k}) m={self.m} t={self.t} S={self.s}"}
