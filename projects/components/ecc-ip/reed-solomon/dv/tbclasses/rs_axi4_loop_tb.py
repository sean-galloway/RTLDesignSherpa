"""
rs_encoder_axi4 / rs_decoder_axi4 testbench (full memory-to-memory loop)

messages -> M1 -> encode -> M2 -> decode -> M3 -> messages, with three real
sdpram memories in the chain. What this proves that the engine-level test
cannot:

  - the codec tops compute their own beat counts from a BLOCK count, and the
    source and destination counts differ (k in, n out for the encoder; n in, k
    out for the decoder). An off-by-one in either direction shows up here as a
    short read, a hung job, or a frame error.
  - a codeword occupies K_BEATS + P_BEATS beats, not ceil(N/S), because the
    encoder starts parity on a fresh beat instead of packing it onto a partial
    final data beat. The decoder has to present the received beats with the
    SAME keep pattern, reconstructed from the beat index. On a profile where
    both phases fill their beats this is invisible, so the parameter list
    includes one where they do not.
  - every job asserts cfg_done. A job that completes silently but never raises
    done would hang a host, so done is checked as hard as the data.

No errors are injected, so every block must come back CLEAN -- which also
means the decoder's accumulated counters are checked, not just the data.

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class RSAxi4LoopTB(TBBase):
    """Runs the seed / encode / decode / drain chain and checks the round trip."""

    BLOCKS = {'gate': 2, 'func': 6, 'full': 16}
    LENS = {'gate': [16], 'func': [1, 16], 'full': [1, 7, 16, 64]}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.m = self.convert_to_int(os.environ.get('SYMBOL_WIDTH', 8))
        self.t = self.convert_to_int(os.environ.get('T_SYMBOLS', 8))
        self.n = self.convert_to_int(os.environ.get('N_SYMBOLS', 252))
        self.dw = self.convert_to_int(os.environ.get('DATA_WIDTH', 32))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.s = self.dw // self.m
        self.k = self.n - 2 * self.t
        self.k_beats = -(-self.k // self.s)
        self.p_beats = -(-(2 * self.t) // self.s)
        self.cw_beats = self.k_beats + self.p_beats
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()

    def _init_bfms(self):
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="SEED", prefix="in_", clock=self.dut.aclk,
                                 field_config=fc, pkt_prefix="", multi_sig=True, log=self.log)
        fc2 = FieldConfig()
        fc2.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc2.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="DRAIN", prefix="out_", clock=self.dut.aclk,
                               field_config=fc2, pkt_prefix="", multi_sig=True, log=self.log)

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', period_ns, 'ns')
        for sig in ('seed_start', 'enc_start', 'dec_start', 'drain_start'):
            getattr(self.dut, sig).value = 0
        self.dut.seed_beats.value = 0
        self.dut.drain_beats.value = 0
        self.dut.drain_per_block.value = 1
        self.dut.blocks.value = 0
        self.dut.burst_len.value = 16
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    def _fail(self, msg):
        self.mismatches += 1
        self.log.error(msg)

    async def _pulse(self, sig):
        sig.value = 1
        await RisingEdge(self.dut.aclk)
        sig.value = 0

    async def _await_done(self, sig, label, limit):
        """Wait for a job's done, having first seen it CLEAR.

        cfg_done is held from one job until the next cfg_start, so polling it
        straight after the start pulse reads the PREVIOUS job's done and
        returns immediately. That is what happened here: the second iteration
        started its drain while the decode was still running, and the whole
        message came back wrong in the fast profile and partly wrong in the
        throttled one -- which is the shape of a race, not of bad data.
        """
        for _ in range(64):                       # the start pulse clears it
            if not int(sig.value):
                break
            await RisingEdge(self.dut.aclk)
        else:
            self._fail(f"{label}: done never cleared after cfg_start")
            return False
        for _ in range(limit):
            if int(sig.value):
                return True
            await RisingEdge(self.dut.aclk)
        self._fail(f"{label}: done never asserted within {limit} cycles")
        return False

    # -- the round trip ------------------------------------------------------
    async def run_loop(self, blocks, burst_len, profile='backtoback'):
        self.checks += 1
        self.set_profile(profile)
        # Each iteration re-seeds M1 at address 0 with a DIFFERENT pattern, so
        # anything the previous drain left in the slave's queue would be read
        # as this run's first beats. That is what it looked like: beat 0 came
        # back carrying the previous burst length's word.
        self.slave._recvQ.clear()
        rnd = random.Random(0xC0DE + blocks * 977 + burst_len)
        mask = (1 << self.dw) - 1
        msg_beats = blocks * self.k_beats
        words = [rnd.randrange(1 << self.dw) & mask for _ in range(msg_beats)]
        label = f"blocks={blocks} len={burst_len} {profile}"
        budget = 400 * blocks * self.cw_beats + 20000

        self.dut.blocks.value = blocks
        self.dut.burst_len.value = burst_len

        # ---- seed M1 with the messages
        self.dut.seed_beats.value = msg_beats
        await self._pulse(self.dut.seed_start)
        for i, w in enumerate(words):
            await self.master.send(self.master.create_packet(
                data=w, last=int((i + 1) % self.k_beats == 0)))
        if not await self._await_done(self.dut.seed_done, f"{label} seed", budget):
            return

        # ---- encode M1 -> M2
        await self._pulse(self.dut.enc_start)
        if not await self._await_done(self.dut.enc_done, f"{label} encode", budget):
            return
        if int(self.dut.enc_resp_err.value):
            self._fail(f"{label}: encoder resp_err")
        if int(self.dut.enc_frame_err.value):
            self._fail(f"{label}: encoder frame_err -- a block was not k symbols")

        # ---- decode M2 -> M3
        await self._pulse(self.dut.dec_start)
        if not await self._await_done(self.dut.dec_done, f"{label} decode", budget):
            return
        if int(self.dut.dec_resp_err.value):
            self._fail(f"{label}: decoder resp_err")

        # no errors were injected, so every block must be CLEAN
        ok = int(self.dut.dec_blocks_ok.value)
        corr = int(self.dut.dec_blocks_corrected.value)
        unc = int(self.dut.dec_blocks_uncorrectable.value)
        fr = int(self.dut.dec_blocks_frame_err.value)
        if (ok, corr, unc, fr) != (blocks, 0, 0, 0):
            self._fail(f"{label}: verdicts ok/corr/unc/frame = {ok}/{corr}/{unc}/{fr}, "
                       f"expected {blocks}/0/0/0 on an error-free loop")

        # ---- drain M3 and compare
        self.dut.drain_beats.value = msg_beats
        self.dut.drain_per_block.value = self.k_beats
        await self._pulse(self.dut.drain_start)
        got, waited = [], 0
        while len(got) < msg_beats and waited < budget:
            if self.slave._recvQ:
                got.append(int(self.slave._recvQ.popleft().data) & mask)
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1
        if not await self._await_done(self.dut.drain_done, f"{label} drain", 8000):
            return
        if len(got) != msg_beats:
            self._fail(f"{label}: drained {len(got)} of {msg_beats} beats")
            return
        if got != words:
            diffs = [i for i, (a, b) in enumerate(zip(got, words)) if a != b]
            first = diffs[0]
            # Is it a SHIFT rather than corruption? A whole-block or whole-beat
            # offset says the addressing or the beat accounting slipped; a
            # scattered difference says the data itself is wrong.
            shift = None
            for off in range(1, min(len(words), self.cw_beats * 2 + 4)):
                if got[off:] == words[:len(got) - off]:
                    shift = off; break
                if words[off:] == got[:len(words) - off]:
                    shift = -off; break
            self._fail(
                f"{label}: {len(diffs)} of {len(words)} beats differ, first at {first} "
                f"(got 0x{got[first]:08X}, sent 0x{words[first]:08X}); "
                + (f"the stream is SHIFTED by {shift} beats "
                   f"({shift / self.k_beats:.2f} blocks)" if shift is not None
                   else "no whole-beat shift explains it, so the data itself is wrong"))

    async def run_bursts(self):
        for ln in self.LENS[self.level]:
            await self.run_loop(self.BLOCKS[self.level], ln)
        return self.mismatches == 0

    async def run_backpressure(self):
        for profile in self.PROFILES[self.level]:
            if profile == 'backtoback':
                continue
            await self.run_loop(self.BLOCKS[self.level], 16, profile=profile)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"RS({self.n},{self.k}) m={self.m} t={self.t} S={self.s}",
                'beats': f"K_BEATS={self.k_beats} P_BEATS={self.p_beats} CW={self.cw_beats}"}
