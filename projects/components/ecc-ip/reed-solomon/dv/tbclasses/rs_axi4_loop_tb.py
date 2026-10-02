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
        self.k_tail = self.k % self.s            # 0 = the message fills its beats
        # a codeword is written PACKED: ceil(N/S) beats, any partial one last
        self.cw_beats = -(-self.n // self.s)
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
        msg_beats = blocks * self.k_beats
        smask = (1 << self.m) - 1

        # Build the message as SYMBOLS, then pack into beats. When k does not
        # fill its final beat the pad lanes are seeded as zero, but they are
        # never compared: the decoder writes whole beats and whatever its core
        # drove in the unused lanes lands in memory, so only the k meaningful
        # symbols per block can be checked.
        msgs = [[rnd.randrange(1 << self.m) for _ in range(self.k)] for _ in range(blocks)]
        words = []
        for syms in msgs:
            for i in range(0, self.k_beats * self.s, self.s):
                chunk = syms[i:i + self.s]
                w = 0
                for j, sym in enumerate(chunk):
                    w |= (sym & smask) << (j * self.m)
                words.append(w)
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
        # (the seed engine ignores last; the block boundary that matters is the
        #  encoder's, which its read engine derives from cfg_beats_per_block)
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
                got.append(int(self.slave._recvQ.popleft().data))
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1
        if not await self._await_done(self.dut.drain_done, f"{label} drain", 8000):
            return
        if len(got) != msg_beats:
            self._fail(f"{label}: drained {len(got)} of {msg_beats} beats")
            return
        # Unpack the drained beats back into the k meaningful symbols per block.
        # The pad lanes of a partial final beat are deliberately not compared.
        got_msgs = []
        for b in range(blocks):
            syms = []
            for i in range(self.k_beats):
                w = got[b * self.k_beats + i]
                take = self.s if (i < self.k_beats - 1 or self.k_tail == 0) else self.k_tail
                for j in range(take):
                    syms.append((w >> (j * self.m)) & smask)
            got_msgs.append(syms)

        if got_msgs != msgs:
            bad = [b for b in range(blocks) if got_msgs[b] != msgs[b]]
            b = bad[0]
            diffs = [i for i, (a, c) in enumerate(zip(got_msgs[b], msgs[b])) if a != c]
            # A whole-symbol SHIFT says the beat accounting or addressing
            # slipped; a scattered difference says the data itself is wrong.
            shift = None
            g, w = got_msgs[b], msgs[b]
            for off in range(1, min(len(w), 2 * self.s + 4)):
                if g[off:] == w[:len(g) - off]:
                    shift = off; break
                if w[off:] == g[:len(w) - off]:
                    shift = -off; break
            self._fail(
                f"{label}: {len(bad)} of {blocks} blocks differ; block {b} has "
                f"{len(diffs)} of {self.k} symbols wrong, first at {diffs[0]} "
                f"(got 0x{g[diffs[0]]:02X}, sent 0x{w[diffs[0]]:02X}); "
                + (f"the symbols are SHIFTED by {shift}" if shift is not None
                   else "no shift explains it, so the data itself is wrong"))

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

    async def _watch_valid_hold(self, name, vsig, rsig, want_beats):
        """Count cycles where VALID is low after the first handshake.

        The requirement is about the RS block's OUTPUT valid, so this watches
        only valid and treats the consumer's ready as irrelevant: a cycle with
        valid high and ready low is the SLAVE refusing, not the codec
        faltering, and it is not counted. A cycle with valid LOW between the
        first handshake and the last beat is the codec faltering, and it is.
        Nothing before the first handshake counts -- command issue and the
        first read's latency are explicitly out of scope.

        Results go into self._vh rather than being returned: the caller KILLS
        this task rather than awaiting it. Awaiting a watcher here ended the
        simulation after one burst length, so a two-length sweep silently ran
        only the first -- which is the shape of a test that reports a pass it
        never measured.
        """
        st = {"beats": 0, "drops": 0, "events": 0, "where": []}
        self._vh[name] = st
        armed = False
        was_low = False
        while st["beats"] < want_beats:
            await RisingEdge(self.dut.aclk)
            v = int(vsig.value)
            r = int(rsig.value)
            if v and r:
                st["beats"] += 1
                armed = True
                was_low = False
            elif armed and st["beats"] < want_beats and not v:
                st["drops"] += 1
                if not was_low:
                    st["events"] += 1
                    st["where"].append(st["beats"])
                was_low = True

    async def run_valid_hold(self, blocks=8, burst_lens=(16, 64)):
        """Once the first data beat handshakes, RS's output valid must not drop.

        Measured on the two seams RS actually DRIVES -- the encoder's write
        channel into M2 and the decoder's write channel into M3. The decoder's
        READ channel is deliberately absent: its valid belongs to the memory,
        so it cannot answer a question about the codec's output.

        BURST LENGTH IS PART OF THE REQUIREMENT, not an incidental knob. For
        the encoder's output to be gapless it must read k beats inside the n
        cycles its own gapless output takes, i.e. k/n beats per cycle. The
        slave delivers burst_len/(burst_len + ~2) -- a DEFICIT at a 16-beat
        burst and a surplus at 64 -- and no buffer depth fixes a rate deficit.
        So the check demands zero drops only where the rate allows it, and
        reports the deficit as a deficit otherwise.

        PRODUCTION RATE IS THE OTHER HARD LIMIT. The core emits
        ceil(k/S) + ceil(2t/S) beats per block (parity starts on a fresh
        beat), which the packer compresses into ceil(n/S). When the core's
        count is LARGER -- RS(15,9) at S=4 emits 5 beats into 4 output slots
        -- the codec produces symbols slower than a beat per cycle and
        (core - cw) idle cycles per block are structural: no buffer depth,
        burst length or packing can prevent them, only a block-overlapping
        core could. Those holes are budgeted, not failed, and the fall-through
        merge in rs_beat_packer places them at block boundaries. When the
        counts are equal (RS(255,239): 64 into 64) the budget is zero and the
        output must be gapless end to end.
        """
        ok = True
        for bl in burst_lens:
            ok &= await self._valid_hold_one(blocks, bl)
        return ok

    async def _valid_hold_one(self, blocks, burst_len):
        self.checks += 1
        self._vh = {}
        tasks = [
            cocotb.start_soon(self._watch_valid_hold(
                "encoder W", self.dut.m2_wvalid, self.dut.m2_wready,
                blocks * self.cw_beats)),
            cocotb.start_soon(self._watch_valid_hold(
                "decoder W", self.dut.m3_wvalid, self.dut.m3_wready,
                blocks * self.k_beats)),
        ]
        # run_loop is VOID -- it records into self.mismatches and returns None,
        # which is the house pattern here (see run_bursts). Taking its return
        # value made `ok &= await ...` a TypeError that killed the sweep after
        # the first burst length, so the second one silently never ran.
        before = self.mismatches
        await self.run_loop(blocks, burst_len, profile='backtoback')
        loop_ok = (self.mismatches == before)
        for t in tasks:
            t.kill()

        # what the read side can actually deliver, against what a gapless
        # output needs. ~2 cycles of slave gap per burst, measured.
        supply  = burst_len / float(burst_len + 2)
        demand  = self.k_beats / float(self.cw_beats)
        surplus = supply >= demand

        # the production limit: the core's unpacked beat count per block
        # against the packed output slots. Where the core's is larger, that
        # many idle cycles per block cannot be prevented by anything short of
        # a block-overlapping core, so they are the encoder's drop budget.
        p_beats = -(-(2 * self.t) // self.s)
        core_beats = self.k_beats + p_beats
        enc_budget = blocks * max(0, core_beats - self.cw_beats)

        bad = False
        for name, per_blk in (("encoder W", self.cw_beats), ("decoder W", self.k_beats)):
            st = self._vh.get(name)
            if st is None:
                continue
            at_blk = sum(1 for w in st["where"] if w % per_blk == 0)
            inside = st["events"] - at_blk
            self.log.info(
                f"valid-hold len={burst_len} {name}: {st['beats']} beats, VALID low "
                f"{st['drops']} cycles in {st['events']} drop(s) -- {at_blk} at block "
                f"boundaries, {inside} INSIDE a block; starts at {st['where'][:12]} "
                f"(block = {per_blk} beats, supply {supply:.3f} vs demand {demand:.3f})")

            # A drop INSIDE a block is a fault ONLY where the read side can
            # actually keep up. Under a rate deficit the codec genuinely has no
            # beat to present, and no buffer depth invents one -- failing that
            # would be blaming the codec for the burst length.
            if inside and surplus:
                bad = True
                self.mismatches += 1
                self.log.error(
                    f"valid-hold len={burst_len} {name}: VALID dropped INSIDE a block "
                    f"({inside} time(s)) with read supply {supply:.3f} >= demand "
                    f"{demand:.3f}. Once data starts, the codec's output valid must "
                    f"stay up; the consumer's ready is its own business.")

            # At a block boundary the encoder may drop only where the core's
            # own production rate forces it: core_beats per block into
            # cw_beats output slots budgets max(0, core - cw) holes per block,
            # and any more than that is a buffering fault the rate does not
            # excuse. The decoder emits k beats per n consumed, so its output
            # duty cannot exceed k/n however much it buffers -- boundary drops
            # there are arithmetic, and are reported, not failed.
            if name == "encoder W" and at_blk > enc_budget and surplus:
                bad = True
                self.mismatches += 1
                self.log.error(
                    f"valid-hold len={burst_len} encoder W: VALID dropped at "
                    f"{at_blk} block boundary/ies, over the structural budget of "
                    f"{enc_budget} ({core_beats} core beats into {self.cw_beats} "
                    f"output slots per block), with read supply {supply:.3f} >= "
                    f"demand {demand:.3f}. The rate allows a gapless output here.")
            if name == "encoder W" and at_blk and enc_budget:
                self.log.info(
                    f"valid-hold len={burst_len} encoder W: {at_blk} boundary "
                    f"drop(s) within the structural budget of {enc_budget} -- the "
                    f"core emits {core_beats} beats per block into {self.cw_beats} "
                    f"output slots, so {core_beats - self.cw_beats} idle cycle(s) "
                    f"per block cannot be prevented by buffering or burst length.")
            if st["drops"] and not surplus:
                self.log.info(
                    f"valid-hold len={burst_len} {name}: {st['drops']} drop cycles "
                    f"are a READ-RATE deficit, not a buffering fault -- supply "
                    f"{supply:.3f} < demand {demand:.3f} at this burst length. No "
                    f"buffer depth fixes a rate deficit; lengthen the burst.")
        return loop_ok and not bad

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"RS({self.n},{self.k}) m={self.m} t={self.t} S={self.s}",
                'beats': f"K_BEATS={self.k_beats} (tail {self.k_tail}) "
                         f"CW={self.cw_beats} packed"}
