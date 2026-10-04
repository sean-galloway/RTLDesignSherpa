"""
bch_encoder_axi4 / bch_decoder_axi4 testbench (full memory-to-memory loop)

messages -> M1 -> encode -> M2 -> decode -> M3 -> messages, with three real
sdpram memories in the chain. The golden reference is bch_model.BCHModel.

Author: RTL Design Sherpa
Created: 2026-10-03
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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel


class BCHAxi4LoopTB(TBBase):
    """Runs the seed / encode / decode / drain chain and checks the round trip."""

    BLOCKS = {'gate': 2, 'func': 6, 'full': 16}
    LENS = {'gate': [16], 'func': [1, 16], 'full': [1, 7, 16, 64]}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.m = self.convert_to_int(os.environ.get('FIELD_DIM', 6))
        self.prim = int(os.environ.get('PRIM_POLY', '0x43'), 0)
        self.t = self.convert_to_int(os.environ.get('T_BITS', 1))
        self.n = self.convert_to_int(os.environ.get('N_BITS', 63))
        self.b = self.convert_to_int(os.environ.get('FIRST_ROOT', 1))
        self.dw = self.convert_to_int(os.environ.get('DATA_WIDTH', 8))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.model = BCHModel(self.m, self.prim, self.t, self.n, self.b)
        self.k = self.model.k()
        self.deg_g = self.model.degree_g()

        self.bpb = self.dw  # bits per beat = DATA_WIDTH for the BCH tops
        self.k_beats = -(-self.k // self.bpb)
        self.k_tail = self.k % self.bpb
        self.cw_beats = -(-self.n // self.bpb)
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
        for _ in range(64):
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

    def beats_of(self, bits):
        """Split a bit list into (data, keep) beats of B bits, low lane first."""
        beats = []
        for i in range(0, len(bits), self.bpb):
            chunk = bits[i:i + self.bpb]
            data = 0
            for u, b in enumerate(chunk):
                data |= b << u
            beats.append((data, (1 << len(chunk)) - 1))
        return beats

    def bits_of(self, beats):
        """(data, keep) beats back to bits; a partial beat may appear anywhere."""
        out = []
        for data, keep in beats:
            for u in range(self.bpb):
                if keep >> u & 1:
                    out.append((data >> u) & 1)
        return out

    async def run_loop(self, blocks, burst_len, profile='backtoback'):
        self.checks += 1
        self.set_profile(profile)
        self.slave._recvQ.clear()
        rnd = random.Random(0xC0DE + blocks * 977 + burst_len)
        msg_beats = blocks * self.k_beats

        msgs = [[rnd.randint(0, 1) for _ in range(self.k)] for _ in range(blocks)]
        words = []
        for bits in msgs:
            words.extend([d for d, _ in self.beats_of(bits)])
        label = f"blocks={blocks} len={burst_len} {profile}"
        budget = 400 * blocks * self.cw_beats + 20000

        self.dut.blocks.value = blocks
        self.dut.burst_len.value = burst_len

        # seed M1 with the messages
        self.dut.seed_beats.value = msg_beats
        await self._pulse(self.dut.seed_start)
        for i, w in enumerate(words):
            await self.master.send(self.master.create_packet(
                data=w, last=int((i + 1) % self.k_beats == 0)))
        if not await self._await_done(self.dut.seed_done, f"{label} seed", budget):
            return

        # encode M1 -> M2
        await self._pulse(self.dut.enc_start)
        if not await self._await_done(self.dut.enc_done, f"{label} encode", budget):
            return
        if int(self.dut.enc_resp_err.value):
            self._fail(f"{label}: encoder resp_err")
        if int(self.dut.enc_frame_err.value):
            self._fail(f"{label}: encoder frame_err -- a block was not k bits")

        # decode M2 -> M3
        trace = cocotb.start_soon(self._trace_dec())
        await self._pulse(self.dut.dec_start)
        if not await self._await_done(self.dut.dec_done, f"{label} decode", budget):
            trace.kill()
            d = self.dut.u_dec
            self.log.info(f"DEBUG: rd_v={int(d.u_rd.out_valid.value)} rd_r={int(d.u_rd.out_ready.value)} rd_last={int(d.u_rd.out_last.value)} rd_data=0x{int(d.u_rd.out_data.value):02x} rd_block={int(d.u_rd.r_in_block.value)} rd_blen={int(d.u_rd.w_block_len.value)}")
            self.log.info(f"DEBUG: core_in_v={int(d.u_core.in_valid.value)} core_in_r={int(d.u_core.in_ready.value)} core_in_last={int(d.u_core.in_last.value)} core_state={int(d.u_core.r_state.value)} block_end={int(d.u_core.r_block_ending.value)}")
            self.log.info(f"DEBUG: core ibeat={int(d.r_ibeat.value)} in_keep=0x{int(d.w_in_keep.value):02x} rx_bit={int(d.u_core.r_rx_bit_count.value)} beat={int(d.u_core.r_rx_beat_count.value)} frame={int(d.u_core.r_frame_err.value)} flush={int(d.u_core.r_synd_flush.value)}")
            self.log.info(f"DEBUG: synd_v={int(d.u_core.w_synd_out_valid.value)} synd_r={int(d.u_core.w_synd_out_ready.value)} synd_noerr={int(d.u_core.w_synd_out_no_error.value)}")
            self.log.info(f"DEBUG: core_out_v={int(d.u_core.out_valid.value)} core_out_r={int(d.u_core.out_ready.value)} core_out_last={int(d.u_core.out_last.value)} rel_idx={int(d.u_core.r_release_idx.value)} rel_beats={int(d.u_core.r_release_beats.value)}")
            self.log.info(f"DEBUG: wr_in_v={int(d.u_wr.in_valid.value)} wr_in_r={int(d.u_wr.in_ready.value)} wr_left={int(d.u_wr.r_w_left.value)}")
            return
        if int(self.dut.dec_resp_err.value):
            self._fail(f"{label}: decoder resp_err")

        ok = int(self.dut.dec_blocks_ok.value)
        corr = int(self.dut.dec_blocks_corrected.value)
        unc = int(self.dut.dec_blocks_uncorrectable.value)
        fr = int(self.dut.dec_blocks_frame_err.value)
        if (ok, corr, unc, fr) != (blocks, 0, 0, 0):
            self._fail(f"{label}: verdicts ok/corr/unc/frame = {ok}/{corr}/{unc}/{fr}, "
                       f"expected {blocks}/0/0/0 on an error-free loop")

        # drain M3 and compare
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

        got_msgs = []
        for b in range(blocks):
            bits = []
            for i in range(self.k_beats):
                w = got[b * self.k_beats + i]
                take = self.bpb if (i < self.k_beats - 1 or self.k_tail == 0) else self.k_tail
                for j in range(take):
                    bits.append((w >> j) & 1)
            got_msgs.append(bits)

        if got_msgs != msgs:
            bad = [b for b in range(blocks) if got_msgs[b] != msgs[b]]
            b = bad[0]
            diffs = [i for i, (a, c) in enumerate(zip(got_msgs[b], msgs[b])) if a != c]
            shift = None
            g, w = got_msgs[b], msgs[b]
            for off in range(1, min(len(w), 2 * self.bpb + 4)):
                if g[off:] == w[:len(g) - off]:
                    shift = off
                    break
                if w[off:] == g[:len(w) - off]:
                    shift = -off
                    break
            self._fail(
                f"{label}: {len(bad)} of {blocks} blocks differ; block {b} has "
                f"{len(diffs)} of {self.k} bits wrong, first at {diffs[0]}; "
                + (f"the bits are SHIFTED by {shift}" if shift is not None
                   else "no shift explains it, so the data itself is wrong"))

    async def _trace_dec(self):
        d = self.dut.u_dec
        n = 0
        while n < 200:
            await RisingEdge(self.dut.aclk)
            rd_fire = int(d.u_rd.out_valid.value) and int(d.u_rd.out_ready.value)
            wr_fire = int(d.u_core.out_valid.value) and int(d.u_core.out_ready.value)
            if rd_fire or wr_fire:
                self.log.info(
                    f"TRACE{n}: rd_fire={int(rd_fire)} last={int(d.u_rd.out_last.value)} "
                    f"ibeat={int(d.r_ibeat.value)} keep=0x{int(d.w_in_keep.value):02x} "
                    f"st={int(d.u_core.r_state.value)} rx_b={int(d.u_core.r_rx_beat_count.value)} "
                    f"rx_bit={int(d.u_core.r_rx_bit_count.value)} "
                    f"synd_v={int(d.u_core.w_synd_out_valid.value)} synd_r={int(d.u_core.w_synd_out_ready.value)} "
                    f"synd_bit={int(d.u_core.u_synd.r_bit_count.value)} "
                    f"wr_fire={int(wr_fire)} rel={int(d.u_core.r_release_idx.value)}/{int(d.u_core.r_release_beats.value)}")
                n += 1

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
        before = self.mismatches
        await self.run_loop(blocks, burst_len, profile='backtoback')
        loop_ok = (self.mismatches == before)
        for t in tasks:
            t.kill()

        supply = burst_len / float(burst_len + 2)
        demand = self.k_beats / float(self.cw_beats)
        surplus = supply >= demand

        p_beats = -(-self.deg_g // self.bpb)
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

            if inside and surplus:
                bad = True
                self.mismatches += 1
                self.log.error(
                    f"valid-hold len={burst_len} {name}: VALID dropped INSIDE a block "
                    f"({inside} time(s)) with read supply {supply:.3f} >= demand "
                    f"{demand:.3f}.")

            if name == "encoder W" and at_blk > enc_budget and surplus:
                bad = True
                self.mismatches += 1
                self.log.error(
                    f"valid-hold len={burst_len} encoder W: VALID dropped at "
                    f"{at_blk} block boundary/ies, over the structural budget of "
                    f"{enc_budget}.")
        return loop_ok and not bad

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"BCH({self.n},{self.k}) m={self.m} t={self.t} B={self.bpb}",
                'beats': f"K_BEATS={self.k_beats} (tail {self.k_tail}) "
                         f"CW={self.cw_beats} packed"}
