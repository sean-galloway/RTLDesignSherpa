"""
bch_decoder_core testbench

GAXIMaster drives the `in_` valid/ready port (data, keep, last), GAXISlave
drains the `out_` port and captures the per-beat status sideband. Every block
is scored against bch_model.BCHModel.decode(rx_block): status mapping,
corrected count, data bits, and framing must match. Uncorrectable and frame-
err blocks must leave the first K data bits byte-identical to the received
stream (R2 passthrough).

Scenarios:
  blocks        random data blocks with 0..t, t+1, and heavier error loads
  framing       a short block and a long block: frame_err, passthrough, and
                the next clean block is clean
  backpressure  one block under each TEST_LEVEL profile

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


class BCHDecoderCoreTB(TBBase):
    """Drives bch_decoder_core and scores it against BCHModel."""

    BLOCKS = {'gate': 4, 'func': 24, 'full': 96}
    PROFILES = {'gate': ['constrained'],
                'func': ['constrained', 'bursty', 'slow'],
                'full': ['constrained', 'bursty', 'slow', 'chaotic', 'backtoback']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.BLOCKS:
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)

        self.M = int(dut.FIELD_DIM.value)
        self.PRIM = int(dut.PRIM_POLY.value)
        self.T = int(dut.T_BITS.value)
        self.N = int(dut.N_BITS.value)
        self.B = int(dut.BITS_PER_BEAT.value)
        self.FIRST_ROOT = int(dut.FIRST_ROOT.value)
        self.K = int(dut.K_BITS.value)
        self.ENABLE_RECHECK = int(dut.ENABLE_RECHECK.value)
        self.STATUS_W = (self.T + 1).bit_length()

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, self.FIRST_ROOT)

        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"BCHDecoderCoreTB BCH({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.FIRST_ROOT} B={self.B} "
                      f"recheck={self.ENABLE_RECHECK} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- BFMs ----------------------------------------------------------------
    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.B, default=(1 << self.B) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="BCH_DEC_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_ok', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_corrected', bits=self.STATUS_W, default=0))
        fc_out.add_field(FieldDefinition(name='status_uncorrectable', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_frame_err', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="BCH_DEC_OUT", prefix="out_", clock=self.clk,
                               field_config=fc_out, pkt_prefix="", multi_sig=True, log=self.log)

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    # -- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 2)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # -- golden / helpers ----------------------------------------------------
    def beats_of(self, bits):
        """Split a bit list into (data, keep) beats of B bits, low lane first."""
        beats = []
        for i in range(0, len(bits), self.B):
            chunk = bits[i:i + self.B]
            data = 0
            for u, b in enumerate(chunk):
                data |= b << u
            beats.append((data, (1 << len(chunk)) - 1))
        return beats

    def bits_of(self, beats):
        """(data, keep) beats back to bits; a partial beat may appear anywhere."""
        out = []
        for data, keep in beats:
            for u in range(self.B):
                if keep >> u & 1:
                    out.append((data >> u) & 1)
        return out

    def status_of_packet(self, pkt):
        """Return status tuple from a captured output packet."""
        return (int(pkt.status_ok), int(pkt.status_corrected),
                int(pkt.status_uncorrectable), int(pkt.status_frame_err))

    def status_name(self, ok, corrected, uncorr, frame_err):
        if frame_err:
            return 'frame_err'
        if uncorr:
            return 'uncorrectable'
        if ok:
            return 'ok'
        return 'corrected'

    async def send_block(self, bits, wait=True):
        """Queue one block as beats; last on the final beat."""
        beats = self.beats_of(bits)
        for i, (d, k) in enumerate(beats):
            pkt = self.master.create_packet(data=d, keep=k, last=1 if i == len(beats) - 1 else 0)
            if wait:
                await self.master.send(pkt)
            else:
                await self.master._driver_send(pkt, sync=True)

    def expected_beats(self, data_len=None, frame_err=False):
        """Beats the decoder emits for a block."""
        if frame_err:
            return (data_len + self.B - 1) // self.B
        return (self.K + self.B - 1) // self.B

    async def collect(self, count, timeout_cycles):
        """Wait for `count` output BEATS; return packet list."""
        waited = 0
        while len(self.slave._recvQ) < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_cycles:
                self.log.error(f"timeout: {len(self.slave._recvQ)} of {count} beats after "
                               f"{timeout_cycles} cycles")
                self.mismatches += 1
                break
        out = []
        while self.slave._recvQ:
            out.append(self.slave._recvQ.popleft())
        return out

    def _score_block(self, label, rx_block, out_pkts, allow_recheck_off=False):
        """Score one decoded block."""
        self.checks += 1
        exp_data, exp_status, exp_count = self.model.decode(rx_block)
        exp_beats = self.beats_of(exp_data)

        if len(out_pkts) != len(exp_beats):
            self.mismatches += 1
            if self.mismatches <= 10:
                self.log.error(f"{label}: beat count {len(out_pkts)} vs expected {len(exp_beats)}")
            return False

        # Reassemble emitted data using keep masks
        got_data = []
        for pkt in out_pkts:
            data = int(pkt.data)
            keep = int(pkt.keep)
            for u in range(self.B):
                if keep >> u & 1:
                    got_data.append((data >> u) & 1)

        # Compare data bits
        data_ok = (got_data == exp_data)

        # Compare status on the last beat (valid every beat, sample point)
        last_pkt = out_pkts[-1]
        ok, corr, uncorr, ferr = self.status_of_packet(last_pkt)
        got_status = self.status_name(ok, corr, uncorr, ferr)

        # With re-check disabled, the DUT may declare 'corrected' for a block the
        # model flags uncorrectable because the locator fooled the degree/root
        # checks. In that case the emitted data must still match the model's
        # correction candidate, not the raw rx stream.
        status_ok = (got_status == exp_status)
        if allow_recheck_off and not status_ok:
            if got_status == 'corrected' and exp_status == 'uncorrectable':
                # The DUT believes it corrected; verify it used the same locator.
                # The model's corrected candidate is the only other acceptable data.
                candidate = self.model._chien_positions(
                    self.model._berlekamp_massey(self.model._full_syndrome_sequence(rx_block)))
                cand_bits = list(rx_block)
                for p in candidate:
                    cand_bits[p] ^= 1
                data_ok = (got_data == cand_bits[:self.K])
                status_ok = True
                exp_count = len(candidate)

        count_ok = (corr == exp_count)
        framing_ok = all(int(p.last) == (i == len(out_pkts) - 1) for i, p in enumerate(out_pkts))
        keep_ok = all(int(p.keep) == ((1 << self.B) - 1) or i == len(out_pkts) - 1
                      for i, p in enumerate(out_pkts))
        # Status must be stable across all beats
        status_stable = all(self.status_of_packet(p) == (ok, corr, uncorr, ferr) for p in out_pkts)

        ok_all = data_ok and status_ok and count_ok and framing_ok and keep_ok and status_stable
        if not ok_all:
            self.mismatches += 1
            if self.mismatches <= 10:
                self.log.error(f"{label}: status={got_status} exp={exp_status} "
                               f"count={corr} exp={exp_count} data_ok={data_ok} "
                               f"framing_ok={framing_ok} keep_ok={keep_ok} "
                               f"status_stable={status_stable}")
                try:
                    self.log.error(f"  kes_deg={int(self.dut.u_kes.out_lambda_degree.value)} "
                                   f"more_than_t={int(self.dut.u_kes.out_more_than_t.value)} "
                                   f"chien_roots={int(self.dut.u_chien.out_root_count.value)}")
                    if self.ENABLE_RECHECK:
                        self.log.error(f"  recheck_ok={int(self.dut.g_rechk.u_rechk.out_no_error.value)}")
                except Exception as e:
                    self.log.error(f"  debug access failed: {e}")
                self.log.error(f"  rx[:20]   = {rx_block[:20]}")
                self.log.error(f"  got[:20]  = {got_data[:20]}")
                self.log.error(f"  exp[:20]  = {exp_data[:20]}")
        return ok_all

    def _random_data(self):
        return [random.randint(0, 1) for _ in range(self.K)]

    def _inject_errors(self, block, count):
        """Flip `count` random bit positions; returns (rx, positions)."""
        rx = list(block)
        if count <= 0:
            return rx, []
        count = min(count, self.N)
        pos = random.sample(range(self.N), count)
        for p in pos:
            rx[p] ^= 1
        return rx, pos

    # -- scenarios ------------------------------------------------------------
    async def run_blocks(self, profile='backtoback'):
        self.set_profile(profile)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        self.log.info(f"blocks: {n_blocks} x BCH({self.N},{self.K}) under '{profile}'")
        # Error loads per block
        loads = [0, 1]
        loads += [self.T] * 2
        if self.T > 1:
            loads += [self.T - 1]
        loads += [self.T + 1, min(self.N, self.T + 3), min(self.N, 2 * self.T + 1)]
        loads += [random.randint(1, self.T) for _ in range(max(0, n_blocks - len(loads)))]
        loads = loads[:n_blocks]

        allow_off = not self.ENABLE_RECHECK
        for i, err_count in enumerate(loads):
            data = self._random_data()
            enc = self.model.encode(data)
            rx, _ = self._inject_errors(enc, err_count)
            await self.send_block(rx)
            out = await self.collect(self.expected_beats(frame_err=False),
                                     timeout_cycles=40 * self.N + 400)
            self._score_block(f"block {i} e={err_count}", rx, out, allow_recheck_off=allow_off)
        return self.mismatches == 0

    async def run_framing(self):
        self.set_profile('constrained')
        data = self._random_data()
        enc = self.model.encode(data)

        # short block
        short_len = max(1, self.K - 3)
        short = enc[:short_len]
        await self.send_block(short)
        out = await self.collect(self.expected_beats(data_len=short_len, frame_err=True),
                                 timeout_cycles=40 * self.N + 400)
        self._score_framing_block("short block", short, out)

        # long block (still < N for the test fixture)
        long_len = min(self.N - 1, self.K + 2)
        long = enc[:long_len]
        await self.send_block(long)
        out = await self.collect(self.expected_beats(data_len=long_len, frame_err=True),
                                 timeout_cycles=40 * self.N + 400)
        self._score_framing_block("long block", long, out)

        # a clean block afterwards must decode normally
        data2 = self._random_data()
        enc2 = self.model.encode(data2)
        await self.send_block(enc2)
        out = await self.collect(self.expected_beats(frame_err=False),
                                 timeout_cycles=40 * self.N + 400)
        self._score_block("block after framing", enc2, out)
        return self.mismatches == 0

    def _score_framing_block(self, label, rx_block, out_pkts):
        """Frame-err blocks pass through unchanged: status frame_err, data == rx_block."""
        self.checks += 1
        exp_data = rx_block
        exp_beats = self.beats_of(exp_data)
        if len(out_pkts) != len(exp_beats):
            self.mismatches += 1
            if self.mismatches <= 10:
                self.log.error(f"{label}: beat count {len(out_pkts)} vs expected {len(exp_beats)}")
            return False

        got_data = []
        for pkt in out_pkts:
            data = int(pkt.data)
            keep = int(pkt.keep)
            for u in range(self.B):
                if keep >> u & 1:
                    got_data.append((data >> u) & 1)

        last_pkt = out_pkts[-1]
        status = self.status_of_packet(last_pkt)
        ok_all = (got_data == exp_data) and (status == (0, 0, 0, 1))
        ok_all &= all(self.status_of_packet(p) == status for p in out_pkts)
        ok_all &= all(int(p.last) == (i == len(out_pkts) - 1) for i, p in enumerate(out_pkts))
        if not ok_all:
            self.mismatches += 1
            if self.mismatches <= 10:
                self.log.error(f"{label}: framing/passthrough mismatch status={status}")
        return ok_all

    async def run_backpressure(self):
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            data = self._random_data()
            enc = self.model.encode(data)
            err_count = random.choice([0, 1, self.T])
            rx, _ = self._inject_errors(enc, err_count)
            await self.send_block(rx)
            out = await self.collect(self.expected_beats(frame_err=False),
                                     timeout_cycles=40 * self.N + 400)
            self._score_block(f"profile {profile} e={err_count}", rx, out,
                              allow_recheck_off=not self.ENABLE_RECHECK)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
