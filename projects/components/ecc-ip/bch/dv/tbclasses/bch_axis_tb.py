"""
bch_encoder_axis4 / bch_decoder_axis4 testbench

Mirrors the RS AXIS4 wrapper TB (rs_axis_tb.py) for the binary BCH tops.
What the wrappers add over the bare handshake is tested here:

  keep mapping    byte-aligned codes carry per-bit keep on tstrb; non-byte-
                  aligned codes carry it on the low BITS_PER_BEAT bits of tuser.
  tlast placement the encoder emits a partial data-phase beat when K_BITS is
                  not a multiple of BITS_PER_BEAT, so keep (not beat count) is
                  the ground truth.
  sideband        tid and tdest are held across every beat of a block.
  backpressure    randomized valid/ready on both AXIS ends.
  verdict         decoder status is sampled at m_axis_tlast.

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import collections
import os
import random

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axis4.axis_factories import create_axis_master, create_axis_slave
from CocoTBFramework.components.shared.flex_config_gen import quick_config

from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel


class BCHAxisTB(TBBase):
    """Drives bch_encoder_axis4 or bch_decoder_axis4 over AXI4-Stream."""

    BLOCKS = {'gate': 4, 'func': 16, 'full': 48}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'bursty', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.role = os.environ.get('BCH_AXIS_ROLE', 'encoder')
        self.M = self.convert_to_int(os.environ.get('FIELD_DIM', '6'))
        self.PRIM = int(os.environ.get('PRIM_POLY', '0x43'), 0)
        self.T = self.convert_to_int(os.environ.get('T_BITS', '1'))
        self.N = self.convert_to_int(os.environ.get('N_BITS', '63'))
        self.FIRST_ROOT = self.convert_to_int(os.environ.get('FIRST_ROOT', '1'))
        self.B = self.convert_to_int(os.environ.get('BITS_PER_BEAT', '8'))
        self.idw = self.convert_to_int(os.environ.get('AXIS_ID_WIDTH', '4'))
        self.destw = self.convert_to_int(os.environ.get('AXIS_DEST_WIDTH', '2'))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, self.FIRST_ROOT)
        self.K = self.model.k()

        self.sw = self.B // 8
        self.full_keep = (1 << self.B) - 1
        self.byte_aligned = ((self.K % 8) == 0) and ((self.N % 8) == 0)
        # Byte-aligned profiles use tstrb and a 1-bit tuser; the others need
        # enough tuser bits to carry the per-bit keep.
        self.uw = self.convert_to_int(os.environ.get('AXIS_USER_WIDTH',
                                                      '1' if self.byte_aligned else str(self.B)))

        self.checks = 0
        self.mismatches = 0

        self._init_bfms()
        self.log.info(f"BCHAxisTB role={self.role} BCH({self.N},{self.K}) "
                      f"m={self.M} t={self.T} b={self.FIRST_ROOT} B={self.B} "
                      f"byte_aligned={self.byte_aligned} uw={self.uw}")

    def _init_bfms(self):
        # The BCH decoder is single-outstanding and can hold in_ready low for
        # many cycles while a block is processed; give the master a long timeout.
        timeout = 50 * self.N + 5000
        self.master = create_axis_master(
            self.dut, self.dut.aclk, prefix='s_axis_', data_width=self.B,
            id_width=self.idw, dest_width=self.destw, user_width=self.uw,
            timeout_cycles=timeout, log=self.log)['master']
        self.slave = create_axis_slave(
            self.dut, self.dut.aclk, prefix='m_axis_', data_width=self.B,
            id_width=self.idw, dest_width=self.destw, user_width=self.uw,
            log=self.log)['slave']
        self._rx = collections.deque()
        self.slave.add_callback(self._rx.append)
        self.slave.set_ready_always()

    # -- mandatory reset methods ------------------------------------------------
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

    # -- keep helpers ------------------------------------------------------------
    def strb_from_keep(self, keep):
        """tstrb[u] is high iff all eight keep bits in byte u are high."""
        strb = 0
        for u in range(self.sw):
            byte_keep = (keep >> (u * 8)) & 0xFF
            if byte_keep == 0xFF:
                strb |= 1 << u
        return strb

    def keep_from_strb(self, strb):
        """Expand each strobe bit to its eight keep bits."""
        keep = 0
        for u in range(self.sw):
            if (strb >> u) & 1:
                keep |= 0xFF << (u * 8)
        return keep & self.full_keep

    def keep_from_packet(self, p):
        if self.byte_aligned:
            return self.keep_from_strb(int(p.strb))
        return int(p.user) & self.full_keep

    def expected_keep(self, beat_idx):
        """Per-beat keep the wrapper should emit for a clean block."""
        full = self.full_keep
        if self.role == 'encoder':
            data_beats = (self.K + self.B - 1) // self.B
            parity_beats = ((self.N - self.K) + self.B - 1) // self.B
            if beat_idx < data_beats - 1:
                return full
            if beat_idx == data_beats - 1:
                rem = self.K % self.B
                return full if rem == 0 else (1 << rem) - 1
            p_idx = beat_idx - data_beats
            if p_idx < parity_beats - 1:
                return full
            rem = (self.N - self.K) % self.B
            return full if rem == 0 else (1 << rem) - 1
        else:
            out_beats = (self.K + self.B - 1) // self.B
            if beat_idx < out_beats - 1:
                return full
            rem = self.K % self.B
            return full if rem == 0 else (1 << rem) - 1

    def expected_beats(self):
        if self.role == 'encoder':
            return ((self.K + self.B - 1) // self.B
                    + ((self.N - self.K) + self.B - 1) // self.B)
        return (self.K + self.B - 1) // self.B

    # -- packing / unpacking -----------------------------------------------------
    def beats_of(self, bits):
        """Pack bits low-bit-first into (data, keep, strb, user, last) beats."""
        out = []
        n_chunks = (len(bits) + self.B - 1) // self.B
        for i in range(0, len(bits), self.B):
            chunk = bits[i:i + self.B]
            word = 0
            for u, b in enumerate(chunk):
                word |= b << u
            keep = (1 << len(chunk)) - 1
            last = (i // self.B) == (n_chunks - 1)
            strb = self.strb_from_keep(keep) if self.byte_aligned else self.full_strb()
            user = keep if not self.byte_aligned else 0
            out.append((word, keep, strb, user, last))
        return out

    def full_strb(self):
        return (1 << self.sw) - 1

    def bits_of(self, packets):
        """Unpack valid bits from received packets, honouring keep."""
        bits = []
        for p in packets:
            keep = self.keep_from_packet(p)
            data = int(p.data)
            for u in range(self.B):
                if (keep >> u) & 1:
                    bits.append((data >> u) & 1)
        return bits

    # -- stimulus / collection ---------------------------------------------------
    async def _send(self, bits, tid, tdest, wait=True):
        for word, keep, strb, user, last in self.beats_of(bits):
            pkt = self.master.create_packet(
                data=word, strb=strb, last=int(last), id=tid, dest=tdest, user=user)
            if wait:
                await self.master.send(pkt)
            else:
                await self.master._driver_send(pkt, sync=True)

    async def _collect(self, want_beats, timeout_cycles):
        got = []
        waited = 0
        while len(got) < want_beats and waited < timeout_cycles:
            if self._rx:
                got.append(self._rx.popleft())
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1
        return got

    def _status_at_last(self):
        return (int(self.dut.out_status_ok.value),
                int(self.dut.out_status_corrected.value),
                int(self.dut.out_status_uncorrectable.value),
                int(self.dut.out_status_frame_err.value))

    # -- scoring -----------------------------------------------------------------
    def _fail(self, msg):
        self.mismatches += 1
        self.log.error(msg)

    def _score(self, label, got, want_bits, tid, tdest):
        self.checks += 1
        want_beats = self.expected_beats()
        if len(got) != want_beats:
            self._fail(f"{label}: {len(got)} beats, expected {want_beats}")
            return

        # bit-exact payload
        got_bits = self.bits_of(got)
        if got_bits != want_bits:
            first = next((i for i, (a, b) in enumerate(zip(got_bits, want_bits)) if a != b),
                         min(len(got_bits), len(want_bits)))
            self._fail(f"{label}: bits differ from bit {first}: "
                       f"got {got_bits[first:first + 8]} want {want_bits[first:first + 8]}")

        # tlast exactly once, on the last beat
        lasts = [i for i, p in enumerate(got) if int(p.last)]
        if lasts != [len(got) - 1]:
            self._fail(f"{label}: tlast on beats {lasts}, expected only {len(got) - 1}")

        # tid / tdest held on every beat
        bad_id = [i for i, p in enumerate(got) if int(p.id) != tid]
        bad_dest = [i for i, p in enumerate(got) if int(p.dest) != tdest]
        if bad_id:
            self._fail(f"{label}: tid wrong on beats {bad_id[:4]} (want {tid})")
        if bad_dest:
            self._fail(f"{label}: tdest wrong on beats {bad_dest[:4]} (want {tdest})")

        # keep alignment and low-alignment
        for i, p in enumerate(got):
            keep = self.keep_from_packet(p)
            if keep & (keep + 1):
                self._fail(f"{label}: beat {i} keep 0x{keep:X} is not low-aligned")
            exp_keep = self.expected_keep(i)
            if keep != exp_keep:
                self._fail(f"{label}: beat {i} keep 0x{keep:X}, expected 0x{exp_keep:X}")
            if self.byte_aligned:
                exp_strb = self.strb_from_keep(keep)
                if int(p.strb) != exp_strb:
                    self._fail(f"{label}: beat {i} tstrb 0x{int(p.strb):X}, "
                               f"expected 0x{exp_strb:X}")
            else:
                if (int(p.user) & self.full_keep) != keep:
                    self._fail(f"{label}: beat {i} tuser keep mismatch")

    def _score_verdict(self, label, e):
        self.checks += 1
        ok, corr, unc, frame = self._status_at_last()
        if frame or unc:
            self._fail(f"{label}: verdict says frame={frame} unc={unc} for e={e} <= t")
            return
        if e == 0:
            if not ok or corr != 0:
                self._fail(f"{label}: e=0 should read ok=1 corrected=0, got ok={ok} "
                           f"corrected={corr}")
        else:
            if ok or corr != e:
                self._fail(f"{label}: e={e} should read ok=0 corrected={e}, got ok={ok} "
                           f"corrected={corr}")

    # -- scenarios ---------------------------------------------------------------
    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    async def run_stream(self, profile='backtoback'):
        self.set_profile(profile)
        seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        rnd = random.Random(seed + 0xA715 + (sum(map(ord, profile)) * 7919))
        blocks = self.BLOCKS[self.level]
        for b in range(blocks):
            msg = [rnd.randint(0, 1) for _ in range(self.K)]
            cw = self.model.encode(msg)
            tid = rnd.randrange(1 << self.idw) if self.idw else 0
            tdest = rnd.randrange(1 << self.destw) if self.destw else 0
            if self.role == 'encoder':
                await self._send(msg, tid, tdest)
                want = cw
                e = 0
            else:
                rx = list(cw)
                e = rnd.randint(0, self.T)
                for p in rnd.sample(range(self.N), e):
                    rx[p] ^= 1
                await self._send(rx, tid, tdest)
                want = msg
            got = await self._collect(self.expected_beats(),
                                      timeout_cycles=40 * self.N + 4000)
            self._score(f"{profile} block {b}", got, want, tid, tdest)
            if self.role == 'decoder':
                self._score_verdict(f"{profile} block {b}", e)
        return self.mismatches == 0

    async def run_backpressure(self):
        ok = True
        for profile in self.PROFILES[self.level]:
            if profile == 'backtoback':
                continue
            ok &= await self.run_stream(profile)
        return ok

    async def run_no_dead_cycles(self):
        self.set_profile('backtoback')
        seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        rnd = random.Random(seed + 0x51095)
        out_beats = self.expected_beats()
        took = {}
        for blocks in (4, 8):
            self._rx.clear()
            msgs = [[rnd.randint(0, 1) for _ in range(self.K)] for _ in range(blocks)]

            async def drive(msgs=msgs):
                for msg in msgs:
                    payload = msg if self.role == 'encoder' else self.model.encode(msg)
                    await self._send(payload, 0, 0, wait=False)

            cocotb.start_soon(drive())
            cycles, start = 0, None
            while len(self._rx) < blocks * out_beats:
                await RisingEdge(self.dut.aclk)
                cycles += 1
                if start is None and int(self.dut.s_axis_tvalid.value) \
                        and int(self.dut.s_axis_tready.value):
                    start = cycles
                if cycles > 40 * self.N * blocks + 4000:
                    break
            got = await self._collect(blocks * out_beats, timeout_cycles=200)
            for i, msg in enumerate(msgs):
                want = self.model.encode(msg) if self.role == 'encoder' else msg
                self._score(f"slope {blocks} blk {i}",
                            got[i * out_beats:(i + 1) * out_beats], want, 0, 0)
            took[blocks] = cycles - (start or 0)

        slope = (took[8] - took[4]) / 4.0
        rate = out_beats
        dead = slope - rate
        self.checks += 1
        self.log.info(f"no-dead-cycles ({self.role}): {took[4]} cycles for 4 blocks, "
                      f"{took[8]} for 8 -> slope {slope:.2f} cycles/block vs rate {rate} "
                      f"({dead:+.2f} dead per block)")
        if dead > 0.25:
            self.mismatches += 1
            self.log.error(f"{dead:.2f} dead cycles per block through the {self.role} wrapper")
        return self.mismatches == 0

    def get_test_report(self):
        return {'role': self.role, 'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"BCH({self.N},{self.K}) m={self.M} t={self.T} B={self.B}"}
