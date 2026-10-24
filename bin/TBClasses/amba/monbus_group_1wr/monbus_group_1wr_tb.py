# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: monbus_group_1wr_tb
# Purpose: Testbench for the single-write-port monbus group: the bare
#          monbus_group_core_1wr and its protocol wrappers
#          (monbus_axil4_group_1wr, monbus_axi4_group_1wr).
#
# Author: sean galloway
# Created: 2026-10-23

"""
One bench for the 1wr family. The DUT writes everything it accepts to
memory over ONE master-write port: error-selected packets into the error
window as raw 3-beat records, everything else into the trace window. The
bench:

  - drives the MonBus ingress with a framework GAXI master in multi-signal
    mode, so the 128-bit packet AND the 64-bit source timestamp ride the
    same valid/ready handshake (the family TBs only sniff the timestamp;
    this bench checks that it lands)
  - acts as the write slave with MonbusGroupHarness's multi-outstanding
    in-order consumer, throttled by a FlexRandomizer
  - attributes every landed beat to a window by its burst's AW address
    (per-beat addresses come from trace_bursts, see the handbook row)
  - decodes each window with the shared parse_stream() and compares the
    decoded records, in order, with the packets and timestamps sent
  - counts irq_out pulses and checks them, and err_rec_count, against the
    number of error RECORDS sent (not bursts)

Three TEST_TYPEs (one per pytest cell): errors_only, trace_only, mixed.
TEST_LEVEL (gate/func/full) sets the record count, the ingress delay
profile and the slave's ready distribution.

The write-port shape is a constructor argument: the runner for the bare
core passes ("axi4", "fub_m_"), the AXIL wrapper ("axil", "m_axil_"), the
AXI4 wrapper ("axi4", "m_axi_"). Nothing else differs.
"""

import os
import random
from typing import Dict, List, Tuple

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase
from TBClasses.scoreboards.monbus_group import MonbusGroupHarness, BeatLayout, BeatOrder
from TBClasses.monbus import (
    create_monitor_packet, parse, parse_stream,
    PktType, ProtocolType, AXIErrorCode,
)
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


BEATS_PER_RECORD = 3
BYTES_PER_BEAT   = 8
STRIDE_BYTES     = BEATS_PER_RECORD * BYTES_PER_BEAT
TS_MASK          = (1 << 60) - 1          # beat 0 carries source_ts[59:0] under a 4-bit tag

ERR_BASE,   ERR_LIMIT   = 0x0000_1000, 0x0000_1FFF   # 4 KB: 170 records
TRACE_BASE, TRACE_LIMIT = 0x0000_4000, 0x0000_7FFF   # 16 KB

# Per level: how many records, the ingress valid_delay profile (FlexConfigGen
# name) and the slave's per-cycle ready as (stall weight, ready weight).
LEVELS = {
    'gate': dict(n_records=16,  ingress='fast',        ready_w=(3, 7)),
    'func': dict(n_records=48,  ingress='constrained', ready_w=(1, 1)),
    'full': dict(n_records=150, ingress='bursty',      ready_w=(13, 7)),
}

TEST_TYPES = ('errors_only', 'trace_only', 'mixed')


def monbus_ingress_field_config() -> FieldConfig:
    """Packet and source timestamp as two fields on one handshake. In
    multi-signal mode each field maps to its own DUT signal."""
    cfg = FieldConfig()
    cfg.add_field(FieldDefinition(name="packet",    bits=128, format="hex"))
    cfg.add_field(FieldDefinition(name="timestamp", bits=64,  format="hex"))
    return cfg


class MonbusGroup1wrTB(TBBase):

    def __init__(self, dut, *, trace_proto: str, trace_prefix: str):
        super().__init__(dut)
        self.trace_proto  = trace_proto
        self.trace_prefix = trace_prefix
        self.level     = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.test_type = os.environ.get('TEST_TYPE', 'mixed')
        assert self.level in LEVELS, f"TEST_LEVEL {self.level!r} not in {sorted(LEVELS)}"
        assert self.test_type in TEST_TYPES, f"TEST_TYPE {self.test_type!r} not in {TEST_TYPES}"
        self.cfg = LEVELS[self.level]
        self.SEED = int(os.environ.get('SEED', '0'))
        self.rng = random.Random(self.SEED)

        self.axi_aclk    = dut.axi_aclk
        self.axi_aresetn = dut.axi_aresetn

        # Write slave + capture. The ctor only stores handles.
        self.mon = MonbusGroupHarness(
            dut, self.axi_aclk,
            drain_proto="axi4", drain_prefix="unused_",     # no drain port in this family
            trace_proto=trace_proto, trace_prefix=trace_prefix,
            group_node=dut, irq_sig=dut.irq_out, log=self.log,
            layout_trace=BeatLayout(order=BeatOrder.TS_HI_LO),
        )
        self.monbus_master = None
        self.irq_pulses = 0
        self._irq_task = None

    # ------------------------------------------------------------------
    # MANDATORY: clock and reset
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self):
        self.tie_off()
        await self.start_clock('axi_aclk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('axi_aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('axi_aclk', 5)

    async def assert_reset(self):
        self.axi_aresetn.value = 0

    async def deassert_reset(self):
        self.axi_aresetn.value = 1

    # ------------------------------------------------------------------
    # configuration
    # ------------------------------------------------------------------

    def tie_off(self, *, err_watermark: int = BEATS_PER_RECORD,
                trace_watermark: int = BEATS_PER_RECORD):
        d = self.dut
        d.cam_clear.value       = 0
        d.cfg_compress_en.value = 0
        d.cfg_base_addr.value           = TRACE_BASE
        d.cfg_limit_addr.value          = TRACE_LIMIT
        d.cfg_flush_watermark.value     = trace_watermark
        d.cfg_err_base_addr.value       = ERR_BASE
        d.cfg_err_limit_addr.value      = ERR_LIMIT
        d.cfg_err_flush_watermark.value = err_watermark
        for sig in (
            'cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask',
            'cfg_axi_timeout_mask', 'cfg_axi_compl_mask', 'cfg_axi_thresh_mask',
            'cfg_axi_perf_mask', 'cfg_axi_addr_mask', 'cfg_axi_debug_mask',
            'cfg_axis_pkt_mask', 'cfg_axis_err_select', 'cfg_axis_error_mask',
            'cfg_axis_timeout_mask', 'cfg_axis_compl_mask', 'cfg_axis_credit_mask',
            'cfg_axis_channel_mask', 'cfg_axis_stream_mask',
            'cfg_core_pkt_mask', 'cfg_core_err_select', 'cfg_core_error_mask',
            'cfg_core_timeout_mask', 'cfg_core_compl_mask', 'cfg_core_thresh_mask',
            'cfg_core_perf_mask', 'cfg_core_debug_mask',
        ):
            getattr(d, sig).value = 0
        # Error-type packets go to the error window; everything else is trace.
        d.cfg_axi_err_select.value = 1 << int(PktType.PktTypeError)

    async def setup_interfaces(self):
        """Ingress master and the slave's timing, both from the level profile."""
        self.monbus_master = create_gaxi_master(
            dut=self.dut, title="MonBus 1wr ingress", prefix="monbus",
            clock=self.axi_aclk, field_config=monbus_ingress_field_config(),
            multi_sig=True,
            signal_map={'valid': 'monbus_valid', 'ready': 'monbus_ready',
                        'packet': 'monbus_packet', 'timestamp': 'monbus_timestamp'},
            log=self.log,
        )
        profile = self.cfg['ingress']
        self.monbus_master.set_randomizer(
            FlexConfigGen(profiles=[profile], fields=['valid_delay']).build()[profile])
        stall_w, ready_w = self.cfg['ready_w']
        self.mon.set_trace_ready_randomizer(
            FlexRandomizer({'ready': ([(0, 0), (1, 1)], [stall_w, ready_w])}))
        self.start_irq_counter()
        self.log.info(f"ingress profile {profile}, slave ready weights stall:ready = "
                      f"{stall_w}:{ready_w}, write port {self.trace_proto} at {self.trace_prefix}*")

    # ------------------------------------------------------------------
    # irq_out pulse counter (an observer: a 1-cycle pulse per error record)
    # ------------------------------------------------------------------

    def start_irq_counter(self):
        self.irq_pulses = 0
        self._irq_task = cocotb.start_soon(self._irq_counter())

    def stop_irq_counter(self):
        if self._irq_task is not None:
            self._irq_task.cancel()
            self._irq_task = None

    async def _irq_counter(self):
        while True:
            await ReadOnly()
            if int(self.dut.irq_out.value) == 1:
                self.irq_pulses += 1
            await RisingEdge(self.axi_aclk)

    # ------------------------------------------------------------------
    # stimulus
    # ------------------------------------------------------------------

    def make_record(self, is_err: bool, i: int) -> Tuple[int, int, bool]:
        """(packet, source_ts, is_err). Error-type packets select the error
        path through cfg_axi_err_select; completions take the trace path."""
        if is_err:
            pkt = create_monitor_packet(
                PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
                AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, i % 8, 0x21,
                self.rng.randint(0, 0xFFFF_FFFF_FFFF_FFFF))
        else:
            pkt = create_monitor_packet(
                PktType.PktTypeCompletion, ProtocolType.PROTOCOL_AXI,
                0, 0, i % 8, 0x22, self.rng.randint(0, 0xFFFF_FFFF_FFFF_FFFF))
        return pkt, self.rng.randint(0, TS_MASK), is_err

    def make_stream(self) -> List[Tuple[int, int, bool]]:
        n = self.cfg['n_records']
        if self.test_type == 'errors_only':
            return [self.make_record(True, i) for i in range(n)]
        if self.test_type == 'trace_only':
            return [self.make_record(False, i) for i in range(n)]
        recs = [self.make_record(self.rng.random() < 0.3, i) for i in range(n)]
        recs[0] = self.make_record(True, 0)        # at least one of each
        recs[1] = self.make_record(False, 1)
        return recs

    async def send_records(self, records):
        """Queue the whole stream on the master; the profile gaps the beats."""
        pkts = [self.monbus_master.create_packet(packet=p, timestamp=ts)
                for p, ts, _ in records]
        await self.monbus_master.send_burst(pkts)

    async def capture(self, n_beats: int, *, drain_cycles: int):
        self.mon.start_trace_consumer()
        waited = 0
        while len(self.mon.trace_beats) < n_beats and waited < drain_cycles:
            await self.wait_clocks('axi_aclk', 10)
            waited += 10
        # let the last bursts' B return (irq pulses ride on B)
        await self.wait_clocks('axi_aclk', 40)
        self.mon.stop_trace_consumer()
        await self.wait_clocks('axi_aclk', 2)

    # ------------------------------------------------------------------
    # checks
    # ------------------------------------------------------------------

    @staticmethod
    def window_of(addr: int) -> str:
        if ERR_BASE <= addr <= ERR_LIMIT:
            return 'err'
        if TRACE_BASE <= addr <= TRACE_LIMIT:
            return 'trc'
        return 'none'

    def split_by_window(self) -> Dict[str, List[Tuple[int, int]]]:
        """Per-beat (addr, data) by window, rebuilt from the completed bursts
        (INCR, 8 bytes per beat). B comes back in AW order, so completion
        order is AW order."""
        bursts = self.mon.trace_bursts
        n_in_bursts = sum(len(b['beats']) for b in bursts)
        assert n_in_bursts == len(self.mon.trace_beats), (
            f"{len(self.mon.trace_beats)} beats captured but only {n_in_bursts} "
            f"are in acknowledged bursts (a B never came back)")
        out: Dict[str, List[Tuple[int, int]]] = {'err': [], 'trc': []}
        for b in bursts:
            assert len(b['beats']) == b['awlen'] + 1, (
                f"burst at 0x{b['addr']:08x}: {len(b['beats'])} beats for awlen {b['awlen']}")
            assert b['wlast_flags'][-1] == 1 and not any(b['wlast_flags'][:-1]), (
                f"burst at 0x{b['addr']:08x}: wlast flags {b['wlast_flags']}")
            w = self.window_of(b['addr'])
            assert w != 'none', f"burst at 0x{b['addr']:08x} is outside both windows"
            for i, data in enumerate(b['beats']):
                out[w].append((b['addr'] + i * BYTES_PER_BEAT, data))
        return out

    @staticmethod
    def check_sequential(beats, base: int, limit: int, name: str):
        """Addresses step by 8 within the window and wrap to base past the
        last whole record (the writer never splits a record across the wrap)."""
        window_recs = ((limit + 1 - base) // BYTES_PER_BEAT) // BEATS_PER_RECORD
        for i, (addr, _) in enumerate(beats):
            rec, slot = divmod(i, BEATS_PER_RECORD)
            expected = base + ((rec % window_recs) * BEATS_PER_RECORD + slot) * BYTES_PER_BEAT
            assert addr == expected, (
                f"{name} beat {i}: addr 0x{addr:08x}, expected 0x{expected:08x}")

    def check_window(self, name: str, beats, sent, base: int, limit: int):
        """Decode the window with the shared parse_stream() (24-byte raw
        records, source timestamp first) and compare with what was sent."""
        self.check_sequential(beats, base, limit, name)
        assert len(beats) % BEATS_PER_RECORD == 0, (
            f"{name}: {len(beats)} beats is not a whole number of records")
        got = list(parse_stream((d for _, d in beats), stride_bytes=STRIDE_BYTES, ts_mode=1))
        # parse_stream drops a record with a non-raw tag or an all-zero body,
        # so a short count here means a malformed record, not a lost one.
        assert len(got) == len(beats) // BEATS_PER_RECORD, (
            f"{name}: {len(beats) // BEATS_PER_RECORD} records landed but only "
            f"{len(got)} decoded (bad tag or zero body)")
        exp = [(parse(p), ts & TS_MASK) for p, ts, _ in sent]
        assert len(got) == len(exp), f"{name}: {len(got)} records landed, {len(exp)} sent"
        for i, (g, (e_pkt, e_ts)) in enumerate(zip(got, exp)):
            assert g.packet == e_pkt, (
                f"{name} record {i}: got {g.packet}, expected {e_pkt}")
            assert g.source_ts == e_ts, (
                f"{name} record {i}: source_ts 0x{g.source_ts:x}, expected 0x{e_ts:x}")

    def error_bursts_completed(self) -> int:
        return sum(1 for b in self.mon.trace_bursts if self.window_of(b['addr']) == 'err')

    def check_irq(self, n_err_records: int):
        """One irq pulse and one err_rec_count step per whole error record
        landed, regardless of how the writer cut the records into bursts."""
        count = int(self.dut.err_rec_count.value)
        assert self.irq_pulses == n_err_records, (
            f"{self.irq_pulses} irq pulses, {n_err_records} error records sent "
            f"({self.error_bursts_completed()} error bursts acknowledged)")
        assert count == n_err_records, (
            f"err_rec_count {count}, {n_err_records} error records sent")

    # ------------------------------------------------------------------
    # the test
    # ------------------------------------------------------------------

    async def run(self):
        """Drive the TEST_TYPE stream, capture both windows, check everything."""
        sent = self.make_stream()
        n_err = sum(1 for r in sent if r[2])
        self.log.info(f"=== {self.test_type} level={self.level} seed={self.SEED}: "
                      f"{n_err} error + {len(sent) - n_err} trace records ===")
        cap = cocotb.start_soon(self.capture(len(sent) * BEATS_PER_RECORD,
                                             drain_cycles=400 * len(sent)))
        await self.send_records(sent)
        await cap
        by = self.split_by_window()
        self.check_window('err', by['err'], [r for r in sent if r[2]], ERR_BASE, ERR_LIMIT)
        self.check_window('trc', by['trc'], [r for r in sent if not r[2]], TRACE_BASE, TRACE_LIMIT)
        self.check_irq(n_err)
        self.stop_irq_counter()
        self.log.info(f"{self.test_type}: {len(sent)} records in {len(self.mon.trace_bursts)} bursts "
                      f"({self.error_bursts_completed()} error), {self.irq_pulses} irq pulses, "
                      f"{self.mon.stats.trace_backpressure_cycles} slave stall cycles -- OK")
