# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gaxi_age_bfm
# Purpose: GAXI BFM wrappers for ports that carry an age beside the data
#          (gaxi_age_fifo_sync), plus the age-pool writer the N-bank wrapper
#          RTL would put in front of such a FIFO.
#
# Documentation: docs/markdown/rtl-amba/gaxi/gaxi_age_fifo_sync.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-25
"""Age-carrying GAXI BFM wrappers.

The framework's GAXIMaster / GAXISlave already drive and sample a multi-field
packet in multi-signal mode. These wrappers fix the two-field layout
(`data`, `data_age`) and the `wr_*` / `rd_*` signal map once, so a testbench
never repeats the binding, and give the age a first-class API:

- GaxiAgeMaster.send_aged / send_burst_aged take (data, age) pairs.
- GaxiAgeSlave.observed_aged returns (data, age) pairs as read.
- GaxiAgePoolDriver is the one-queue mirror of the N-bank wrapper: it drives
  age_dec (retire strobe and/or a Bernoulli strobe) and, when live, the
  writer rule from the spec, wr_data_age = youngest + 1, or youngest when
  age_dec is high, in place of the master's placeholder field.

The handshakes stay with the framework BFMs. The pool driver touches only
age_dec (a plain control input) and the age payload field, the way the
instantiating RTL's AND gate and adder would ([[bfm-usage]]).
"""
import os
import random

import cocotb
from cocotb.triggers import FallingEdge, Timer

from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave

# The BFMs drive on these offsets: GAXIMaster after the rising edge, GAXISlave
# AT the falling edge. The pool driver runs after both; a checker that reads
# pins samples after the pool driver.
POOL_DRIVE_NS = 2
CHECK_SAMPLE_NS = 3


def age_field_config(data_width: int, age_width: int) -> FieldConfig:
    """The two-field packet layout shared by both ports."""
    return FieldConfig.from_dict(
        field_dict={'data': {'bits': data_width, 'default': 0},
                    'data_age': {'bits': age_width, 'default': 0}},
        lsb_first=True)


class GaxiAgeMaster(GAXIMaster):
    """GAXIMaster bound to wr_valid/wr_ready/wr_data/wr_data_age."""

    def __init__(self, dut, clock, data_width, age_width, log,
                 prefix='wr_', title='write_master', timeout_cycles=2000):
        self.age_field_config = age_field_config(data_width, age_width)
        super().__init__(
            dut=dut, title=title, prefix='', clock=clock,
            field_config=self.age_field_config, timeout_cycles=timeout_cycles,
            mode='fifo_mux', bus_name='', pkt_prefix='', multi_sig=True,
            signal_map={'valid': f'{prefix}valid', 'ready': f'{prefix}ready',
                        'data': f'{prefix}data', 'data_age': f'{prefix}data_age'},
            log=log)

    def make_packet(self, data: int, age: int) -> GAXIPacket:
        pkt = GAXIPacket(self.age_field_config)
        pkt.data = data
        pkt.data_age = age
        return pkt

    async def send_aged(self, data: int, age: int):
        await self.send(self.make_packet(data, age))

    async def send_burst_aged(self, pairs):
        """Queue every (data, age) first so valid can stay up across beats."""
        await self.send_burst([self.make_packet(d, a) for d, a in pairs])


class GaxiAgeSlave(GAXISlave):
    """GAXISlave bound to rd_valid/rd_ready/rd_data/rd_data_age."""

    def __init__(self, dut, clock, data_width, age_width, log,
                 prefix='rd_', title='read_slave', timeout_cycles=2000):
        self.age_field_config = age_field_config(data_width, age_width)
        super().__init__(
            dut=dut, title=title, prefix='', clock=clock,
            field_config=self.age_field_config, timeout_cycles=timeout_cycles,
            mode='fifo_mux', bus_name='', pkt_prefix='', multi_sig=True,
            signal_map={'valid': f'{prefix}valid', 'ready': f'{prefix}ready',
                        'data': f'{prefix}data', 'data_age': f'{prefix}data_age'},
            log=log)

    def observed_aged(self):
        """(data, age) as read, in order. The age is the age AT the read."""
        return [(int(p.data), int(p.data_age)) for p in self.get_observed_packets()]


class GaxiAgePoolDriver:
    """One-queue mirror of the N-bank wrapper around gaxi_age_fifo_sync.

    Drives `age_dec` and, in live mode, `wr_data_age`, POOL_DRIVE_NS after the
    falling edge so it lands after both framework BFMs and before a checker
    sampling at CHECK_SAMPLE_NS.

    Policies, all settable between phases:
      decr_prob    Bernoulli age_dec strobe per cycle
      decr_on_read age_dec = rd_valid & rd_ready this cycle (the retire strobe)
      live_age     wr_data_age = 0 when the queue is empty (rd_valid low;
                   the one-queue pool is empty), else youngest + 1, or
                   youngest when age_dec is high and the writer has the dec
                   term, clamped at max
    POOL_WRITER_DEC_TERM=0 in the environment drops the dec term and
    POOL_WRITER_EMPTY_TERM=0 drops the empty term: those are the mutations the
    pool rank check must fail on (the second on the very first entry).
    """

    def __init__(self, dut, clock, age_width, log):
        self.dut = dut
        self.clock = clock
        self.log = log
        self.max_age = (1 << age_width) - 1
        self.decr_prob = 0.0
        self.decr_on_read = False
        self.live_age = False
        self.has_dec_term = os.environ.get('POOL_WRITER_DEC_TERM', '1') == '1'
        self.has_empty_term = os.environ.get('POOL_WRITER_EMPTY_TERM', '1') == '1'
        self._task = None
        dut.age_dec.value = 0

    def start(self):
        if self._task is None:
            self._task = cocotb.start_soon(self._run())

    def configure(self, decr_prob=0.0, decr_on_read=False, live_age=False):
        self.decr_prob = decr_prob
        self.decr_on_read = decr_on_read
        self.live_age = live_age

    def idle(self):
        self.configure()

    async def _run(self):
        dut = self.dut
        while True:
            await FallingEdge(self.clock)
            await Timer(POOL_DRIVE_NS, 'ns')
            strobe = random.random() < self.decr_prob
            if self.decr_on_read and int(dut.rd_valid.value) and int(dut.rd_ready.value):
                strobe = True
            dut.age_dec.value = 1 if strobe else 0
            if self.live_age:
                bump = 0 if (strobe and self.has_dec_term) else 1
                empty = self.has_empty_term and not int(dut.rd_valid.value)
                age = 0 if empty else int(dut.youngest.value) + bump
                dut.wr_data_age.value = min(age, self.max_age)
