# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Unit tests for read_bus_meters.py. The decode path is pure -- packed CSR
# 32-bit words go in, BucketCounts / ChannelBuckets / MeterSnapshot come out.
# Tests use a CannedReader to play back exact 32-bit values matching what
# harness_csr would return for known meter state.

import io
import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

# Set REPO_ROOT in case descriptor_builder needs it for shared imports.
_repo_root = HERE.parents[4]
os.environ.setdefault("REPO_ROOT", str(_repo_root))

from read_bus_meters import (  # noqa: E402
    OFF_AGG_PRODUCTIVE, OFF_AGG_BACKPRESSURE, OFF_AGG_STARVATION,
    OFF_AGG_IDLE, OFF_CH_OVERFLOW,
    OFF_CH_PROD_BP_BASE, OFF_CH_STARV_IDLE_BASE,
    R_METER_BASE, W_METER_BASE,
    read_meter, read_bus_meters,
    format_meter, format_snapshot,
    BucketCounts, ChannelBuckets, MeterSnapshot,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

class CannedReader:
    """Map (address) -> 32-bit value. Reads not in the map return 0."""

    def __init__(self, values: dict):
        self.values = dict(values)
        self.read_log = []

    def read(self, addr: int) -> int:
        self.read_log.append(addr)
        return self.values.get(addr, 0)


def _meter_values(base: int, *, agg_prod, agg_bp, agg_starv, agg_idle,
                  per_ch_prod, per_ch_bp, per_ch_starv, per_ch_idle,
                  per_ch_overflow):
    """Build the dict of (addr -> word) the bridge would return for one
    meter pre-loaded with the given counter state."""
    out = {
        base + OFF_AGG_PRODUCTIVE:   agg_prod   & 0xFFFF_FFFF,
        base + OFF_AGG_BACKPRESSURE: agg_bp     & 0xFFFF_FFFF,
        base + OFF_AGG_STARVATION:   agg_starv  & 0xFFFF_FFFF,
        base + OFF_AGG_IDLE:         agg_idle   & 0xFFFF_FFFF,
    }
    ov_word = 0
    for ch, ov in enumerate(per_ch_overflow):
        ov_word |= (ov & 0xF) << (4 * ch)
    out[base + OFF_CH_OVERFLOW] = ov_word & 0xFFFF_FFFF
    for ch, (p, b) in enumerate(zip(per_ch_prod, per_ch_bp)):
        out[base + OFF_CH_PROD_BP_BASE + 4 * ch] = (
            ((b & 0xFFFF) << 16) | (p & 0xFFFF)
        )
    for ch, (s, i) in enumerate(zip(per_ch_starv, per_ch_idle)):
        out[base + OFF_CH_STARV_IDLE_BASE + 4 * ch] = (
            ((i & 0xFFFF) << 16) | (s & 0xFFFF)
        )
    return out


# ---------------------------------------------------------------------------
# BucketCounts arithmetic
# ---------------------------------------------------------------------------

def test_bucketcounts_total_and_util():
    b = BucketCounts(productive=80, backpressure=10, starvation=5, idle=5)
    assert b.total == 100
    assert b.datapath_utilization == 0.8


def test_bucketcounts_util_zero_total_is_zero():
    b = BucketCounts(0, 0, 0, 0)
    assert b.datapath_utilization == 0.0


# ---------------------------------------------------------------------------
# read_meter -- packing/unpacking round-trip
# ---------------------------------------------------------------------------

def test_read_meter_unpacks_aggregate_and_per_channel():
    vals = _meter_values(
        R_METER_BASE,
        agg_prod=950, agg_bp=30, agg_starv=15, agg_idle=5,
        per_ch_prod   = [100, 200, 50, 0, 0, 0, 0, 0],
        per_ch_bp     = [ 10,   5,  3, 0, 0, 0, 0, 0],
        per_ch_starv  = [  2,   1,  1, 0, 0, 0, 0, 0],
        per_ch_idle   = [  3,   2,  1, 0, 0, 0, 0, 0],
        per_ch_overflow = [0]*8,
    )
    reader = CannedReader(vals)
    snap = read_meter(reader, R_METER_BASE, 8, 'R')

    assert snap.name == 'R'
    assert snap.aggregate.productive == 950
    assert snap.aggregate.backpressure == 30
    assert snap.aggregate.starvation == 15
    assert snap.aggregate.idle == 5
    assert snap.aggregate.total == 1000
    assert snap.aggregate.datapath_utilization == 0.95

    assert len(snap.per_channel) == 8
    assert snap.per_channel[0].productive == 100
    assert snap.per_channel[0].backpressure == 10
    assert snap.per_channel[1].productive == 200
    assert snap.per_channel[1].starvation == 1
    assert snap.per_channel[2].idle == 1
    assert all(c.overflow == 0 for c in snap.per_channel)


def test_read_meter_decodes_per_channel_overflow_mask():
    # Mark ch3 as having "productive" overflowed (bit 3 of the 4-bit slot)
    # and ch5 as having "idle" overflowed (bit 0).
    ovf = [0]*8
    ovf[3] = 0b1000
    ovf[5] = 0b0001
    vals = _meter_values(
        W_METER_BASE,
        agg_prod=0, agg_bp=0, agg_starv=0, agg_idle=0,
        per_ch_prod = [0]*8, per_ch_bp = [0]*8,
        per_ch_starv = [0]*8, per_ch_idle = [0]*8,
        per_ch_overflow = ovf,
    )
    reader = CannedReader(vals)
    snap = read_meter(reader, W_METER_BASE, 8, 'W')
    assert snap.per_channel[3].overflow == 0b1000
    assert snap.per_channel[3].any_overflow
    assert snap.per_channel[5].overflow == 0b0001
    assert not snap.per_channel[0].any_overflow


def test_read_meter_emits_expected_addresses():
    """The reader should issue exactly 5 + 2*num_channels reads at the
    documented offsets (no more, no less). Catches drift in OFF_* constants."""
    vals = _meter_values(
        R_METER_BASE,
        agg_prod=0, agg_bp=0, agg_starv=0, agg_idle=0,
        per_ch_prod = [0]*4, per_ch_bp = [0]*4,
        per_ch_starv = [0]*4, per_ch_idle = [0]*4,
        per_ch_overflow = [0]*4,
    )
    reader = CannedReader(vals)
    read_meter(reader, R_METER_BASE, 4, 'R')

    # 4 aggregate + 1 overflow + 4 channels x 2 per-channel reads
    # The reader interleaves prod_bp and starv_idle per channel, so the
    # access pattern is ch0_pb, ch0_si, ch1_pb, ch1_si, ...
    assert len(reader.read_log) == 5 + 2 * 4
    expected = [
        R_METER_BASE + 0x00,
        R_METER_BASE + 0x04,
        R_METER_BASE + 0x08,
        R_METER_BASE + 0x0C,
        R_METER_BASE + 0x10,
        R_METER_BASE + 0x20, R_METER_BASE + 0x40,  # ch0 pb, si
        R_METER_BASE + 0x24, R_METER_BASE + 0x44,  # ch1
        R_METER_BASE + 0x28, R_METER_BASE + 0x48,  # ch2
        R_METER_BASE + 0x2C, R_METER_BASE + 0x4C,  # ch3
    ]
    assert reader.read_log == expected


# ---------------------------------------------------------------------------
# read_bus_meters -- two-meter wrapper
# ---------------------------------------------------------------------------

def test_read_bus_meters_returns_r_and_w_snapshots():
    # R sees mostly productive; W sees mostly idle.
    vals = {}
    vals.update(_meter_values(
        R_METER_BASE,
        agg_prod=1000, agg_bp=0, agg_starv=0, agg_idle=0,
        per_ch_prod=[1000]+[0]*7, per_ch_bp=[0]*8,
        per_ch_starv=[0]*8, per_ch_idle=[0]*8,
        per_ch_overflow=[0]*8,
    ))
    vals.update(_meter_values(
        W_METER_BASE,
        agg_prod=0, agg_bp=0, agg_starv=0, agg_idle=1000,
        per_ch_prod=[0]*8, per_ch_bp=[0]*8,
        per_ch_starv=[0]*8, per_ch_idle=[1000]+[0]*7,
        per_ch_overflow=[0]*8,
    ))
    reader = CannedReader(vals)
    snaps = read_bus_meters(reader, 8)

    assert set(snaps.keys()) == {'r', 'w'}
    assert snaps['r'].aggregate.datapath_utilization == 1.0
    assert snaps['w'].aggregate.datapath_utilization == 0.0
    assert snaps['r'].per_channel[0].productive == 1000
    assert snaps['w'].per_channel[0].idle == 1000


# ---------------------------------------------------------------------------
# format_meter / format_snapshot -- shape only
# ---------------------------------------------------------------------------

def test_format_meter_emits_utilization_and_per_channel_table():
    snap = MeterSnapshot(
        name='R',
        aggregate=BucketCounts(productive=80, backpressure=10, starvation=5, idle=5),
        per_channel=[
            ChannelBuckets(channel=0, productive=80, backpressure=10,
                           starvation=5, idle=5, overflow=0),
        ],
    )
    buf = io.StringIO()
    format_meter(snap, file=buf)
    out = buf.getvalue()
    assert "R-bus meter" in out
    assert "datapath_util" in out
    assert " 80.0%" in out
    assert "Per-channel breakdown" in out


def test_format_meter_flags_overflow_channels():
    snap = MeterSnapshot(
        name='W',
        aggregate=BucketCounts(0, 0, 0, 0),
        per_channel=[
            ChannelBuckets(channel=0, productive=0xFFFF, backpressure=0,
                           starvation=0, idle=0, overflow=0b1000),
        ],
    )
    buf = io.StringIO()
    format_meter(snap, file=buf)
    out = buf.getvalue()
    assert "PROD wrapped" in out
