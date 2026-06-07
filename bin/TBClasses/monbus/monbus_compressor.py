"""
monbus_compressor.py — Python model of the future monbus bulk-trace
compressor.

This is a pre-RTL modeling tool. It encodes a stream of
`(packet[127:0], timestamp[63:0])` records into 64-bit AXIL slots
using the tagged-timestamp beat format defined in
`docs/markdown/RTLAmba/includes/monitor_package_spec.md`, and decodes
the resulting slot stream back to the original records.

The encoder and decoder are bit-exact mirrors of each other — they
must produce identical CAM state at every step so the decoder can
reconstruct templates from the slots alone (without out-of-band
information about CAM contents).

Once the encoder/decoder behavior here is validated against real
captured traces, this file becomes the spec the RTL compressor
implements. Until then, the RTL writer hardwires `tag = 4'h0` (raw)
on every record and these classes are only used by the modeling /
tuning workflow.

----------------------------------------------------------------------
Format (locked-in for this iteration; bit allocations may be tuned
based on trace statistics before RTL implementation):

Tag 0x0 — Raw / no compression / Tier-0 escape (3 beats):
    beat 0: {tag[3:0]=0x0, source_ts[59:0]}
    beat 1: packet[127:64]
    beat 2: packet[63:0]

Tag 0x1 — Tier-1 format A (template hit, small payload, 1 beat):
    beat 0: {tag=0x1, tmpl_idx[4:0], delta_ts[14:0], event_data[39:0]}
    Covers: Δts ≤ 32K cycles, event_data ≤ 40 bits

Tag 0x2 — Tier-1 format B (template hit, big delta_ts, 1 beat):
    beat 0: {tag=0x2, tmpl_idx[4:0], delta_ts[22:0], event_data[31:0]}
    Covers: Δts ≤ 8M cycles, event_data ≤ 32 bits

Tag 0x3 — Tier-1 format C (template hit, event_data delta, 1 beat):
    beat 0: {tag=0x3, tmpl_idx[4:0], delta_ts[14:0], ed_delta[39:0] signed}
    Covers: Δts ≤ 32K cycles, monotonic counters / sequential addresses

Tags 0x4-0xF — Reserved for future use.

CAM: 32 entries by default (locked 2026-06-06 based on real desc-bus
captures — see fpga_stream_char_v1 dataset). Heavy workloads with up to
~8 channels × ~3 reporter cones plateau at ~17 hot templates that
account for >33% of records; cold tail has too much inter-arrival gap
to benefit from a larger CAM at any practical size (analyzed up to 128,
no incremental gain past 32). The 5-bit template index steals one bit
from delta_ts in each of formats A/B/C — measured at 99% in-band on
real captures, the few overflows were already SRAM-wrap noise.

Each entry stores a template (packet_type, protocol, event_code,
channel_id, agent_id, unit_id) plus the most-recent event_data observed
for that template. Eviction policy is LRU; insertion happens on a
Tier-0 escape (CAM miss).
----------------------------------------------------------------------
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Iterator, List, Optional, Tuple

from .monbus_types import MONBUS_PKT_WIDTH, MONBUS_TS_WIDTH


# ---------------------------------------------------------------------------
# Format constants
# ---------------------------------------------------------------------------

TAG_RAW       = 0x0
TAG_FORMAT_A  = 0x1
TAG_FORMAT_B  = 0x2
TAG_FORMAT_C  = 0x3

TS_BITS       = 60                  # timestamp width in compressed beats
DELTA_TS_A    = 15                  # format A: 15-bit delta_ts (~328 µs @ 100 MHz)
DELTA_TS_B    = 23                  # format B: 23-bit delta_ts (~84 ms @ 100 MHz)
DELTA_TS_C    = 15                  # format C: 15-bit delta_ts
EVENT_DATA_A  = 40                  # format A: 40-bit event_data low bits
EVENT_DATA_B  = 32                  # format B: 32-bit event_data low bits
EVENT_DATA_C_DELTA = 40             # format C: 40-bit signed delta
TMPL_IDX_BITS = 5                   # 5-bit template index → 32-entry CAM

DEFAULT_CAM_SIZE = 32

# Derived: idx field starts at bit 55 (under the 4-bit tag at 63:60 +
# 1-bit idx growth from the legacy 4-bit packing). All Tier-1 slot
# packers shift idx into [59:55] and mask with TMPL_IDX_MASK.
TMPL_IDX_MASK = (1 << TMPL_IDX_BITS) - 1
TMPL_IDX_SHIFT = 64 - 4 - TMPL_IDX_BITS  # 64 - 4 (tag) - 5 (idx) = 55

# Packet field positions (see monitor_common_pkg.sv)
_PKT_TYPE_HI, _PKT_TYPE_LO     = 127, 124
_PROTOCOL_HI, _PROTOCOL_LO     = 108, 105
_EVENT_CODE_HI, _EVENT_CODE_LO = 104,  97
_CHANNEL_ID_HI, _CHANNEL_ID_LO =  96,  88
_AGENT_ID_HI, _AGENT_ID_LO     =  87,  72
_UNIT_ID_HI, _UNIT_ID_LO       =  71,  64
_EVENT_DATA_HI, _EVENT_DATA_LO =  63,   0


def _field(packet: int, hi: int, lo: int) -> int:
    """Extract bits [hi:lo] from a 128-bit packet integer."""
    width = hi - lo + 1
    return (packet >> lo) & ((1 << width) - 1)


def _make_packet(packet_type: int, protocol: int, event_code: int,
                 channel_id: int, agent_id: int, unit_id: int,
                 event_data: int) -> int:
    """Rebuild a 128-bit packet from its fields.
    Reserved bits [123:109] always zero."""
    pkt = 0
    pkt |= (packet_type & 0xF)   << _PKT_TYPE_LO
    pkt |= (protocol   & 0xF)    << _PROTOCOL_LO
    pkt |= (event_code & 0xFF)   << _EVENT_CODE_LO
    pkt |= (channel_id & 0x1FF)  << _CHANNEL_ID_LO
    pkt |= (agent_id   & 0xFFFF) << _AGENT_ID_LO
    pkt |= (unit_id    & 0xFF)   << _UNIT_ID_LO
    pkt |= (event_data & ((1 << 64) - 1)) << _EVENT_DATA_LO
    return pkt & ((1 << MONBUS_PKT_WIDTH) - 1)


def _sign_extend(value: int, bits: int) -> int:
    """Sign-extend a `bits`-wide unsigned int to a Python int."""
    sign_bit = 1 << (bits - 1)
    return (value & (sign_bit - 1)) - (value & sign_bit)


# ---------------------------------------------------------------------------
# Template (the key the CAM keys on) + CAM state
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TemplateKey:
    """The fields that identify a packet "kind" for template matching.
    event_data is NOT part of the key — that's what gets compressed."""
    packet_type: int
    protocol:    int
    event_code:  int
    channel_id:  int
    agent_id:    int
    unit_id:     int


@dataclass
class CamEntry:
    key:  TemplateKey
    last_event_data: int
    hits: int = 0           # for stats


def _key_from_packet(packet: int) -> TemplateKey:
    return TemplateKey(
        packet_type = _field(packet, _PKT_TYPE_HI,    _PKT_TYPE_LO),
        protocol    = _field(packet, _PROTOCOL_HI,    _PROTOCOL_LO),
        event_code  = _field(packet, _EVENT_CODE_HI,  _EVENT_CODE_LO),
        channel_id  = _field(packet, _CHANNEL_ID_HI,  _CHANNEL_ID_LO),
        agent_id    = _field(packet, _AGENT_ID_HI,    _AGENT_ID_LO),
        unit_id     = _field(packet, _UNIT_ID_HI,     _UNIT_ID_LO),
    )


class Cam:
    """LRU CAM. Head of the list is most-recently-used.

    Both encoder and decoder maintain identical CAM state by feeding
    the SAME sequence of (key, event_data) updates through this class.
    """

    def __init__(self, size: int = DEFAULT_CAM_SIZE):
        self.size = size
        self.entries: List[CamEntry] = []

    def reset(self):
        self.entries.clear()

    def lookup(self, key: TemplateKey) -> Optional[int]:
        """Return the index of `key` in the CAM, or None if absent.
        Touches the entry (moves to head) on hit — counts as LRU access."""
        for i, e in enumerate(self.entries):
            if e.key == key:
                # Move-to-front (LRU touch)
                self.entries.insert(0, self.entries.pop(i))
                self.entries[0].hits += 1
                return 0
        return None

    def install(self, key: TemplateKey, event_data: int) -> int:
        """Install a new template (called on Tier-0 escape paths).
        Evicts the LRU entry if full. Returns the new index (always 0)."""
        # If already present, just update event_data and move-to-front.
        for i, e in enumerate(self.entries):
            if e.key == key:
                e.last_event_data = event_data
                e.hits += 1
                self.entries.insert(0, self.entries.pop(i))
                return 0
        # Insert at head; evict LRU (tail) if full.
        if len(self.entries) >= self.size:
            self.entries.pop()
        self.entries.insert(0, CamEntry(key=key, last_event_data=event_data))
        return 0

    def update_event_data(self, idx: int, event_data: int):
        """Refresh the template's last_event_data after a Tier-1 hit."""
        self.entries[idx].last_event_data = event_data


# ---------------------------------------------------------------------------
# Encoder state + statistics
# ---------------------------------------------------------------------------

class EscapeReason:
    CAM_MISS         = "cam_miss"
    DELTA_TS_OVF     = "delta_ts_overflow"
    EVENT_DATA_OVF   = "event_data_overflow"
    ED_DELTA_OVF     = "event_data_delta_overflow"


@dataclass
class CompressorStats:
    records_total:    int = 0
    tier1_a_hits:     int = 0
    tier1_b_hits:     int = 0
    tier1_c_hits:     int = 0
    tier0_escapes:    int = 0
    escape_reasons:   dict = field(default_factory=dict)
    slots_emitted:    int = 0     # 64-bit slots produced

    @property
    def tier1_hits(self) -> int:
        return self.tier1_a_hits + self.tier1_b_hits + self.tier1_c_hits

    @property
    def bits_in(self) -> int:
        # 192 bits per input record (128 packet + 64 timestamp).
        return self.records_total * 192

    @property
    def bits_out(self) -> int:
        return self.slots_emitted * 64

    @property
    def compression_ratio(self) -> float:
        if self.bits_out == 0:
            return 0.0
        return self.bits_in / self.bits_out

    @property
    def tier1_hit_rate(self) -> float:
        if self.records_total == 0:
            return 0.0
        return self.tier1_hits / self.records_total

    def bump_escape(self, reason: str):
        self.escape_reasons[reason] = self.escape_reasons.get(reason, 0) + 1


# ---------------------------------------------------------------------------
# Encoder
# ---------------------------------------------------------------------------

class Encoder:
    """Compresses a stream of (packet, timestamp) records to 64-bit slots."""

    def __init__(self, cam_size: int = DEFAULT_CAM_SIZE):
        self.cam = Cam(cam_size)
        self.last_ts: int = 0
        self.stats = CompressorStats()

    def reset(self):
        self.cam.reset()
        self.last_ts = 0
        self.stats = CompressorStats()

    def encode_one(self, packet: int, timestamp: int) -> List[int]:
        """Encode one record. Returns a list of 1 or 3 64-bit slot ints."""
        self.stats.records_total += 1
        packet &= (1 << MONBUS_PKT_WIDTH) - 1
        timestamp &= (1 << MONBUS_TS_WIDTH) - 1

        key = _key_from_packet(packet)
        event_data = _field(packet, _EVENT_DATA_HI, _EVENT_DATA_LO)
        delta_ts = (timestamp - self.last_ts) & ((1 << MONBUS_TS_WIDTH) - 1)

        # Try CAM lookup (does NOT move-to-front; that's done by install
        # for Tier-0 path, and we'll do it manually on Tier-1 hit below).
        # We need a non-mutating lookup first to decide whether the
        # candidate fits Tier-1; if it does we then commit via touch.
        idx = self._cam_peek(key)

        if idx is not None:
            # Format A: small delta_ts + small absolute event_data
            if delta_ts < (1 << DELTA_TS_A) and event_data < (1 << EVENT_DATA_A):
                self._touch(idx, event_data)
                self.last_ts = timestamp
                self.stats.tier1_a_hits += 1
                self.stats.slots_emitted += 1
                return [self._pack_format_a(idx, delta_ts, event_data)]

            # Format B: big delta_ts + smaller absolute event_data
            if delta_ts < (1 << DELTA_TS_B) and event_data < (1 << EVENT_DATA_B):
                self._touch(idx, event_data)
                self.last_ts = timestamp
                self.stats.tier1_b_hits += 1
                self.stats.slots_emitted += 1
                return [self._pack_format_b(idx, delta_ts, event_data)]

            # Format C: small delta_ts + signed delta event_data
            if delta_ts < (1 << DELTA_TS_C):
                last_ed = self.cam.entries[idx].last_event_data
                ed_delta = event_data - last_ed
                lo = -(1 << (EVENT_DATA_C_DELTA - 1))
                hi = (1 << (EVENT_DATA_C_DELTA - 1))
                if lo <= ed_delta < hi:
                    self._touch(idx, event_data)
                    self.last_ts = timestamp
                    self.stats.tier1_c_hits += 1
                    self.stats.slots_emitted += 1
                    return [self._pack_format_c(idx, delta_ts, ed_delta)]

            # Tier-1 candidate failed every sub-format — pick a reason.
            if delta_ts >= (1 << DELTA_TS_B):
                self.stats.bump_escape(EscapeReason.DELTA_TS_OVF)
            elif event_data >= (1 << EVENT_DATA_A):
                self.stats.bump_escape(EscapeReason.EVENT_DATA_OVF)
            else:
                self.stats.bump_escape(EscapeReason.ED_DELTA_OVF)
        else:
            self.stats.bump_escape(EscapeReason.CAM_MISS)

        # Tier-0 escape (raw 3-beat record).
        self.cam.install(key, event_data)
        self.last_ts = timestamp
        self.stats.tier0_escapes += 1
        self.stats.slots_emitted += 3
        return self._pack_raw(packet, timestamp)

    def encode(self, records: Iterable[Tuple[int, int]]) -> Iterator[int]:
        for pkt, ts in records:
            yield from self.encode_one(pkt, ts)

    # ----- helpers -----

    def _cam_peek(self, key: TemplateKey) -> Optional[int]:
        """Index lookup without LRU touch."""
        for i, e in enumerate(self.cam.entries):
            if e.key == key:
                return i
        return None

    def _touch(self, idx: int, new_event_data: int):
        """Move CAM[idx] to front and update last_event_data — same
        bookkeeping the decoder will do on the matching hit."""
        e = self.cam.entries.pop(idx)
        e.last_event_data = new_event_data
        e.hits += 1
        self.cam.entries.insert(0, e)

    @staticmethod
    def _pack_format_a(idx: int, delta_ts: int, event_data: int) -> int:
        # [63:60] tag, [59:55] idx, [54:40] delta_ts (15b), [39:0] event_data
        return (
            (TAG_FORMAT_A << 60)
            | ((idx & TMPL_IDX_MASK) << TMPL_IDX_SHIFT)
            | ((delta_ts & ((1 << DELTA_TS_A) - 1)) << EVENT_DATA_A)
            | (event_data & ((1 << EVENT_DATA_A) - 1))
        )

    @staticmethod
    def _pack_format_b(idx: int, delta_ts: int, event_data: int) -> int:
        # [63:60] tag, [59:55] idx, [54:32] delta_ts (23b), [31:0] event_data
        return (
            (TAG_FORMAT_B << 60)
            | ((idx & TMPL_IDX_MASK) << TMPL_IDX_SHIFT)
            | ((delta_ts & ((1 << DELTA_TS_B) - 1)) << EVENT_DATA_B)
            | (event_data & ((1 << EVENT_DATA_B) - 1))
        )

    @staticmethod
    def _pack_format_c(idx: int, delta_ts: int, ed_delta: int) -> int:
        # [63:60] tag, [59:55] idx, [54:40] delta_ts (15b), [39:0] signed ed_delta
        return (
            (TAG_FORMAT_C << 60)
            | ((idx & TMPL_IDX_MASK) << TMPL_IDX_SHIFT)
            | ((delta_ts & ((1 << DELTA_TS_C) - 1)) << EVENT_DATA_C_DELTA)
            | (ed_delta & ((1 << EVENT_DATA_C_DELTA) - 1))
        )

    @staticmethod
    def _pack_raw(packet: int, timestamp: int) -> List[int]:
        ts60 = timestamp & ((1 << TS_BITS) - 1)
        return [
            (TAG_RAW << 60) | ts60,
            (packet >> 64) & ((1 << 64) - 1),
            packet & ((1 << 64) - 1),
        ]


# ---------------------------------------------------------------------------
# Decoder
# ---------------------------------------------------------------------------

class Decoder:
    """Bit-exact mirror of Encoder. Same CAM state evolution."""

    def __init__(self, cam_size: int = DEFAULT_CAM_SIZE):
        self.cam = Cam(cam_size)
        self.last_ts: int = 0

    def reset(self):
        self.cam.reset()
        self.last_ts = 0

    def decode(self, slots: Iterable[int]) -> Iterator[Tuple[int, int]]:
        """Decode a stream of 64-bit slots into (packet, timestamp) tuples."""
        it = iter(slots)
        for beat0 in it:
            beat0 &= (1 << 64) - 1
            tag = (beat0 >> 60) & 0xF

            if tag == TAG_RAW:
                ts60 = beat0 & ((1 << TS_BITS) - 1)
                pkt_hi = next(it) & ((1 << 64) - 1)
                pkt_lo = next(it) & ((1 << 64) - 1)
                packet = ((pkt_hi << 64) | pkt_lo) & ((1 << MONBUS_PKT_WIDTH) - 1)
                # Mirror encoder: install template in CAM.
                key = _key_from_packet(packet)
                event_data = _field(packet, _EVENT_DATA_HI, _EVENT_DATA_LO)
                self.cam.install(key, event_data)
                self.last_ts = ts60
                yield packet, ts60

            elif tag == TAG_FORMAT_A:
                idx = (beat0 >> TMPL_IDX_SHIFT) & TMPL_IDX_MASK
                delta_ts = (beat0 >> EVENT_DATA_A) & ((1 << DELTA_TS_A) - 1)
                event_data = beat0 & ((1 << EVENT_DATA_A) - 1)
                yield self._reconstruct(idx, delta_ts, event_data)

            elif tag == TAG_FORMAT_B:
                idx = (beat0 >> TMPL_IDX_SHIFT) & TMPL_IDX_MASK
                delta_ts = (beat0 >> EVENT_DATA_B) & ((1 << DELTA_TS_B) - 1)
                event_data = beat0 & ((1 << EVENT_DATA_B) - 1)
                yield self._reconstruct(idx, delta_ts, event_data)

            elif tag == TAG_FORMAT_C:
                idx = (beat0 >> TMPL_IDX_SHIFT) & TMPL_IDX_MASK
                delta_ts = (beat0 >> EVENT_DATA_C_DELTA) & ((1 << DELTA_TS_C) - 1)
                ed_delta = _sign_extend(beat0 & ((1 << EVENT_DATA_C_DELTA) - 1),
                                        EVENT_DATA_C_DELTA)
                last_ed = self.cam.entries[idx].last_event_data
                event_data = (last_ed + ed_delta) & ((1 << 64) - 1)
                yield self._reconstruct(idx, delta_ts, event_data)

            else:
                raise ValueError(f"Decoder: unknown tag 0x{tag:x} in slot 0x{beat0:016x}")

    def _reconstruct(self, idx: int, delta_ts: int, event_data: int):
        """Build packet from template + new event_data, advance ts, touch CAM."""
        e = self.cam.entries[idx]
        packet = _make_packet(
            packet_type = e.key.packet_type,
            protocol    = e.key.protocol,
            event_code  = e.key.event_code,
            channel_id  = e.key.channel_id,
            agent_id    = e.key.agent_id,
            unit_id     = e.key.unit_id,
            event_data  = event_data,
        )
        ts = (self.last_ts + delta_ts) & ((1 << MONBUS_TS_WIDTH) - 1)
        # Move-to-front + update event_data, mirroring encoder's _touch.
        self.cam.entries.pop(idx)
        e.last_event_data = event_data
        e.hits += 1
        self.cam.entries.insert(0, e)
        self.last_ts = ts
        return packet, ts


# ---------------------------------------------------------------------------
# Statistics reporter
# ---------------------------------------------------------------------------

def format_report(enc: Encoder, limit_top_templates: int = 8) -> str:
    """Build a human-readable summary of an encoder's run."""
    s = enc.stats
    lines = []
    lines.append(f"Records:           {s.records_total}")
    if s.records_total == 0:
        lines.append("(empty stream)")
        return "\n".join(lines)
    lines.append(f"Tier 1 hits:       {s.tier1_hits} ({100*s.tier1_hit_rate:.1f}%)")
    if s.tier1_hits:
        lines.append(f"  - format A:      {s.tier1_a_hits} ({100*s.tier1_a_hits/s.records_total:.1f}%)")
        lines.append(f"  - format B:      {s.tier1_b_hits} ({100*s.tier1_b_hits/s.records_total:.1f}%)")
        lines.append(f"  - format C:      {s.tier1_c_hits} ({100*s.tier1_c_hits/s.records_total:.1f}%)")
    lines.append(f"Tier 0 (raw):      {s.tier0_escapes} ({100*s.tier0_escapes/s.records_total:.1f}%)")
    if s.escape_reasons:
        lines.append("")
        lines.append("Escape reasons (Tier 0):")
        for reason in sorted(s.escape_reasons, key=lambda r: -s.escape_reasons[r]):
            n = s.escape_reasons[reason]
            lines.append(f"  {reason:24s}  {n} ({100*n/s.tier0_escapes:.0f}%)")

    lines.append("")
    lines.append(f"CAM final state ({len(enc.cam.entries)}/{enc.cam.size} entries used):")
    for i, e in enumerate(enc.cam.entries[:limit_top_templates]):
        lines.append(
            f"  [{i:2d}]  pkt_type=0x{e.key.packet_type:x} "
            f"protocol=0x{e.key.protocol:x} "
            f"event=0x{e.key.event_code:02x} "
            f"agent=0x{e.key.agent_id:04x} "
            f"chan={e.key.channel_id} "
            f"unit=0x{e.key.unit_id:02x}  "
            f"hits={e.hits}"
        )
    if len(enc.cam.entries) > limit_top_templates:
        lines.append(f"  ... and {len(enc.cam.entries) - limit_top_templates} more")

    lines.append("")
    lines.append(f"Bits in:           {s.bits_in:,} ({s.records_total} × 192b records)")
    lines.append(f"Bits out:          {s.bits_out:,} ({s.slots_emitted} × 64b slots)")
    if s.bits_out:
        avg_bits = s.bits_out / s.records_total
        lines.append(f"Avg per record:    {avg_bits:.1f} bits ({avg_bits/8:.2f} bytes)")
        lines.append(f"Compression ratio: {s.compression_ratio:.2f}x")

    return "\n".join(lines)


__all__ = [
    "Encoder", "Decoder", "Cam", "CamEntry",
    "TemplateKey", "CompressorStats", "EscapeReason",
    "format_report",
    "TAG_RAW", "TAG_FORMAT_A", "TAG_FORMAT_B", "TAG_FORMAT_C",
    "DEFAULT_CAM_SIZE",
]
