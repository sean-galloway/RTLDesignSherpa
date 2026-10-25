# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Buffer sizing rule for a generated bridge (bridge TASK-016).

Every response-tracking buffer in a bridge is a credit loop: a master may
keep `max_outstanding` transactions in flight, and a stream of B-beat bursts
saturates its port only while

    max_outstanding * B  >=  B + latency_cycles + round_trip

(Dally & Towles ch. 12 / 15: the required depth is the loop's round trip, in
units of what each entry carries). Of the three terms the generator knows
two: the burst is the master's business, the slave's own response latency is
a TOML hint (`latency_cycles`, default 0: a slave that answers the cycle after
it accepts), and the fabric round trip is the sum of the registered stages
the generator itself builds on the path. This module adds those stages up
per (master, slave) path, derives the minimal depth for every port whose TOML
leaves it unset, and reports the rule beside each depth so an override is a
decision, not a guess.

The round-trip model is a BOUND, calibrated against the single-beat round
trips the bandwidth gate measured (`test_bridge_perf_char.RTT_BUDGET`):
plain 2x2 write 8 / read 7, registered crossbar 10 / 8, a 2:1 upsize into a
shared slave 12, a CDC port 13-15. `bin/tests/test_generator_pkg.py` holds
the model to those within two cycles. It is not a cycle-exact simulator.

Depths derived here (TOML key wins when present):
  max_outstanding  pow2 >= 1 + latency_cycles + round_trip, over the port's
                   connected paths; 2..64. Sizes every tracker, W-destination
                   and W-owner FIFO and remap table on the path.
  rate_buffer      wide beats to hold a `max_burst_beats`-beat narrow burst
                   whole on an upsized path into a shared slave:
                   pow2 >= max_burst_beats / ratio, >= 2; 0 where no such path.
Skid depths default to 2 on every channel (`config._DEFAULT_SKID_DEPTHS`):
the smallest stage that sustains one beat per cycle.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

SHIMS = ('apb', 'apb5', 'axil', 'axil5', 'wb4')
AXI = ('axi3', 'axi4', 'axi5')
MIN_OUTSTANDING, MAX_OUTSTANDING = 2, 64
MIN_RATE_BUFFER = 2


def pow2_ceil(n: int) -> int:
    return 1 << max(0, (int(n) - 1).bit_length())


def _skid(port, ch: str) -> int:
    return int((getattr(port, 'skid_depths', None) or {}).get(ch, 2))


@dataclass(frozen=True)
class PathLoop:
    """The fabric's own round trip on one master -> slave path, cycles."""
    master: str
    slave: str
    read: int
    write: int
    terms: Tuple[Tuple[str, int], ...]

    @property
    def worst(self) -> int:
        return max(self.read, self.write)


@dataclass
class SizingRow:
    port: str
    direction: str              # 'master' | 'slave'
    key: str                    # 'max_outstanding' | 'rate_buffer'
    value: int
    source: str                 # 'toml' | 'rule'
    rule_min: int               # the rule's minimum before rounding
    basis: str                  # how rule_min came about, one line
    warning: Optional[str] = None


def _connected(cfg, m, s) -> bool:
    return s.port_name in (cfg.connectivity or {}).get(m.port_name, [])


def _shared(cfg, s) -> bool:
    return sum(1 for m in cfg.masters if _connected(cfg, m, s)) >= 2


def path_loop(cfg, m, s) -> PathLoop:
    """Registered stages on the m -> s path, request side then response
    side, as the generators build them (crossbar `_uses_slots`,
    adapter `_rate_buffer_depth`, the timing wrappers' `latency` cuts)."""
    pipe = 1 if getattr(cfg, 'xbar_pipeline', False) else 0
    shared = _shared(cfg, s)
    cdc = bool(getattr(m, 'cdc', False) or getattr(s, 'cdc', False))
    s_axi = s.protocol in AXI
    # the slave's AW/AR request slot: an arbitrated slave whose channel had
    # a register to replace, or a shim (crossbar_generator._uses_slots);
    # a CDC slave is arbitrated on its own clock from lanes instead
    slot = 0
    if shared and not getattr(s, 'cdc', False):
        if s.protocol in SHIMS:
            slot = 1
        elif s_axi and (_skid(s, 'aw') > 0 or pipe):
            slot = 1
    width_conv = m.data_width != s.data_width
    rate = 1 if (m.data_width < s.data_width and shared and int(getattr(m, 'rate_buffer', 0) or 0) > 0
                 and m.protocol in AXI) else 0
    conv_req = conv_resp = 0
    if width_conv and m.protocol in AXI:
        conv_req, conv_resp = 2, 2            # dwidth converter, both sides skid-isolated
    if s.protocol in ('apb', 'apb5'):
        conv_req, conv_resp = conv_req + 2, conv_resp + 2
    elif s.protocol in ('axil', 'axil5', 'wb4'):
        conv_req, conv_resp = conv_req + 1, conv_resp + 1
    elif s.protocol == 'axi3':
        conv_req += 1
    if m.protocol == 'axi3':
        conv_req += 1
    elif m.protocol in SHIMS:                 # requester-side aligners
        conv_req, conv_resp = conv_req + 1, conv_resp + 1
    if cdc:
        conv_req, conv_resp = conv_req + 3, conv_resp + 3

    def side(ax: str, resp: str) -> Tuple[int, List[Tuple[str, int]]]:
        terms = [
            ('master request stage', 1 if _skid(m, ax) > 0 else 0),
            ('request slot', slot),
            ('xbar request stage', pipe),
            ('slave request stage', 1 if (s_axi and _skid(s, ax) > 0) else 0),
            ('converters, request side', conv_req),
            ('rate buffer', rate),
            ('slave turnaround', 1),
            ('slave response stage', 1 if (s_axi and _skid(s, resp) > 0) else 0),
            ('converters, response side', conv_resp),
            ('xbar response stage', pipe),
            ('response routing', 1),
            ('master response stage', 1 if _skid(m, resp) > 0 else 0),
        ]
        return sum(v for _, v in terms), terms

    rd, rd_terms = side('ar', 'r')
    wr, _ = side('aw', 'b')
    wr += 1                                   # W follows its AW's grant by a cycle
    return PathLoop(m.port_name, s.port_name, rd, wr, tuple(rd_terms))


def rule_outstanding(cfg, port) -> Tuple[int, str]:
    """(minimum in flight for a single-beat stream to saturate this port,
    the path that set it)."""
    best, basis = 0, 'no connected path'
    # the internal catch-all slave answers DECERR at once and sizes nothing
    if port.direction == 'master':
        paths = [(port, s) for s in cfg.slaves
                 if _connected(cfg, port, s) and not getattr(s, 'internal', False)]
    else:
        paths = [(m, port) for m in cfg.masters if _connected(cfg, m, port)]
    for m, s in paths:
        lp = path_loop(cfg, m, s)
        lat = int(getattr(s, 'latency_cycles', 0) or 0)
        n = 1 + lat + lp.worst
        if n > best:
            best = n
            basis = (f"1 + latency_cycles {lat} + round trip {lp.worst} "
                     f"({m.port_name} -> {s.port_name}, write {lp.write} / read {lp.read})")
    return best, basis


def rule_rate_buffer(cfg, m) -> Tuple[int, str]:
    """(wide beats needed to hold a max_burst_beats-beat burst whole on the
    master's widest upsized path into a shared slave, the path)."""
    if m.protocol not in AXI or m.channels not in ('wr', 'rw'):
        return 0, 'no burst write path'
    bb = int(getattr(m, 'max_burst_beats', 16) or 16)
    best, basis = 0, 'no upsized path into a shared slave'
    for s in cfg.slaves:
        if not _connected(cfg, m, s) or s.data_width <= m.data_width or not _shared(cfg, s):
            continue
        ratio = s.data_width // m.data_width
        need = max(MIN_RATE_BUFFER, -(-bb // ratio))
        if need > best:
            best = need
            basis = f"max_burst_beats {bb} / ratio {ratio} ({m.port_name} -> {s.port_name}, {s.data_width}b shared)"
    return best, basis


def apply(cfg) -> Tuple[List[SizingRow], List[str]]:
    """Fill every unset depth from the rule and report all of them."""
    rows: List[SizingRow] = []
    warnings: List[str] = []
    for port in list(cfg.masters) + list(cfg.slaves):
        if getattr(port, 'internal', False):
            continue
        n_min, basis = rule_outstanding(cfg, port)
        if getattr(port, 'max_outstanding_set', False):
            v = int(port.max_outstanding)
            w = None
            if n_min and v < n_min:
                w = (f"{port.direction} '{port.port_name}': max_outstanding = {v} is under the rule's "
                     f"minimum {n_min} ({basis}); a single-beat stream tops out at {v}/{n_min:.0f} "
                     f"of the port's peak")
                warnings.append(w)
            rows.append(SizingRow(port.port_name, port.direction, 'max_outstanding', v, 'toml',
                                  n_min, basis, w))
        else:
            # A master whose ID fits a 16-deep slot (id_width <= 4) keeps its
            # own ID end to end today; a derived depth under 2**id_width would
            # make the slot narrower than the ID and switch bridge_id_remap on
            # (a table bigger than the tracker entries it saved). The rule does
            # not make that trade by itself: floor at 2**id_width unless the
            # port opted out of remapping (id_remap = false, IDs whole).
            floor = 0
            if (port.direction == 'master' and getattr(port, 'id_remap', True)
                    and 0 < int(getattr(port, 'id_width', 0) or 0) <= 4):
                floor = 1 << int(port.id_width)
                if floor > n_min:
                    basis = f"{basis}; floored at 2**id_width = {floor} so the {port.id_width}-bit ID is not remapped"
            v = min(MAX_OUTSTANDING, max(MIN_OUTSTANDING, pow2_ceil(max(1, n_min, floor))))
            port.max_outstanding = v
            w = None
            if n_min > MAX_OUTSTANDING:
                w = (f"{port.direction} '{port.port_name}': the rule wants {n_min} in flight, more than "
                     f"the {MAX_OUTSTANDING} the trackers can hold; a single-beat stream tops out at "
                     f"{MAX_OUTSTANDING}/{n_min} of the port's peak")
                warnings.append(w)
            rows.append(SizingRow(port.port_name, port.direction, 'max_outstanding', v, 'rule',
                                  n_min, basis, w))
        if port.direction == 'master':
            r_min, r_basis = rule_rate_buffer(cfg, port)
            if getattr(port, 'rate_buffer_set', False):
                v = int(port.rate_buffer or 0)
                w = None
                if r_min and 0 < v < r_min:
                    w = (f"master '{port.port_name}': rate_buffer = {v} wide beats holds less than one "
                         f"max_burst_beats burst ({r_basis}); longer bursts hold the shared slave at "
                         f"the narrow rate")
                    warnings.append(w)
                rows.append(SizingRow(port.port_name, 'master', 'rate_buffer', v, 'toml', r_min, r_basis, w))
            else:
                v = pow2_ceil(r_min) if r_min else 0
                port.rate_buffer = v
                rows.append(SizingRow(port.port_name, 'master', 'rate_buffer', v, 'rule', r_min, r_basis))
        # bridge TASK-020: an atomic slave's read-return tracker is a depth too;
        # no loop model (the far end's atomic latency is its own), so it is
        # reported as pinned or default, never derived
        if (port.direction == 'slave' and port.protocol == 'axi5'
                and 'atomic' in (getattr(port, 'axi5_features', None) or [])
                and getattr(port, 'channels', 'rw') == 'rw'):
            v = int(getattr(port, 'atomic_rr_depth', 8) or 8)
            rows.append(SizingRow(port.port_name, 'slave', 'atomic_rr_depth', v,
                                  'toml' if getattr(port, 'atomic_rr_depth_set', False) else 'default', v,
                                  'read-return atomics in flight at this port (axi5_atomic_rr_tracker); the next atomic AW waits'))
    cfg.sizing = rows
    cfg.sizing_warnings = warnings
    return rows, warnings


def report_lines(cfg) -> List[str]:
    out = ["  sizing (bridge TASK-016): depth = TOML value, or the rule's minimum rounded to a power of two"]
    for r in getattr(cfg, 'sizing', []) or []:
        out.append(f"    {r.direction:6} {r.port:<18} {r.key:<15} = {r.value:>3}  [{r.source}]  "
                   f"rule min {r.rule_min}: {r.basis}")
    rq = int(getattr(cfg, 'r_queue_depth', 0) or 0)
    out.append(f"    bridge r_queue_depth = {rq:>3}  [{'toml' if rq else 'default'}]  "
               + (f"{rq}-beat read response queue per (reading master, shared slave) pair (bridge TASK-021)"
                  if rq else "no read response queues: a shared slave's in-order R can head-of-line block past saturation (bridge TASK-021)"))
    for w in getattr(cfg, 'sizing_warnings', []) or []:
        out.append(f"  WARNING: {w}")
    return out


def as_dict(cfg) -> Dict:
    return {
        'bridge': cfg.name,
        'rule': 'max_outstanding >= 1 + latency_cycles + round_trip (single-beat saturation); '
                'rate_buffer >= max_burst_beats / ratio; skid stages 2 (one beat per cycle)',
        'ports': [dict(port=r.port, direction=r.direction, key=r.key, value=r.value, source=r.source,
                       rule_min=r.rule_min, basis=r.basis, warning=r.warning)
                  for r in (getattr(cfg, 'sizing', []) or [])],
        'paths': [dict(master=m.port_name, slave=s.port_name, read=lp.read, write=lp.write,
                       terms=dict(lp.terms))
                  for m in cfg.masters for s in cfg.slaves
                  if _connected(cfg, m, s) and not getattr(s, 'internal', False)
                  for lp in [path_loop(cfg, m, s)]],
        'r_queue_depth': int(getattr(cfg, 'r_queue_depth', 0) or 0),
        'warnings': list(getattr(cfg, 'sizing_warnings', []) or []),
    }
