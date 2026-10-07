"""
amber_fsm_oracle -- gem5-derived golden FSM for the amber MESI L1 line state

Pure Python, no I/O, deterministic. Single source of truth for the *coherence
behavior* of one cache line; the cycle-level blocking pipeline lives in
`amber_control` (MAS ch02), which this model scores.

Derivation: every transition group is hand-cited against the gem5 Ruby
``MESI_Two_Level-L1cache.sm`` transition table (see
``dv/tests/test_amber_oracle.py`` row cites and ``gem5_mapping_notes.md`` in
this directory). DECISION D-11: gem5's TBE transients collapse onto amber's
blocking CTRL transient states as

    gem5 IS       (read miss in flight)      -> amber CTRL_MISS_FILL
    gem5 IM       (write miss in flight)     -> amber CTRL_MISS_FILL
    gem5 SM       (upgrade in flight)        -> amber CTRL_MISS_FILL
    gem5 IS_I     (fill invalidated en route)-> amber CTRL_MISS_FILL (post-commit I)
    gem5 M_I      (dirty victim draining)    -> amber CTRL_MISS_DRAIN
    gem5 SINK_WB_ACK (snoop hit the drain)   -> amber CTRL_MISS_DRAIN

gem5 PF_* prefetch and LLSC_* states are out of scope (D-11). Divergences
from gem5 that amber's IHI0022/broadcast domain requires (ReadOnce on
Modified, MakeInvalid, invalidating snoops during IM/SM, snoops during
drain) are recorded per group in gem5_mapping_notes.md -- this file follows
the landed amber_pkg Table 3.0 decode, which is the binding snoop-decode
authority and is pinned against this oracle by the pkg-pin simulation.

Model shape: a stateless ``step(state, event, fill=None, pending=None)``.
The ``pending`` argument/result carries the one piece of cross-step context
the blocking pipeline cannot express as a line state: a snoop's state
effect (downgrade-to-S / invalidate-to-I) that MAS ch02/02 orders *after*
the fill commits. All other transient context is explicit in the state name.

Author: RTL Design Sherpa
Created: 2026-10-07
"""

from collections import namedtuple

__all__ = [
    'AmberOracleError',
    'STATES',
    'EVENTS',
    'SNOOPS',
    'STATE_CODES',
    'SNOOP_CODES',
    'CRRESP_WIDTH',
    'StepResult',
    'step',
]


class AmberOracleError(Exception):
    """Reserved encoding, unknown argument, or unreachable FSM cell.

    The oracle never guesses: anything outside the derived transition
    table is an ERROR, matching amber_control's sticky CTRL_ERROR contract
    for illegal encodings (MAS ch02).
    """


# ---------------------------------------------------------------------------
# States: the four stable MESI states plus the six gem5 TBE transients
# (D-11 collapse above). Encodings mirror amber_pkg cache_state_t; the
# transient names exist only in this model (amber tracks them as CTRL FSM
# states, not tag encodings).
# ---------------------------------------------------------------------------
STATES = ('I', 'S', 'E', 'M',
          'IS', 'IM', 'SM', 'IS_I', 'M_I', 'SINK_WB_ACK')

STABLE_STATES = ('I', 'S', 'E', 'M')

STATE_CODES = {
    'I': 0b000,
    'S': 0b001,
    'E': 0b010,
    'M': 0b011,
    'O':     0b100,   # reserved (MOESI headroom, PRD D6) -- oracle refuses
    'RSV5':  0b101,
    'RSV6':  0b110,
    'RSV7':  0b111,
}

# The ten amber oracle events: cpu rd/wr, the six IHI0022 AC snoops, and
# the two transaction completions. (The MonBus AMBER_EV_* observation
# codes in amber_pkg are a different, output-side enumeration.)
SNOOPS = ('SNOOP_READ_SHARED', 'SNOOP_READ_ONCE', 'SNOOP_READ_UNIQUE',
          'SNOOP_CLEAN_SHARED', 'SNOOP_CLEAN_INVALID', 'SNOOP_MAKE_INVALID')

EVENTS = ('CPU_RD', 'CPU_WR') + SNOOPS + ('FILL_DONE', 'DRAIN_DONE')

SNOOP_CODES = {
    'SNOOP_READ_SHARED':   0b000,
    'SNOOP_READ_ONCE':     0b001,
    'SNOOP_READ_UNIQUE':   0b010,
    'SNOOP_CLEAN_SHARED':  0b011,
    'SNOOP_CLEAN_INVALID': 0b100,
    'SNOOP_MAKE_INVALID':  0b101,
    # 0b110/0b111 are not IHI0022 snoop encodings -- the oracle refuses them.
}

CRRESP_WIDTH = 5   # {WU[4], IS[3], PD[2], Err[1], DT[0]}, amber_pkg order

# CPU-miss request classes issued to the fabric/memory side (gem5
# GETS/GETX/UPGRADE; MAS ch02/08 Table 2.8.1 names for Task 12's
# amber_ace_issue).
REQ_READ_SHARED = 'READ_SHARED'
REQ_READ_UNIQUE = 'READ_UNIQUE'
REQ_CLEAN_UNIQUE = 'CLEAN_UNIQUE'

StepResult = namedtuple('StepResult',
                        ['next_state', 'result', 'req', 'crresp', 'pending'])

# ---------------------------------------------------------------------------
# Independent copy of the HAS Table 3.0 snoop decode ({I,S,E,M} x 6 snoops):
# next state and CRRESP in IHI0022 wire order. This is the amber MESI
# interpretation pinned bit-for-bit against amber_pkg.amber_snoop_crresp /
# amber_snoop_next_state by the pkg-pin simulation. Reserved inputs raise
# AmberOracleError here; the pkg's combinational decode contracts those to
# the safe default instead (a snoop responder must never crash) -- both
# halves of that contract are asserted in test_amber_oracle.py.
# ---------------------------------------------------------------------------
_DECODE = {
    'M': {
        'SNOOP_READ_SHARED':   ('S', 0b01101),   # DT+PD+IS: dirty out, downgrade
        'SNOOP_READ_ONCE':     ('I', 0b00101),   # DT+PD: dirty out, invalidate
        'SNOOP_READ_UNIQUE':   ('I', 0b00101),   # DT+PD: dirty out, invalidate
        'SNOOP_CLEAN_SHARED':  ('S', 0b01101),   # DT+PD+IS: writeback, downgrade
        'SNOOP_CLEAN_INVALID': ('I', 0b01101),   # DT+PD+IS: writeback, invalidate
        'SNOOP_MAKE_INVALID':  ('I', 0b00000),   # IHI0022 forbids DT
    },
    'E': {
        'SNOOP_READ_SHARED':   ('S', 0b11001),   # DT+IS+WU: clean out, downgrade
        'SNOOP_READ_ONCE':     ('S', 0b11001),   # DT+IS+WU
        'SNOOP_READ_UNIQUE':   ('I', 0b10001),   # DT+WU: clean out, invalidate
        'SNOOP_CLEAN_SHARED':  ('E', 0b11000),   # no transfer, stays E
        'SNOOP_CLEAN_INVALID': ('I', 0b00000),   # no data ("don't send data")
        'SNOOP_MAKE_INVALID':  ('I', 0b00000),
    },
    'S': {
        'SNOOP_READ_SHARED':   ('S', 0b01000),   # IS: no transfer, stays S
        'SNOOP_READ_ONCE':     ('S', 0b01000),
        'SNOOP_READ_UNIQUE':   ('I', 0b00000),   # no transfer, invalidate
        'SNOOP_CLEAN_SHARED':  ('S', 0b00000),
        'SNOOP_CLEAN_INVALID': ('I', 0b00000),
        'SNOOP_MAKE_INVALID':  ('I', 0b00000),
    },
    'I': {sn: ('I', 0b00000) for sn in SNOOPS},
}


def _decode_next(ref, snoop):
    if ref not in _DECODE:
        raise AmberOracleError(f"reserved line state {ref!r} has no snoop decode")
    if snoop not in SNOOPS:
        raise AmberOracleError(f"reserved/illegal snoop encoding {snoop!r}")
    return _DECODE[ref][snoop][0]


def _decode_crresp(ref, snoop):
    if ref not in _DECODE:
        raise AmberOracleError(f"reserved line state {ref!r} has no snoop decode")
    if snoop not in SNOOPS:
        raise AmberOracleError(f"reserved/illegal snoop encoding {snoop!r}")
    return _DECODE[ref][snoop][1]


def _unreachable(state, event):
    raise AmberOracleError(f"unreachable cell: no {event} can arrive in {state}")


def _stable_step(state, event):
    if event == 'CPU_RD':
        if state == 'I':
            return StepResult('IS', 'MISS', REQ_READ_SHARED, None, None)
        return StepResult(state, 'HIT', None, None, None)
    if event == 'CPU_WR':
        if state == 'I':
            return StepResult('IM', 'MISS', REQ_READ_UNIQUE, None, None)
        if state == 'S':
            return StepResult('SM', 'MISS', REQ_CLEAN_UNIQUE, None, None)
        return StepResult('M', 'HIT', None, None, None)   # E and M promote/keep M
    # Snoop on a stable line: the Table 3.0 decode is the whole answer.
    nxt, crresp = _DECODE[state][event]
    return StepResult(nxt, 'RESPOND', None, crresp, None)


def _is_step(state, event, fill, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if fill not in ('S', 'E'):
        raise AmberOracleError(f"{state} requires fill='S'|'E' (pending-fill "
                               f"install state), got {fill!r}")
    if event == 'FILL_DONE':
        # The fill commits its data and installs the pending post-commit
        # effect (downgrade) or the fill state itself.
        return StepResult(pending or fill, 'COMMIT', None, None, None)
    if event == 'DRAIN_DONE':
        _unreachable(state, event)
    # Snoop during the fill: the pending-fill bypass answers at the
    # POST-FILL state (MAS ch02/02); the snoop's own effect is applied
    # after commit. An invalidate converts the race into IS_I (gem5
    # .sm:1364); a downgrade (E-fill read-shared) is remembered as pending.
    effective = pending or fill
    nxt = _decode_next(effective, event)
    if nxt == 'I':
        return StepResult('IS_I', 'RESPOND', None,
                          _decode_crresp(fill, event), None)
    if nxt == effective:
        return StepResult(state, 'RESPOND', None,
                          _decode_crresp(fill, event), pending)
    # downgrade to S: fill will commit Shared
    return StepResult(state, 'RESPOND', None,
                      _decode_crresp(fill, event), 'S')


def _is_i_step(state, event, fill, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if fill not in ('S', 'E'):
        raise AmberOracleError(f"{state} requires fill='S'|'E', got {fill!r}")
    if event == 'FILL_DONE':
        # gem5 .sm:1390: data commits, the line installs Invalid.
        return StepResult('I', 'COMMIT', None, None, None)
    if event == 'DRAIN_DONE':
        _unreachable(state, event)
    # Repeat snoops answer at the original post-fill state and change
    # nothing: the invalidation already sticks (.sm:1364).
    return StepResult(state, 'RESPOND', None,
                      _decode_crresp(fill, event), pending)


def _im_step(state, event, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if event == 'FILL_DONE':
        # Write merges at commit (D-4); a pending snoop effect lands after.
        return StepResult(pending or 'M', 'COMMIT', None, None, None)
    if event == 'DRAIN_DONE':
        _unreachable(state, event)
    # Snoop during a write-miss fill: answered at the post-fill M state;
    # the post-commit effect chains against any pending effect.
    effective = pending or 'M'
    nxt = _decode_next(effective, event)
    return StepResult(state, 'RESPOND', None, _decode_crresp('M', event),
                      None if nxt == effective else nxt)


def _sm_step(state, event, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if event == 'FILL_DONE':
        return StepResult('M', 'COMMIT', None, None, None)
    if event == 'DRAIN_DONE':
        _unreachable(state, event)
    # The S line stays installed during the upgrade, so snoops answer at S.
    # An exclusive-domain snoop kills the upgrade: gem5 converts SM to a
    # full exclusive fetch (.sm:1526 SM x Inv -> IM).
    nxt = _decode_next('S', event)
    if nxt == 'I':
        return StepResult('IM', 'RESPOND', None,
                          _decode_crresp('S', event), None)
    return StepResult(state, 'RESPOND', None, _decode_crresp('S', event), None)


def _m_i_step(state, event, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if event == 'DRAIN_DONE':
        # WB ack: victim retires, the line is gone (.sm:1315).
        return StepResult('I', 'COMMIT', None, None, None)
    if event == 'FILL_DONE':
        _unreachable(state, event)
    # Snoop hits the in-flight dirty victim: served from the victim buffer
    # (.sm:1352 Fwd_GETX, .sm:1357 Fwd_GETS, .sm:1327 Inv -> SINK_WB_ACK),
    # answered at the M state the victim left in.
    return StepResult('SINK_WB_ACK', 'RESPOND', None,
                      _decode_crresp('M', event), None)


def _sink_wb_ack_step(state, event, pending):
    if event in ('CPU_RD', 'CPU_WR'):
        return StepResult(state, 'STALL', None, None, pending)
    if event == 'DRAIN_DONE':
        return StepResult('I', 'COMMIT', None, None, None)   # .sm:1567
    if event == 'FILL_DONE':
        _unreachable(state, event)
    # Only Inv is defined in gem5 here (.sm:1562); a repeat Fwd_* is an
    # amber derivation -- the victim buffer still holds the line and
    # re-serves it until the WB ack lands.
    return StepResult(state, 'RESPOND', None,
                      _decode_crresp('M', event), None)


_TRANSIENT_STEP = {
    'IS': _is_step,
    'IS_I': _is_i_step,
    'IM': _im_step,
    'SM': _sm_step,
    'M_I': _m_i_step,
    'SINK_WB_ACK': _sink_wb_ack_step,
}


def step(state, event, fill=None, pending=None):
    """Advance one cache line by one event.

    Args:
        state:    one of STATES (the six transients are the D-11 collapse
                  onto amber's blocking CTRL transients).
        event:    one of EVENTS -- cpu rd/wr, the six IHI0022 snoops, or a
                  transaction completion (fill done / drain done).
        fill:     pending-transaction install state: 'S'/'E' for IS/IS_I
                  (which state the read fill will commit), ignored for IM
                  (always M) and illegal elsewhere.
        pending:  post-commit snoop effect in flight ('S' or 'I'), only
                  produced/consumed by the in-fill states; pass back the
                  ``pending`` field of the previous step() when composing a
                  sequence.

    Returns:
        StepResult(next_state, result, req, crresp, pending):
            result: HIT | MISS | STALL | COMMIT | RESPOND
            req:    READ_SHARED | READ_UNIQUE | CLEAN_UNIQUE on a cpu MISS,
                    else None
            crresp: 5-bit IHI0022 wire order on RESPOND, else None
            pending: effect to feed into the next step(), else None

    Raises:
        AmberOracleError: reserved/illegal encodings and unreachable cells
            land in ERROR (amber_control's sticky CTRL_ERROR contract),
            never in a guessed transition.
    """
    if state not in STATES:
        raise AmberOracleError(f"unknown/reserved state {state!r}")
    if event not in EVENTS:
        raise AmberOracleError(f"unknown/reserved event {snoop_repr(event)}")
    if pending not in (None, 'S', 'I'):
        raise AmberOracleError(f"bad pending effect {pending!r}")

    if state in STABLE_STATES:
        if event in ('FILL_DONE', 'DRAIN_DONE'):
            _unreachable(state, event)
        return _stable_step(state, event)

    if state == 'IM':
        if fill not in (None, 'M'):
            raise AmberOracleError(f"IM installs M; fill={fill!r} is meaningless")
        return _im_step(state, event, pending)

    if state == 'SM':
        if fill is not None:
            raise AmberOracleError("SM is an upgrade (no fill data); fill not applicable")
        return _sm_step(state, event, pending)

    if state in ('M_I', 'SINK_WB_ACK'):
        if fill is not None:
            raise AmberOracleError(f"{state} has no fill; fill not applicable")
        return _TRANSIENT_STEP[state](state, event, pending)

    # IS / IS_I
    return _TRANSIENT_STEP[state](state, event, fill, pending)


def snoop_repr(event):
    """Helper for error strings: keep ints printable."""
    return f"0b{event:03b}" if isinstance(event, int) else repr(event)
