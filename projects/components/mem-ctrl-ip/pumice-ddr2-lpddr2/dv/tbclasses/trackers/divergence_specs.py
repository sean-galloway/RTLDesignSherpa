# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Central per-FUB event-parity contracts consumed by divergence.py.
#
# Each contract encodes: "for every ACCEPT event at slot S, we must
# see MATCH_EVENT emitted N times at the same slot, where N is either
# fixed or extracted from the accept event's data field."
#
# Adding a contract here automatically strengthens every test whose
# teardown calls assert_no_divergence(fub_key, ...) — no per-test
# change required.

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Union


@dataclass(frozen=True)
class ParityContract:
    """Per-slot event-count parity between an ACCEPT event and a
    MATCH event.

    Attributes:
        name:               short label for error messages
        accept_event:       tracker event that opens a slot obligation
                            (e.g. OP_ACCEPT). One event = one obligation.
        match_event:        event that satisfies the obligation
                            (e.g. BEAT_WE, B_COMPLETE)
        expected_per_accept:
            int:      fixed number of match events per accept.
            str:      key into the accept event's data_dict — the
                      value at that key is the expected match count
                      (e.g. 'len' — one match event per beat).
            callable: takes accept.data_dict, returns expected count.
    """
    name: str
    accept_event: str
    match_event: str
    expected_per_accept: Union[int, str, Callable[[dict], int]] = 1


# ---------------------------------------------------------------------------
# Per-FUB contracts
# ---------------------------------------------------------------------------


DIVERGENCE_SPECS: dict = {

    # rd_cl_aligner: every OP_ACCEPT (with len=L) must produce L BEAT_WE
    # events at the same slot. #31 was exactly this class of divergence:
    # slots got OP_ACCEPT but 0 BEAT_WE.
    "rd_cl_aligner": [
        ParityContract(
            name="op_accept_beats_match_len",
            accept_event="OP_ACCEPT",
            match_event="BEAT_WE",
            expected_per_accept="len",
        ),
    ],

    # wr_beat_sequencer: every OP_ACCEPT must produce exactly one
    # B_COMPLETE at the same slot. #32 (the WR-side mirror) was exactly
    # this class of divergence: slots got OP_ACCEPT but 0 B_COMPLETE.
    "wr_beat_sequencer": [
        ParityContract(
            name="op_accept_b_complete_1to1",
            accept_event="OP_ACCEPT",
            match_event="B_COMPLETE",
            expected_per_accept=1,
        ),
    ],
}
