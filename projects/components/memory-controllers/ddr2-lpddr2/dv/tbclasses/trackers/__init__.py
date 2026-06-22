# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Passive trackers for the ddr2-lpddr2 controller's internal FUBs.

Each tracker:
  * Attaches as `cocotb.start_soon(tracker.run())`.
  * Snoops the FUB's external outputs every clock — never drives.
  * Emits typed `TrackerEvent` records into a single unified `.events`
    deque per tracker.
  * Renders each event as a markdown-table row via `to_md_row()` so the
    output across all trackers stacks into one searchable table.

Available trackers (9 total):
    SchedulerTracker        — issued cmd_* stream, evt_* bank events, grants
    RefreshTracker          — refresh req/grant/pending; JEDEC tREFI compliance
    XBankTimersTracker      — per-(rank, bank) state, row open/close, residency
    PagePredictorTracker    — predictor counter MSB transitions, ACT input log
    DfiCmdFormatterTracker  — JEDEC ras/cas/we_n decode + ODT/CKE changes
    PowerdownTracker        — pdn_req / per-rank CKE residency
    InitSequencerTracker    — init duration, MR-write log, ZQCL pulses
    WrBeatSequencerTracker  — multi-outstanding lifecycle + PULL/DRIVE overlap
    RdClAlignerTracker      — multi-outstanding lifecycle + EN/CAPTURE/EMIT overlap
"""

from ._base import TrackerEvent, md_header, dump_md_unified

from .scheduler_tracker        import SchedulerTracker
from .refresh_tracker          import RefreshTracker
from .xbank_timers_tracker     import XBankTimersTracker
from .page_predictor_tracker   import PagePredictorTracker
from .dfi_cmd_formatter_tracker import DfiCmdFormatterTracker
from .powerdown_tracker        import PowerdownTracker
from .init_sequencer_tracker   import InitSequencerTracker
from .wr_beat_sequencer_tracker import WrBeatSequencerTracker
from .rd_cl_aligner_tracker    import RdClAlignerTracker

__all__ = [
    # base
    "TrackerEvent", "md_header", "dump_md_unified",
    # trackers
    "SchedulerTracker", "RefreshTracker",
    "XBankTimersTracker", "PagePredictorTracker",
    "DfiCmdFormatterTracker", "PowerdownTracker", "InitSequencerTracker",
    "WrBeatSequencerTracker", "RdClAlignerTracker",
]
