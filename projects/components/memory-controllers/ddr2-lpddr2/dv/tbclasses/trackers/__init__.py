# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Passive trackers for the ddr2-lpddr2 controller's internal FUBs.

These classes attach as cocotb background coroutines and snoop the
external outputs of a FUB without driving anything. They decode the
bus activity into typed event records that the testbench can inspect
after the simulation completes — useful for debug, coverage,
compliance checks, and performance measurements.

Available trackers:
    SchedulerTracker — issued cmd_* stream, bank events, grants
    RefreshTracker   — refresh request / grant / pending; JEDEC tREFI compliance
"""

from .scheduler_tracker import (
    SchedulerTracker, CmdEvent, BankEvent, GrantEvent, IssuedEvent,
)
from .refresh_tracker import (
    RefreshTracker, RefreshReqEdge, RefreshGrant, PendingSample,
)

__all__ = [
    "SchedulerTracker", "CmdEvent", "BankEvent", "GrantEvent", "IssuedEvent",
    "RefreshTracker", "RefreshReqEdge", "RefreshGrant", "PendingSample",
]
