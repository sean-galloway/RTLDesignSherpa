# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: bin/kmaps/__init__.py
# Purpose: Shared contract-table / K-map machinery for signal-contract workbooks
#
# Promoted here by TOOLING-KMAP step 5. Both the stream and pumice generators
# carried a private copy of this code; the step was deliberately sequenced
# AFTER items 1-4 so one implementation receives the improvements rather than
# two drifting ones.
#
# What is shared (this package) vs what stays per-component:
#   shared      minimiser, cell rendering, the contract-table writer, the
#               citation gate.
#   component   its RTL path constants, its CITES registry, its build_* sheet
#               builders, and its own output path. Those are the parts that
#               describe a specific block and must not be centralised.
#
# Canonical methodology: bin/SIGNAL_CONTRACTS_KMAPS.md
# Rationale + the required three-part form: vault/handbook/design/signal-contracts-and-kmaps.md
"""Shared signal-contract / K-map emitter machinery."""

from .citations import verify_citations
from .minimize import norm_sop, qm_minimize, cube_str, sop_str
from .writer import KmapWriter, new_kmap_sheet, contract_sheet, CONTRACT_HDRS

__all__ = [
    "verify_citations",
    "norm_sop", "qm_minimize", "cube_str", "sop_str",
    "KmapWriter", "new_kmap_sheet", "contract_sheet", "CONTRACT_HDRS",
]
