# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Verilator configuration shared by the cocotb runs and the FPGA lint flow.

FIELD_COMBO_VLT is make/verilator_vendor.vlt: pass it in compile_args, never
-Wno-MULTIDRIVEN. It switches MULTIDRIVEN off for exactly one proven-legal
pattern -- PeakRDL's per-member writes to its `field_combo` struct -- and
leaves every other multi-driven signal a build failure (a blanket waiver hid
bridge BUG-022 in two board-green bitstreams). The rationale is the handbook's
fpga/cmn-infra/build-flows.md, "MULTIDRIVEN is not waived".
"""
from pathlib import Path

_REPO = Path(__file__).resolve().parents[3]
FIELD_COMBO_VLT = str(_REPO / 'make' / 'verilator_vendor.vlt')
