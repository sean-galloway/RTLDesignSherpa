# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Parity gate: andesite_axi4_layer is a byte-faithful rename-carry of scoria_axi4_layer.

The andesite AXI4 macro layer was born in TASK-016 t7 by renaming scoria's
macro block (module name, sub-FUB instantiation names, package import, and
scoria-referencing comments). No logic, parameter, or port-name changes are
allowed. This gate catches the moment the file diverges from that contract.

When it fails, the instruction is: either the rename-carry contract still
holds and the diff is unintentional, or the layer has acquired andesite-specific
behaviour and needs its own unit test plus a docs/ hierarchy update.
"""

from pathlib import Path

import pytest

from TBClasses.shared.utilities import get_repo_root
import re  # Phase 2 Task 2: BG-delta strip in the parity gate

_REPO = Path(get_repo_root())
_ANDESITE = (
    _REPO
    / "projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_axi4_layer.sv"
)
_SCORIA = (
    _REPO
    / "projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_axi4_layer.sv"
)


def _as_renamed_scoria(text: str) -> str:
    """Apply the TASK-016 t7 rename map: scoria -> andesite everywhere."""
    return text.replace("scoria", "andesite")


def test_andesite_scoria_axi4_logic_parity():
    assert _SCORIA.is_file(), f"scoria source {_SCORIA} is missing"
    assert _ANDESITE.is_file(), f"andesite source {_ANDESITE} is missing"

    scoria_text = _SCORIA.read_text()
    andesite_text = _ANDESITE.read_text()

    # Phase 2 (2026-10-10, Task 2): andesite's axi4 layer gained the intake
    # BG parameterization (.BG_WIDTH(2), .HAS_BG(1) on both mc_{wr,rd}_intake
    # instantiations — the DDR4 bank-group address mapping). That is a
    # deliberate, enumerable divergence from scoria's layer; strip those two
    # connection lines before comparing so the parity gate keeps guarding
    # everything else. (Both files retire when mc_axi4_layer lands in
    # Phase 2 Task 3.)
    andesite_text = "\n".join(
        ln for ln in andesite_text.splitlines()
        if not re.search(r"\.(BG_WIDTH|HAS_BG)\s*\(", ln)
    )

    if andesite_text.rstrip("\n") == _as_renamed_scoria(scoria_text).rstrip("\n"):
        return

    import difflib

    diff = list(
        difflib.unified_diff(
            _as_renamed_scoria(scoria_text).splitlines(),
            andesite_text.splitlines(),
            fromfile="scoria_axi4_layer (renamed)",
            tofile="andesite_axi4_layer",
            lineterm="",
            n=1,
        )
    )
    pytest.fail(
        f"andesite_axi4_layer.sv is no longer a byte-faithful scoria rename-carry "
        f"({len(diff)} diff lines). Either revert the unintended drift or, if the "
        f"change is intentional, write an andesite unit test for the layer and "
        f"remove this rename-parity expectation.\n\n"
        + "\n".join(diff[:80])
    )
