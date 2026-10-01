# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Parity gate: the scoria FUBs that are still pumice's logic, unchanged.

Seven of scoria's FUBs were ported from pumice and, measured, differ from the
original ONLY in comments and in the names of the modules they instantiate.
Their logic is byte-identical to code that pumice's suite exercises on every
regression.

That is worth recording rather than re-testing. A port of pumice's seven test
files would mostly re-prove what pumice already proves, and would do it against
a second copy that drifts -- while the thing actually worth catching is the
moment one of these files STOPS being pumice's logic. A DDR3 change landing in
`scoria_rd_intake` with no test of its own is exactly the gap a ported-and-stale
suite hides.

So this gate asserts the identity instead. When it fails, the message is the
instruction: that module is no longer pumice's, so it needs its own unit test,
and its row comes out of the table below.

What counts as a difference: any non-comment, non-blank line, once the family
prefix (`scoria_` / `pumice_`) is stripped from both sides. Comment edits are
free -- attribution lines and cross-references legitimately differ between the
two trees, and a gate that fires on those gets switched off.

NOT a claim that these modules are correct. It is a claim about WHERE their
coverage lives: in pumice's dv/tests, over the same logic. The modules with
scoria-specific behaviour (mode_register, zq_ctrl, wrlvl_ifc, init_sequencer,
dfi_cmd_formatter, cmd_arbiter, page_policy, ...) are not in this table and
have their own tests.
"""

from pathlib import Path

import pytest

from TBClasses.shared.utilities import get_repo_root

# Git-based rather than a parent count: the count was wrong by one (this file
# sits six directories below `projects/`, not below the root) and the failure
# read as "every ported module is missing".
_REPO = Path(get_repo_root())
_SC = _REPO / "projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub"
_PU = _REPO / "projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/rtl/fub"

# scoria file  ->  pumice file. The pumice tree names some of these with the
# `pumice_` prefix and some without, which is why this is a table and not a
# format string.
PORTED = {
    "scoria_rd_cmd_cam.sv":     "pumice_rd_cmd_cam.sv",
    "scoria_wr_data_cam.sv":    "pumice_wr_data_cam.sv",
    "scoria_rd_intake.sv":      "pumice_rd_intake.sv",
    "scoria_wr_intake.sv":      "pumice_wr_intake.sv",
    "scoria_rd_return_ring.sv": "pumice_rd_return_ring.sv",
    "scoria_dfi_cdc.sv":        "pumice_dfi_cdc.sv",
    "scoria_bank_timers.sv":    "pumice_bank_timers.sv",
}

# Where each one's coverage actually lives, for the failure message.
PUMICE_TEST = {
    "scoria_rd_cmd_cam.sv":     "test_pumice_rd_cmd_cam.py",
    "scoria_wr_data_cam.sv":    "test_pumice_wr_data_cam.py",
    "scoria_rd_intake.sv":      "test_pumice_rd_intake.py",
    "scoria_wr_intake.sv":      "test_pumice_wr_intake.py",
    "scoria_rd_return_ring.sv": "test_pumice_rd_return_ring.py",
    "scoria_dfi_cdc.sv":        "test_pumice_dfi_cdc.py",
    "scoria_bank_timers.sv":    "test_pumice_bank_timers.py",
}

# Canonicalisation: STRIP the family prefix from both sides rather than
# rewriting one into the other. Rewriting pumice -> scoria also rewrote the
# INSTANCE labels, which are identical in both trees (`u_addr_mapper`), and the
# gate then reported two intakes as diverged over a name it had changed itself.
_PREFIXES = ("scoria_", "pumice_")


def _logic_lines(text):
    """Non-comment, non-blank lines, with the family prefix stripped.

    Comments are dropped rather than compared: cross-references and attribution
    lines differ legitimately between the trees, and a gate that fires on a
    comment edit is a gate someone turns off.
    """
    for pfx in _PREFIXES:
        text = text.replace(pfx, "")
    out = []
    in_block = False
    for raw in text.splitlines():
        line = raw
        if in_block:
            if "*/" in line:
                line = line.split("*/", 1)[1]
                in_block = False
            else:
                continue
        if "/*" in line:
            head, rest = line.split("/*", 1)
            line = head
            in_block = "*/" not in rest
            if not in_block:
                line += rest.split("*/", 1)[1]
        line = line.split("//", 1)[0].rstrip()
        if line.strip():
            out.append(line.strip())
    return out


@pytest.mark.parametrize("scoria_file", sorted(PORTED))
def test_scoria_pumice_logic_parity(scoria_file):
    pumice_file = PORTED[scoria_file]
    sp, pp = _SC / scoria_file, _PU / pumice_file
    assert sp.is_file(), f"{sp} is missing"
    assert pp.is_file(), (
        f"{pp} is missing -- pumice's original is gone, so this gate can no "
        f"longer stand in for {scoria_file}'s coverage. Write a scoria unit "
        f"test for it and drop its row from PORTED.")

    s_lines = _logic_lines(sp.read_text())
    p_lines = _logic_lines(pp.read_text())

    if s_lines == p_lines:
        return

    import difflib
    diff = list(difflib.unified_diff(p_lines, s_lines,
                                     fromfile=f"pumice/{pumice_file}",
                                     tofile=f"scoria/{scoria_file}",
                                     lineterm="", n=1))
    pytest.fail(
        f"{scoria_file} is no longer pumice's logic ({len(diff)} diff lines). "
        f"That is allowed -- but its coverage was living in pumice's "
        f"{PUMICE_TEST[scoria_file]}, over the OLD code, and does not cover "
        f"whatever changed. Write a scoria unit test for this module and "
        f"remove its row from PORTED in this file.\n\n"
        + "\n".join(diff[:60]))


def test_ported_table_covers_no_scoria_specific_module():
    """A module with its own scoria test must not also be in this table.

    Both at once is the drifting-copy state this gate exists to prevent: the
    parity check would quietly forbid the scoria-specific change the unit test
    was written for.
    """
    tests = Path(__file__).parent
    clash = [f for f in PORTED
             if (tests / f"test_{f.replace('.sv', '.py')}").is_file()]
    assert clash == [], (
        f"{clash} have their own scoria unit tests AND a parity row. Pick one: "
        f"if the module has diverged, drop the row; if it has not, the unit "
        f"test is testing pumice's logic in a second place.")
