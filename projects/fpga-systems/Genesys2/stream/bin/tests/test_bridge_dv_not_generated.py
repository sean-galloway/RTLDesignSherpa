# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_bridge_dv_not_generated
# Purpose: the bridge PREBUILD must not overwrite hand-maintained DV collateral
#
# Subsystem: fpga-systems/Genesys2/stream

"""`regen_bridges.sh` regenerates bridge RTL. It must not write DV.

The script is the PREBUILD for `make bitstream`, so whatever it writes is
rewritten every time anyone builds a bitstream. It used to pass
`--generate-tests`, and that quietly reverted three separate rounds of
committed fixes to `rtl/bridges/dv/` (33ac787e, 90bca4c1, bd79af49).

What came back each time was worse than a stale file. The generator derived a
dotted import from the output directory, and this area lives under
`projects/fpga-systems/` -- the hyphen makes
`from projects.fpga-systems.Genesys2... import X` a SyntaxError. The five
bridge tests were therefore not failing; they could not be COLLECTED, so they
were absent from the report entirely and the suite looked green without them.

The generator no longer emits that import. But the DV files also carry things a
shared generator cannot know -- the TEST_LEVEL scaling from
`bin/stream_levels.py`, and the `-Wno-MULTIDRIVEN` the generated PeakRDL CSR
needs to compile at all -- so ownership of them is the fix, not just a working
import. This test holds that line.
"""

import ast
import os
import re

import pytest

_AREA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     os.pardir, os.pardir))
_REGEN = os.path.join(_AREA, 'bin', 'regen_bridges.sh')
_DV = os.path.join(_AREA, 'rtl', 'bridges', 'dv')

# Flags that make the generator emit DV collateral. Any one of them puts the
# script back in the business of overwriting these files.
_TEST_GEN_FLAGS = ('--generate-tests', '--output-tb', '--output-test')


def _regen_source():
    with open(_REGEN, encoding='utf-8') as fh:
        return fh.read()


def _invocation_lines(text):
    """The generator invocation only -- comments explain the flags by name."""
    return [ln for ln in text.splitlines() if not ln.lstrip().startswith('#')]


@pytest.mark.parametrize('flag', _TEST_GEN_FLAGS)
def test_regen_does_not_generate_dv(flag):
    body = '\n'.join(_invocation_lines(_regen_source()))
    assert flag not in body, (
        f"regen_bridges.sh passes {flag}. It is the PREBUILD for "
        f"`make bitstream`, so this silently overwrites hand-maintained files "
        f"under rtl/bridges/dv/ on every build. See the header of that script."
    )


def test_regen_declares_no_dv_output_dir():
    """No DV path may be wired up as an output, flags or not."""
    body = '\n'.join(_invocation_lines(_regen_source()))
    for var in ('TB_OUT', 'TEST_OUT'):
        assert var not in body, (
            f"regen_bridges.sh still defines {var}. The DV directories are not "
            f"outputs of this script."
        )
    assert not re.search(r'^\s*mkdir[^\n#]*\bdv\b', body, re.MULTILINE), \
        "regen_bridges.sh creates a dv/ directory -- it does not own one."


def _dv_files():
    out = []
    for sub in ('tests', 'tbclasses'):
        d = os.path.join(_DV, sub)
        if not os.path.isdir(d):
            continue
        out += [os.path.join(d, f) for f in sorted(os.listdir(d))
                if f.endswith('.py')]
    return out


@pytest.mark.parametrize('path', _dv_files(),
                         ids=lambda p: os.path.basename(p))
def test_dv_file_parses(path):
    """The regression that hid five tests for months was a parse failure.

    An uncollectable test does not appear in the report as a failure. It does
    not appear at all, which reads exactly like a suite that passed.
    """
    with open(path, encoding='utf-8') as fh:
        src = fh.read()
    try:
        ast.parse(src, filename=path)
    except SyntaxError as exc:
        pytest.fail(f"{os.path.basename(path)} does not parse: "
                    f"line {exc.lineno}: {exc.text!r}")


def test_there_are_dv_files_to_check():
    """A guard over an empty list passes by saying nothing."""
    assert _dv_files(), f"no DV files found under {_DV} -- the guard is vacuous"
