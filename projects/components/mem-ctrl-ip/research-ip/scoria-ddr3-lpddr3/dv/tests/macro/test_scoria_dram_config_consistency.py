# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""The operating point has three views; this gate keeps them one table.

`scoria_dram_configs` serves two consumers from one set of datasheet
nanoseconds, and they count in different units:

    the CONTROLLER's CSRs       <- prog[]     MC cycles, spacing - 1
    the DFI SLAVE's JEDEC model <- jedec_ns() nanoseconds, which the DV
                                              framework converts to CK cycles

If those ever disagree, the DFI slave polices a part the controller was not
programmed for, and the disagreement surfaces as a timing violation that looks
exactly like an RTL bug. That failure would be expensive and confusing, and it
is cheap to prevent: convert the framework's CK cycles back through DFI_RATE
and require the MC spacing to match.

No simulation. It is arithmetic over the config module and the framework's own
loader, which is the point -- the conversion that matters happens in the
framework (from the datasheet figure), so this checks that my MC-cycle view of
the same figure agrees with it rather than checking my arithmetic against
itself.
"""

import math
import os
import sys

import pytest

_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV not in sys.path:
    sys.path.insert(0, _DV)

from tbclasses.scoria_dram_configs import (  # noqa: E402
    dram_config, jedec_ns, describe,
)

# (our key, the framework's attribute). tCCD has no JedecTimings field and
# tREFI is a deadline rather than a spacing, so neither is cross-checkable
# here; both are covered by the FUB suites that measure them directly.
_PAIRS = [
    ('tRCD', 'tRCD_cycles'),
    ('tRP',  'tRP_cycles'),
    ('tRAS', 'tRAS_min_cycles'),
    ('tRC',  'tRC_cycles'),
    ('tWR',  'tWR_cycles'),
    ('tWTR', 'tWTR_cycles'),
    ('tRTP', 'tRTP_cycles'),
    ('tRRD', 'tRRD_cycles'),
    ('tFAW', 'tFAW_cycles'),
    ('tRFC', 'tRFC_cycles'),
]


def _timings():
    from CocoTBFramework.components.dfi.jedec_timings import timings_from_params
    return timings_from_params(**jedec_ns())


def test_scoria_dram_config_framework_accepts_the_table():
    """The framework must take the point as-is, with no hand-held conversion.

    It rejects a value without an explicit `_ns` / `_ck` suffix, listing the
    offenders -- which is how this module learned to hand it nanoseconds
    instead of cycle counts of its own.
    """
    t = _timings()
    _, _, meta = dram_config()
    assert t.tCK_ns == meta['ck_ns']
    assert t.BL == meta['dram_bl']
    assert t.CL > 0 and t.CWL > 0


@pytest.mark.parametrize("key, attr", _PAIRS)
def test_scoria_dram_config_views_agree(key, attr):
    """CK cycles / DFI_RATE must equal the MC-cycle spacing, window by window."""
    spacing, _, meta = dram_config()
    ratio = meta['mc_ns'] / meta['ck_ns']
    assert ratio == meta['dfi_rate'], (
        f"the MC/CK ratio is {ratio} but DFI_RATE is {meta['dfi_rate']}; the "
        f"operating point is internally inconsistent before any timing is "
        f"even converted")
    ck = getattr(_timings(), attr)
    mc = math.ceil(ck / ratio)
    assert mc == spacing[key], (
        f"{key}: the framework converted the datasheet ns to {ck} CK cycles, "
        f"which is {mc} MC cycles at DFI_RATE {meta['dfi_rate']}, but this "
        f"module's spacing table says {spacing[key]}. One of the two views is "
        f"wrong, and the DFI slave would then police a part the controller is "
        f"not programmed for.\n\n{describe()}")


def test_prog_is_spacing_minus_one():
    """The N+1 convention, asserted where it is derived.

    scoria_csr.rdl: "MC cycles to block; spacing enforced is N+1". Measured in
    test_scoria_bank_timer.py and test_scoria_global_timers.py. Programming the
    datasheet cycle count directly over-spaces every window by one; subtracting
    one twice violates the part.
    """
    spacing, prog, _ = dram_config()
    for k in spacing:
        if k == 'tREFI':
            assert prog[k] == spacing[k], (
                "tREFI is a deadline, not a minimum: it must NOT be N+1 "
                "adjusted")
            continue
        assert prog[k] == spacing[k] - 1, (
            f"{k}: programmed {prog[k]} against spacing {spacing[k]}")
        assert prog[k] >= 0, f"{k}: negative programmed value {prog[k]}"
