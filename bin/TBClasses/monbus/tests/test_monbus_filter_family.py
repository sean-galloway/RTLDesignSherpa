# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# The group filter family: the Python filter_family() must give the same
# answer as ocelus_common_pkg::filter_family() for all sixteen protocol
# values. Re-parses the SV case so a protocol added on one side and not the
# other fails here, not as a capture that silently loses a protocol.

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[3]))  # repo/bin
REPO = HERE.parents[4]

from TBClasses.monbus import FilterFamily, ProtocolType, filter_family  # noqa: E402

SV_COMMON = REPO / "rtl/amba/includes/ocelus_common_pkg.sv"


def _sv_filter_family():
    """{protocol value: family value} from the SV function body."""
    text = SV_COMMON.read_text()
    enum = {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"(PROTOCOL_\w+)\s*=\s*4'h([0-9A-Fa-f])", text)}
    body = re.search(r"function automatic filter_family_t filter_family\(.*?endfunction", text, re.S).group(0)
    fam = {'FILTER_AXI': 0, 'FILTER_STREAM': 1, 'FILTER_CORE': 2}
    default = fam[re.search(r"default:\s*return (FILTER_\w+);", body).group(1)]
    out = {v: default for v in range(16)}
    for m in re.finditer(r"^\s*((?:PROTOCOL_\w+\s*,?\s*)+):\s*return (FILTER_\w+);", body, re.M):
        for name in re.findall(r"PROTOCOL_\w+", m.group(1)):
            out[enum[name]] = fam[m.group(2)]
    return out


def test_python_matches_sv_for_every_value():
    sv = _sv_filter_family()
    for v in range(16):
        assert int(filter_family(v)) == sv[v], f"protocol {v:#x}: python {filter_family(v).name}, sv {sv[v]}"


def test_no_protocol_is_dropped_outright():
    # every named protocol lands in a family that has masks
    for p in ProtocolType:
        assert filter_family(p) in (FilterFamily.FILTER_AXI, FilterFamily.FILTER_STREAM, FilterFamily.FILTER_CORE)


def test_families_by_packet_type_set():
    assert filter_family(ProtocolType.PROTOCOL_CHI) == FilterFamily.FILTER_STREAM
    assert filter_family(ProtocolType.PROTOCOL_CXS) == FilterFamily.FILTER_STREAM
    assert filter_family(ProtocolType.PROTOCOL_APB) == FilterFamily.FILTER_AXI
    assert filter_family(ProtocolType.PROTOCOL_WB) == FilterFamily.FILTER_AXI
    assert filter_family(ProtocolType.PROTOCOL_CORE) == FilterFamily.FILTER_CORE
    assert filter_family(0xF) == FilterFamily.FILTER_AXI
