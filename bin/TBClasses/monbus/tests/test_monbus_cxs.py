# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# PROTOCOL_CXS decode: the Python side must mirror the SV packages exactly.
# Re-parses ocelus_common_pkg.sv and ocelus_cxs_pkg.sv, so an SV edit that
# is not carried into monbus_types.py fails here rather than as a mislabelled
# packet in some later simulation log.

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[3]))  # repo/bin
REPO = HERE.parents[4]

from TBClasses.monbus import (  # noqa: E402
    CXSChannelCode, CXSCompletionCode, CXSCreditCode, CXSErrorCode, CXSStreamCode,
    CXSTimeoutCode, PktType, ProtocolType, create_monitor_packet, get_event_code_name,
    parse,
)

SV_PKG = REPO / "rtl/amba/includes/ocelus_cxs_pkg.sv"
SV_COMMON = REPO / "rtl/amba/includes/ocelus_common_pkg.sv"

ENUMS = {
    'cxs_error_code_t': CXSErrorCode, 'cxs_timeout_code_t': CXSTimeoutCode,
    'cxs_completion_code_t': CXSCompletionCode, 'cxs_credit_code_t': CXSCreditCode,
    'cxs_channel_code_t': CXSChannelCode, 'cxs_stream_code_t': CXSStreamCode,
}


def _sv_enums(path):
    text = path.read_text()
    out = {}
    for m in re.finditer(r'typedef enum logic \[\d+:0\] \{(.*?)\}\s*(\w+);', text, re.S):
        out[m.group(2)] = {e.group(1): int(e.group(2), 16)
                           for e in re.finditer(r"(\w+)\s*=\s*\d+'h([0-9A-Fa-f]+)", m.group(1))}
    return out


def test_python_enums_match_sv_package():
    sv = _sv_enums(SV_PKG)
    assert set(sv) == set(ENUMS)
    for t, cls in ENUMS.items():
        assert {m.name: m.value for m in cls} == sv[t], t


def test_protocol_code_matches_common_pkg():
    sv = _sv_enums(SV_COMMON)['protocol_type_t']
    assert sv['PROTOCOL_CXS'] == ProtocolType.PROTOCOL_CXS == 0x6
    # every Python protocol is in the SV enum with the same value
    for m in ProtocolType:
        assert sv[m.name] == m.value


def test_event_dropped_shares_the_lite_code():
    assert CXSErrorCode.CXS_ERR_EVENT_DROPPED == 0xE


def test_cxs_packet_decodes_by_name():
    raw = create_monitor_packet(PktType.PktTypeStream, ProtocolType.PROTOCOL_CXS,
                                CXSStreamCode.CXS_STREAM_LINK_UP, 0, 0x0A, 0x00C0, 0x1234)
    pkt = parse(raw)
    assert pkt.protocol == ProtocolType.PROTOCOL_CXS
    assert get_event_code_name(ProtocolType.PROTOCOL_CXS, PktType.PktTypeStream,
                               CXSStreamCode.CXS_STREAM_LINK_UP) == 'CXS_STREAM_LINK_UP'
