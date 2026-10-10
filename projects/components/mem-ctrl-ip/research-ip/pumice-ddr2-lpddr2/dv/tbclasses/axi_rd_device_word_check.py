# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""AXI read-data device-word ORDER assertion.

Encodes the `s_axi_rdata` contract from `docs/pumice_signal_contracts.xlsx`
(Sheet 1): every AXI R beat must present the DRAM data in ASCENDING device-word
order. For a narrow (x16) device each beat = beat_bytes/device_word_bytes
device-words; a de-interleave bug in the read path shifts, duplicates, or drops
device-words within the beat while the beat COUNT stays correct — so a beat-level
compare only says "wrong", this says WHICH device-word and HOW (the on-silicon
signatures: `0x..a5a0` = dropped, `phase1==phase0` = duplicated/shifted).

Pure functions (no cocotb/dut dependency) so they unit-test directly and are
reusable from any TB that has a golden reference.
"""
from typing import Callable, List, Optional, Dict


def check_beat_device_words(byte_addr: int, golden_int: int, actual_int: int,
                            beat_bytes: int, device_word_bytes: int) -> Optional[Dict]:
    """Compare one AXI R beat against golden at device-word granularity.

    Returns None if the beat matches. Otherwise a dict that LOCALIZES every bad
    device-word slot and classifies the error:
      - "zero"        : device-word dropped (all-zero where data expected)
      - "shift@<k>"   : observed value equals golden device-word slot k (the
                        de-interleave picked the wrong slot -> shift/duplication)
      - "unrelated"   : neither (genuinely corrupt / analog)
    """
    if device_word_bytes <= 0 or beat_bytes % device_word_bytes != 0:
        device_word_bytes = beat_bytes                  # fall back: whole beat = 1 slot
    n = beat_bytes // device_word_bytes
    bits = device_word_bytes * 8
    m = (1 << bits) - 1
    g = [(golden_int >> (k * bits)) & m for k in range(n)]
    a = [(actual_int >> (k * bits)) & m for k in range(n)]
    if a == g:
        return None
    hexw = device_word_bytes * 2
    bad = []
    for k in range(n):
        if a[k] == g[k]:
            continue
        if a[k] == 0:
            cls = "zero (device-word dropped)"
        elif a[k] in g:
            cls = f"shift@{g.index(a[k])} (got device-word slot {g.index(a[k])}'s value)"
        else:
            cls = "unrelated (corrupt/analog)"
        bad.append({"slot": k, "expected": f"0x{g[k]:0{hexw}x}",
                    "actual": f"0x{a[k]:0{hexw}x}", "class": cls})
    return {"byte_addr": f"0x{byte_addr:x}", "n_slots": n,
            "device_word_bytes": device_word_bytes,
            "golden": [f"0x{x:0{hexw}x}" for x in g],
            "actual": [f"0x{x:0{hexw}x}" for x in a],
            "bad_slots": bad}


def check_read_device_word_order(snoop: List, golden_read: Callable[[int, int], int],
                                 beat_bytes: int, device_word_bytes: int) -> List[Dict]:
    """Run the device-word contract over a list of snooped R beats.

    snoop        : iterable of (byte_addr, actual_int, rid) — one per AXI R beat.
    golden_read  : fn(byte_addr, beat_bytes) -> int, little-endian golden data.
    Returns a list of violation dicts (empty => contract holds for every beat).
    """
    out = []
    for byte_addr, actual_int, rid in snoop:
        golden_int = golden_read(byte_addr, beat_bytes)
        v = check_beat_device_words(byte_addr, golden_int, actual_int,
                                    beat_bytes, device_word_bytes)
        if v is not None:
            v["rid"] = rid
            out.append(v)
    return out


def format_violations(violations: List[Dict], limit: int = 8) -> str:
    if not violations:
        return "device-word read order: OK"
    lines = [f"device-word read-order CONTRACT VIOLATED ({len(violations)} beat(s)):"]
    for v in violations[:limit]:
        lines.append(f"  @{v['byte_addr']} rid={v.get('rid')} "
                     f"golden={v['golden']} actual={v['actual']}")
        for b in v["bad_slots"]:
            lines.append(f"      slot {b['slot']}: exp {b['expected']} "
                         f"got {b['actual']} -> {b['class']}")
    if len(violations) > limit:
        lines.append(f"  ... +{len(violations) - limit} more")
    return "\n".join(lines)
