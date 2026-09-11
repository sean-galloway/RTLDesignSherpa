#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Validate the WaveJSON in design/waves/.

WaveDrom fails SILENTLY on a malformed diagram: a `data` list shorter than the
number of data slots in its `wave` string just leaves later buses blank, and
rows of unequal length simply render ragged. Neither looks like an error, so a
wrong diagram survives review. This checks the two mechanical properties.

    python3 design/check_waves.py     # exit 1 on a bad diagram
"""
from __future__ import annotations
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WAVES = os.path.join(HERE, "waves")
# characters that open a NEW data slot in a wave string
DATA_CHARS = set("23456789=")


def _rows(sig, out):
    for item in sig:
        if isinstance(item, dict) and "wave" in item:
            out.append(item)
        elif isinstance(item, list):
            _rows(item, out)
    return out


def _groups(sig, out):
    for item in sig:
        if isinstance(item, list):
            if item and isinstance(item[0], str):
                out.append(item[0])
            _groups(item, out)
    return out


def main() -> int:
    bad = 0
    for fn in sorted(os.listdir(WAVES)):
        if not fn.endswith(".json"):
            continue
        path = os.path.join(WAVES, fn)
        try:
            obj = json.load(open(path))
        except Exception as exc:                       # noqa: BLE001
            print(f"BAD JSON  {fn}: {exc}")
            bad += 1
            continue
        rows = _rows(obj.get("signal", []), [])
        lens = {len(r["wave"]) for r in rows}
        if len(lens) > 1:
            print(f"RAGGED    {fn}: wave lengths {sorted(lens)} -- rows will not "
                  f"line up in time")
            bad += 1
        for r in rows:
            slots = sum(1 for c in r["wave"] if c in DATA_CHARS)
            data = r.get("data", [])
            if isinstance(data, str):
                data = data.split()
            if slots and len(data) != slots:
                print(f"DATA      {fn}: '{r.get('name')}' has {slots} data slot(s) "
                      f"but {len(data)} label(s)")
                bad += 1
        head = obj.get("head", {}).get("text", "")
        if not head:
            print(f"NO HEAD   {fn}: a diagram with no caption cannot be read "
                  f"without the generator")
            bad += 1
        elif len(head) > 90:
            # WaveDrom centres head.text on ONE line and does not wrap, so a
            # long caption runs off both ends of the SVG and is truncated in
            # the PNG. The figure gets a title; the argument belongs in the MAS
            # prose beneath it, where it can be read.
            print(f"LONG HEAD {fn}: caption is {len(head)} chars -- WaveDrom "
                  f"does not wrap, so it will overflow the image. Keep it "
                  f"under 90 and put the explanation in the MAS.")
            bad += 1
    print(f"\nwave diagrams checked: "
          f"{len([f for f in os.listdir(WAVES) if f.endswith('.json')])}   "
          f"problems: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
