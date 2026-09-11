#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Render design/waves/*.json to SVG + PNG for the MAS.

The WaveJSON was written in 2026-09 and never rendered, so twelve timing
diagrams existed that nobody could look at without pasting them into the
WaveDrom editor one at a time -- which is why nothing in the MAS referenced
them. This closes that: one command produces the figures the MAS embeds.

    python3 design/render_waves.py          # -> docs/pumice_mas/assets/waves/

Needs `wavedrom-cli` (npm -g install wavedrom-cli) and `rsvg-convert`
(librsvg2-bin). Both are present on the build host. Diagrams are validated
first -- WaveDrom renders a malformed diagram without complaining, so an
unchecked render is a picture of a bug.
"""
from __future__ import annotations
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
WAVES = os.path.join(HERE, "waves")
OUT = os.path.join(ROOT, "docs", "pumice_mas", "assets", "waves")
PNG_WIDTH = 1600


def main() -> int:
    for tool in ("wavedrom-cli", "rsvg-convert"):
        if not shutil.which(tool):
            print(f"missing {tool} -- cannot render")
            return 1

    sys.path.insert(0, HERE)
    import check_waves
    if check_waves.main() != 0:
        print("\nREFUSING to render: WaveDrom draws a malformed diagram without "
              "complaining, so the picture would look fine and be wrong.")
        return 1

    os.makedirs(OUT, exist_ok=True)
    names = sorted(f for f in os.listdir(WAVES) if f.endswith(".json"))
    print(f"\nrendering {len(names)} diagram(s) -> {os.path.relpath(OUT, ROOT)}")
    for fn in names:
        stem = fn[:-5]
        src = os.path.join(WAVES, fn)
        svg = os.path.join(OUT, stem + ".svg")
        png = os.path.join(OUT, stem + ".png")
        subprocess.run(["wavedrom-cli", "-i", src, "-s", svg], check=True)
        subprocess.run(["rsvg-convert", "-w", str(PNG_WIDTH), svg, "-o", png],
                       check=True)
        print(f"  {stem}.png")
    return 0


if __name__ == "__main__":
    sys.exit(main())
