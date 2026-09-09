#!/usr/bin/env python3
"""Generate the RDS netlistsvg skin from the shipped default.

Why not hand-maintain the SVG: the default skin carries a style block and a
layout-properties block that are fiddly and that upstream changes. This copies
the installed default and applies a documented set of edits, so `diff` against
a fresh default shows exactly what RDS changed and an upstream bump is a
re-run rather than a merge.

What it fixes, chosen from an actual cell histogram of the pumice FUBs
(34508 cells) rather than from taste:

  $pmux    1.9%  -- the default skin ALIASES $pmux ONTO THE 2:1 MUX SYMBOL, so
                    every case statement is drawn as a two-input mux. That is
                    not a cosmetic problem, it misrepresents the netlist. Gets
                    its own tall one-hot symbol.
  $mux    32.6%  -- enlarged, and a heavy-stroke $mux-bus variant so the
                    datapath separates from control at a glance.
  $eqx     4.8%  \\
  $reduce_and 2.5% |  none of these are in the default skin, so ~13% of all
  $adff    2.3%  |  cells render as anonymous generic rectangles. $adff in
  $shiftx  2.2%  |  particular is the async-reset flop -- the thing you most
  $mul/$neg/...  /   want to SEE in a CDC review.

Generic fallback is deliberately garish: it is the TODO list for symbols not
yet drawn.

    python3 make_skin.py            # -> skin/rds-skin.svg (+ skin/default.svg)
"""
import re, shutil, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SKIN = HERE / "skin"


def find_default():
    for probe in (
        Path.home() / ".npm-global/lib/node_modules/netlistsvg/lib/default.svg",
    ):
        if probe.exists():
            return probe
    try:
        root = subprocess.check_output(["npm", "root", "-g"], text=True).strip()
        p = Path(root) / "netlistsvg/lib/default.svg"
        if p.exists():
            return p
    except Exception:
        pass
    sys.exit("cannot find netlistsvg's default.svg; is netlistsvg installed?")


# ---- new symbols, appended before </svg> ----------------------------------
NEW_SYMBOLS = r'''
  <!-- ===================== RDS additions ===================== -->

  <!-- $pmux: one-hot case mux. A = default, B = all cases concatenated,
       S = one-hot select. Deliberately NOT the 2:1 shape. -->
  <g s:type="pmux" transform="translate(50,150)" s:width="34" s:height="80">
    <s:alias val="$pmux"/>
    <path d="M0,0 L34,14 L34,66 L0,80 Z" style="stroke-width:2.5" class="$cell_id"/>
    <text x="17" y="36" class="nodelabel $cell_id" style="font-size:9px">1-hot</text>
    <text x="17" y="48" class="nodelabel $cell_id" style="font-size:8px">case</text>
    <g s:x="0"  s:y="14" s:pid="A"/>
    <g s:x="0"  s:y="52" s:pid="B"/>
    <g s:x="17" s:y="76" s:pid="S"/>
    <g s:x="34" s:y="40" s:pid="Y"/>
  </g>

  <!-- $mux-bus: netlistsvg appends -bus when WIDTH>1. Heavy stroke = datapath. -->
  <g s:type="mux-bus" transform="translate(120,150)" s:width="24" s:height="48">
    <s:alias val="$mux-bus"/>
    <path d="M0,0 L24,12 L24,36 L0,48 Z" style="stroke-width:2.5" class="$cell_id"/>
    <g s:x="0"  s:y="12" s:pid="A"/>
    <g s:x="0"  s:y="36" s:pid="B"/>
    <g s:x="12" s:y="43" s:pid="S"/>
    <g s:x="24" s:y="24" s:pid="Y"/>
  </g>

  <!-- $adff: ASYNC-reset flop. Double left edge + ARST marked, so an async
       reset is visible without reading the label. -->
  <g s:type="adff" transform="translate(200,150)" s:width="34" s:height="44">
    <s:alias val="$adff"/>
    <s:alias val="$adffe"/>
    <s:alias val="$dffsr"/>
    <rect width="34" height="44" x="0" y="0" style="stroke-width:2.5" class="$cell_id"/>
    <path d="M0,38 L6,33 L0,28" class="$cell_id"/>
    <path d="M3,3 L3,41" style="stroke-dasharray:3,2" class="$cell_id"/>
    <text x="17" y="16" class="nodelabel $cell_id" style="font-size:8px">aRST</text>
    <g s:x="34" s:y="12" s:pid="Q"/>
    <g s:x="0"  s:y="33" s:pid="CLK"/>
    <g s:x="0"  s:y="12" s:pid="D"/>
    <g s:x="0"  s:y="22" s:pid="ARST"/>
  </g>

  <!-- $sdff / $dffe: sync reset / clock enable -->
  <g s:type="sdff" transform="translate(250,150)" s:width="34" s:height="44">
    <s:alias val="$sdff"/>
    <s:alias val="$sdffe"/>
    <s:alias val="$sdffce"/>
    <s:alias val="$dffe"/>
    <rect width="34" height="44" x="0" y="0" class="$cell_id"/>
    <path d="M0,38 L6,33 L0,28" class="$cell_id"/>
    <text x="17" y="16" class="nodelabel $cell_id" style="font-size:8px">sRST</text>
    <g s:x="34" s:y="12" s:pid="Q"/>
    <g s:x="0"  s:y="33" s:pid="CLK"/>
    <g s:x="0"  s:y="12" s:pid="D"/>
    <g s:x="0"  s:y="22" s:pid="SRST"/>
    <g s:x="0"  s:y="22" s:pid="EN"/>
  </g>

  <!-- comparators: $eqx is the 4.8% one the default skin has no symbol for -->
  <g s:type="eqx" transform="translate(300,150)" s:width="28" s:height="28">
    <s:alias val="$eqx"/>
    <s:alias val="$nex"/>
    <s:alias val="$ne"/>
    <s:alias val="$le"/>
    <circle cx="14" cy="14" r="14" class="$cell_id"/>
    <text x="14" y="18" class="nodelabel $cell_id" s:attribute="ref" style="font-size:9px">==x</text>
    <g s:x="0"  s:y="8"  s:pid="A"/>
    <g s:x="0"  s:y="20" s:pid="B"/>
    <g s:x="28" s:y="14" s:pid="Y"/>
  </g>

  <!-- reductions: |A, &A, bool(A) -->
  <g s:type="reduce" transform="translate(350,150)" s:width="28" s:height="26">
    <s:alias val="$reduce_and"/>
    <s:alias val="$reduce_or"/>
    <s:alias val="$reduce_bool"/>
    <path d="M0,0 L18,0 A13,13 0 0 1 18,26 L0,26 Z" class="$cell_id"/>
    <text x="12" y="17" class="nodelabel $cell_id" s:attribute="ref" style="font-size:9px">R</text>
    <g s:x="0"  s:y="13" s:pid="A"/>
    <g s:x="28" s:y="13" s:pid="Y"/>
  </g>

  <!-- shifters: $shiftx is how a variable index into a packed vector lands -->
  <g s:type="shift" transform="translate(400,150)" s:width="32" s:height="32">
    <s:alias val="$shiftx"/>
    <s:alias val="$shift"/>
    <s:alias val="$shl"/>
    <s:alias val="$shr"/>
    <s:alias val="$sshl"/>
    <s:alias val="$sshr"/>
    <rect width="32" height="32" x="0" y="0" class="$cell_id"/>
    <path d="M6,10 L26,10 M20,5 L26,10 L20,15" class="$cell_id"/>
    <text x="16" y="27" class="nodelabel $cell_id" style="font-size:8px">shift</text>
    <g s:x="0"  s:y="10" s:pid="A"/>
    <g s:x="0"  s:y="22" s:pid="B"/>
    <g s:x="32" s:y="16" s:pid="Y"/>
  </g>

  <!-- $mul / $neg: standard ALU trapezoid, marked -->
  <g s:type="mul" transform="translate(450,150)" s:width="30" s:height="36">
    <s:alias val="$mul"/>
    <s:alias val="$div"/>
    <s:alias val="$mod"/>
    <path d="M0,0 L30,7 L30,29 L0,36 Z" style="stroke-width:2.5" class="$cell_id"/>
    <text x="15" y="22" class="nodelabel $cell_id" s:attribute="ref" style="font-size:10px">*</text>
    <g s:x="0"  s:y="9"  s:pid="A"/>
    <g s:x="0"  s:y="27" s:pid="B"/>
    <g s:x="30" s:y="18" s:pid="Y"/>
  </g>

  <g s:type="neg" transform="translate(500,150)" s:width="26" s:height="26">
    <s:alias val="$neg"/>
    <s:alias val="$pos"/>
    <path d="M0,0 L26,13 L0,26 Z" class="$cell_id"/>
    <text x="9" y="17" class="nodelabel $cell_id" style="font-size:10px">-</text>
    <g s:x="0"  s:y="13" s:pid="A"/>
    <g s:x="26" s:y="13" s:pid="Y"/>
  </g>

  <!-- memories: distinct fill so BRAM vs flops is obvious at a glance -->
  <g s:type="mem" transform="translate(550,150)" s:width="44" s:height="52">
    <s:alias val="$mem_v2"/>
    <s:alias val="$mem"/>
    <text x="22" y="-4" class="nodelabel $cell_id" s:attribute="ref">mem</text>
    <rect width="44" height="52" s:generic="body" style="fill:#ffe2b0"
          class="$cell_id"/>
  </g>
'''

# generic fallback: garish on purpose -- it is the "needs a symbol" list
GENERIC_FILL = '<rect width="30" height="40" s:generic="body" style="fill:#ff4dd2;fill-opacity:0.30" class="$cell_id"/>'


def main():
    src = find_default()
    SKIN.mkdir(parents=True, exist_ok=True)
    shutil.copy(src, SKIN / "default.svg")          # pristine, for diffing
    s = src.read_text()

    # 1. layout: more room between layers, left-to-right, bundle fanout
    s = s.replace(
        '''      org.eclipse.elk.layered.spacing.nodeNodeBetweenLayers="35"
      org.eclipse.elk.spacing.nodeNode= "35"
      org.eclipse.elk.layered.layering.strategy= "LONGEST_PATH"''',
        '''      org.eclipse.elk.layered.spacing.nodeNodeBetweenLayers="60"
      org.eclipse.elk.spacing.nodeNode= "45"
      org.eclipse.elk.direction= "RIGHT"
      org.eclipse.elk.layered.mergeEdges= "true"
      org.eclipse.elk.layered.layering.strategy= "LONGEST_PATH"''')

    # 2. $pmux must NOT share the 2:1 mux symbol
    s = s.replace('''  <g s:type="mux" transform="translate(50, 50)" s:width="20" s:height="40">
    <s:alias val="$pmux"/>
    <s:alias val="$mux"/>
    <s:alias val="$_MUX_"/>

    <path d="M0,0 L20,10 L20,30 L0,40 Z" class="$cell_id"/>

    <g s:x="0" s:y="10" s:pid="A"/>
    <g s:x="0" s:y="30" s:pid="B"/>
    <g s:x="10" s:y="35" s:pid="S"/>
    <g s:x="20" s:y="20" s:pid="Y"/>
  </g>''',
'''  <g s:type="mux" transform="translate(50, 50)" s:width="24" s:height="48">
    <s:alias val="$mux"/>
    <s:alias val="$_MUX_"/>

    <path d="M0,0 L24,12 L24,36 L0,48 Z" class="$cell_id"/>

    <g s:x="0" s:y="12" s:pid="A"/>
    <g s:x="0" s:y="36" s:pid="B"/>
    <g s:x="12" s:y="43" s:pid="S"/>
    <g s:x="24" s:y="24" s:pid="Y"/>
  </g>''')

    # 3. garish generic fallback
    s = s.replace('<rect width="30" height="40" s:generic="body" class="$cell_id"/>',
                  GENERIC_FILL)

    # 4. append the new symbols
    s = s.replace("</svg>", NEW_SYMBOLS + "\n</svg>")

    out = SKIN / "rds-skin.svg"
    out.write_text(s)
    added = len(re.findall(r"<s:alias", NEW_SYMBOLS))
    print(f"[ok] {out.relative_to(HERE)}  (+{added} aliases over the default; "
          f"pristine default copied beside it for diffing)")


if __name__ == "__main__":
    sys.exit(main())
