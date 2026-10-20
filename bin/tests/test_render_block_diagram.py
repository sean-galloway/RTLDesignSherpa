# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for bin/render_block_diagram.py's generated key.

The key is derived from the drawing, so the derivation IS the contract: each
element-key shape maps to its class, each line style to its sample, and a
class the drawing does not use never appears. A drawing marked
`// render: no-key` gets none.
"""
from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location("rbd", ROOT / "bin" / "render_block_diagram.py")
rbd = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(rbd)

needs_dot = pytest.mark.skipif(shutil.which("dot") is None, reason="graphviz dot not installed")

DRAWING = '''digraph t {
    node [shape=box, style=filled, fillcolor="white"];
    p   [label="port", style="rounded,filled", fillcolor="#E2EFDA"];
    lg  [label="logic"];
    rg  [label="reg", peripheries=2, fillcolor="#D6E4F0"];
    st  [label="fifo", shape=cylinder, fillcolor="#E8DFF5"];
    pk  [label="arb", shape=invtrapezium, fillcolor="#FFF2CC"];
    wp  [label="tap", style="filled,dashed", color="#777777"];
    pts [shape=point, style=invis];
    p -> lg; lg -> rg [penwidth=1.8]; rg -> st;
    st -> p [color="#1A7A1A"]; pk -> rg [style=dashed];
}
'''


def _classify(text: str):
    js = subprocess.run(["dot", "-Tjson"], input=text, capture_output=True,
                        text=True, check=True).stdout
    return rbd.classify(json.loads(js))


@needs_dot
def test_every_class_and_style_is_sampled() -> None:
    nodes, edges = _classify(DRAWING)
    assert nodes == ["logic", "registered", "storage", "pick", "interface_flopped"]
    assert edges == ["flow", "heavy", "return", "sideband"]


@needs_dot
def test_absent_classes_are_not_sampled() -> None:
    nodes, edges = _classify('digraph t { a [shape=box]; b [shape=box]; a -> b; }')
    assert nodes == ["logic"] and edges == ["flow"]


@needs_dot
def test_waypoint_and_points_are_not_classes() -> None:
    nodes, _ = _classify('digraph t { w [shape=box, style="filled,dashed", color="#777777"];'
                         ' q [shape=point]; w -> q; }')
    assert nodes == []


def test_interface_sample_claims_flopped_only_when_drawn() -> None:
    assert 'label="interface"' in rbd.key_dot(["interface_flopped"], [], False)
    assert '(flopped)' in rbd.key_dot(["interface_flopped"], [], True)


@needs_dot
def test_no_key_marker_and_render(tmp_path: Path) -> None:
    keyed, plain = tmp_path / "a.dot", tmp_path / "b.dot"
    keyed.write_text(DRAWING)
    plain.write_text("// render: no-key (test)\n" + DRAWING)
    assert "no key" not in rbd.render(keyed, 72, True)
    assert "[no key]" in rbd.render(plain, 72, True)
    assert (tmp_path / "a.png").stat().st_size > 0
