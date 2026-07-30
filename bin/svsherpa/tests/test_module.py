# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_module
# Purpose: Module assembly, declaration ordering and emission layout
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for module assembly and file layout."""

from __future__ import annotations

import pytest

from svsherpa import (
    C,
    Case,
    Enum,
    GenFor,
    GenIf,
    If,
    Instance,
    Module,
    ModuleDoc,
    Struct,
    ZERO,
    clog2,
)
from svsherpa.errors import SvError


@pytest.fixture
def counter():
    m = Module("counter", purpose="Enabled binary counter")
    width = m.param("WIDTH", 8)
    clk, rst_n, en = m.input("clk"), m.input("rst_n"), m.input("en")
    count = m.output("count", width)
    m.always_ff(clk, rst_n, reset=[count.set(ZERO)],
                body=[If(en, count.set(count + 1))])
    return m


# ------------------------------------------------------------------- layout
def test_file_opens_with_spdx_and_timescale(counter):
    text = counter.emit()
    assert text.startswith("// SPDX-License-Identifier: MIT")
    assert "`timescale 1ns / 1ps" in text


def test_module_ends_with_labelled_endmodule(counter):
    assert counter.emit().rstrip().endswith("endmodule : counter")


def test_file_ends_with_a_newline(counter):
    """POSIX 3.206, and verilator enforces it."""
    assert counter.emit().endswith("\n")


def test_ports_are_column_aligned(counter):
    lines = [ln for ln in counter.emit().splitlines() if "logic" in ln and "," in ln]
    starts = {ln.index("logic") for ln in lines}
    assert len(starts) == 1


def test_scalar_only_ports_have_no_stray_packed_column():
    m = Module("scalars")
    m.input("a")
    m.output("y")
    assert "input  logic a," in m.emit()


def test_parameters_render_in_the_header(counter):
    text = counter.emit()
    assert "module counter #(" in text
    assert "parameter int WIDTH = 8" in text


def test_module_with_no_parameters_omits_the_hash():
    m = Module("noparams")
    m.input("a")
    m.output("y")
    m.assign(m.ports[1], m.ports[0])
    assert "module noparams (" in m.emit()


def test_reset_macro_pulls_in_its_include(counter):
    assert '`include "reset_defs.svh"' in counter.emit()


def test_explicit_reset_style_drops_the_include():
    m = Module("explicit", reset_style="async_low")
    clk, rst_n = m.input("clk"), m.input("rst_n")
    q = m.output("q")
    m.always_ff(clk, rst_n, reset=[q.set(ZERO)], body=[q.set(C(1))])
    text = m.emit()
    assert "reset_defs.svh" not in text
    assert "always_ff @(posedge clk or negedge rst_n)" in text


@pytest.mark.parametrize(
    "style, expected",
    [
        ("async_low", "always_ff @(posedge clk or negedge rst_n)"),
        ("async_high", "always_ff @(posedge clk or posedge rst_n)"),
        ("sync_low", "always_ff @(posedge clk)"),
    ],
)
def test_reset_styles(style, expected):
    m = Module("styles", reset_style=style)
    clk, rst = m.input("clk"), m.input("rst_n")
    q = m.output("q")
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[q.set(C(1))])
    assert expected in m.emit()


def test_rst_asserted_macro_option():
    m = Module("polarity", use_rst_asserted=True)
    clk, rst = m.input("clk"), m.input("rst_n")
    q = m.output("q")
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[q.set(C(1))])
    assert "`RST_ASSERTED(rst_n)" in m.emit()


# --------------------------------------------------------- assignment operator
def test_always_ff_uses_nonblocking(counter):
    assert "count <= count + 1;" in counter.emit()


def test_always_comb_uses_blocking():
    m = Module("comb")
    a = m.input("a", 8)
    y = m.output("y", 8)
    m.always_comb(y.set(a))
    assert "always_comb y = a;" in m.emit()


def test_continuous_assign():
    m = Module("cont")
    a = m.input("a", 8)
    y = m.output("y", 8)
    m.assign(y, a, comment="straight through")
    assert "assign y = a;  // straight through" in m.emit()


# -------------------------------------------------------- declaration ordering
def test_localparams_precede_signals():
    m = Module("ordering")
    depth = m.param("DEPTH", 8)
    m.input("clk")
    pw = m.localparam("PW", clog2(depth) + 1)
    m.logic("wp", pw)
    text = m.emit()
    assert text.index("localparam int PW") < text.index("logic [PW-1:0] wp")


def test_typedefs_precede_the_module():
    m = Module("with_types")
    m.enum("state_t", ["S0", "S1"])
    m.input("clk")
    text = m.emit()
    assert text.index("typedef enum") < text.index("module with_types")


def test_memory_declaration_uses_unpacked_dimensions():
    m = Module("memories")
    dw = m.param("DATA_WIDTH", 8)
    depth = m.param("DEPTH", 16)
    m.mem("mem", dw, depth)
    assert "logic [DATA_WIDTH-1:0] mem [DEPTH];" in m.emit()


def test_packed_two_dimensional_port():
    m = Module("twodee")
    n = m.param("CHANNELS", 4)
    w = m.param("WIDTH", 8)
    m.input("d", [n, w])
    m.output("q", [n, w])
    text = m.emit()
    assert "input  logic [CHANNELS-1:0][WIDTH-1:0] d," in text
    assert "output logic [CHANNELS-1:0][WIDTH-1:0] q" in text


# ------------------------------------------------------------------- blank lines
def test_blocks_are_separated_by_blank_lines():
    m = Module("spacing")
    clk, rst = m.input("clk"), m.input("rst_n")
    a = m.input("a", 8)
    y = m.output("y", 8)
    q = m.output("q", 8)
    m.assign(y, a)
    m.always_ff(clk, rst, reset=[q.set(ZERO)], body=[q.set(a)])
    lines = m.emit().splitlines()
    assign_at = next(i for i, ln in enumerate(lines) if "assign y" in ln)
    assert lines[assign_at + 1].strip() == ""


def test_consecutive_assigns_stay_grouped():
    m = Module("grouped")
    a = m.input("a", 8)
    y = m.output("y", 8)
    z = m.output("z", 8)
    m.assign(y, a)
    m.assign(z, a)
    text = m.emit()
    assert "assign y = a;\n    assign z = a;" in text


# ------------------------------------------------------------------ naming
def test_duplicate_names_are_rejected():
    m = Module("dupes")
    m.input("a")
    with pytest.raises(SvError, match="duplicate"):
        m.logic("a")


def test_reserved_words_are_rejected():
    m = Module("reserved")
    with pytest.raises(SvError, match="reserved word"):
        m.input("output")


def test_illegal_identifier_is_rejected():
    m = Module("illegal")
    with pytest.raises(SvError, match="must start with"):
        m.logic("1bad")


def test_module_name_is_validated():
    with pytest.raises(SvError, match="reserved word"):
        Module("module")


# ------------------------------------------------------------------ instances
def test_instance_renders_named_connections():
    sub = Module("child")
    sub.param("W", 8)
    sub.input("clk")
    sub.output("q")
    top = Module("parent")
    clk = top.input("clk")
    q = top.output("q")
    top.instance(sub, "u_child", ports={"clk": clk, "q": q}, params={"W": 16})
    text = top.emit()
    assert "child #(" in text
    assert ".W  (16)" in text or ".W (16)" in text
    assert ") u_child (" in text


def test_instance_validates_port_names():
    sub = Module("child2")
    sub.input("clk")
    top = Module("parent2")
    clk = top.input("clk")
    with pytest.raises(SvError, match="no port"):
        top.instance(sub, "u_child", ports={"clk": clk, "nope": clk})


def test_instance_requires_every_port_connected():
    sub = Module("child3")
    sub.input("clk")
    sub.output("q")
    top = Module("parent3")
    clk = top.input("clk")
    with pytest.raises(SvError, match="unconnected"):
        top.instance(sub, "u_child", ports={"clk": clk})


def test_open_port_is_allowed_explicitly():
    sub = Module("child4")
    sub.input("clk")
    sub.output("q")
    top = Module("parent4")
    clk = top.input("clk")
    top.instance(sub, "u_child", ports={"clk": clk, "q": None})
    connection = next(ln for ln in top.emit().splitlines() if ".q" in ln)
    assert connection.split()[0] == ".q"
    assert connection.rstrip().endswith("()")


def test_instance_of_an_unbuilt_module_skips_validation():
    top = Module("parent5")
    clk = top.input("clk")
    top.add(Instance("external_ip", "u_ip", ports={"clk": clk}))
    assert "external_ip u_ip (" in top.emit()


# ------------------------------------------------------------------- generate
def test_gen_for_emits_a_genvar_loop():
    m = Module("genloop")
    n = m.param("N", 4)
    d = m.input("d", n)
    q = m.output("q", n)
    m.add(GenFor("i", n, label="g_lane", body=lambda i: [
        Instance("buf_cell", "u_buf", ports={"a": d[i], "y": q[i]}),
    ]))
    text = m.emit()
    assert "for (genvar i = 0; i < N; i++) begin : g_lane" in text
    assert ".a (d[i])" in text


def test_gen_for_can_wrap_in_generate_endgenerate():
    m = Module("genwrap")
    n = m.param("N", 4)
    d = m.input("d", n)
    q = m.output("q", n)
    m.add(GenFor("i", n, label="g_l", wrap=True, body=lambda i: [
        Instance("buf_cell", "u_buf", ports={"a": d[i], "y": q[i]}),
    ]))
    text = m.emit()
    assert "generate" in text and "endgenerate" in text


def test_gen_if_needs_a_label_for_its_else():
    m = Module("genif")
    flag = m.param("USE", 1, "bit")
    a = m.input("a")
    y = m.output("y")
    with pytest.raises(SvError, match="own label"):
        GenIf(flag, label="g_a", body=[m.ports and y.set(a)], else_body=[y.set(a)])


def test_empty_generate_body_is_rejected():
    m = Module("genempty")
    n = m.param("N", 4)
    with pytest.raises(SvError, match="empty"):
        GenFor("i", n, label="g_x", body=[])


# ----------------------------------------------------------------- doc banner
def test_doc_banner_is_generated_from_the_real_port_list():
    doc = ModuleDoc(
        description="Counts up when enabled.",
        features=("Configurable width",),
        param_notes={"WIDTH": "Description: counter width"},
        port_notes={"en": "Count enable (active-high)"},
        notes=("enable=0 holds the count",),
        test="Location: val/common/test_counter.py",
    )
    m = Module("documented", doc=doc, purpose="Counter")
    width = m.param("WIDTH", 8)
    clk, rst, en = m.input("clk"), m.input("rst_n"), m.input("en")
    count = m.output("count", width)
    m.always_ff(clk, rst, reset=[count.set(ZERO)],
                body=[If(en, count.set(count + 1))])
    text = m.emit()
    assert "// Module: documented" in text
    assert "Counts up when enabled." in text
    assert "count[WIDTH-1:0]" in text          # from the real port
    assert "Count enable (active-high)" in text
    assert "val/common/test_counter.py" in text


# -------------------------------------------------------------------- output
def test_write_names_the_file_after_the_module(tmp_path, counter):
    path = counter.write(tmp_path)
    assert path.name == "counter.sv"
    assert path.read_text() == counter.emit()


def test_write_accepts_an_explicit_filename(tmp_path, counter):
    path = counter.write(tmp_path / "custom.sv")
    assert path.name == "custom.sv"


def test_emit_is_idempotent(counter):
    """Emitting twice must not duplicate diagnostics."""
    counter.emit()
    first = len(counter.warnings)
    counter.emit()
    assert len(counter.warnings) == first


def test_repr_summarises(counter):
    assert "counter" in repr(counter)
