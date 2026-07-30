# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.test_svtypes
# Purpose: Packed enums and packed structs
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Tests for user-defined packed types."""

from __future__ import annotations

import pytest

from svsherpa import Case, Enum, Module, Struct, ZERO
from svsherpa.errors import SvError


# -------------------------------------------------------------------- enums
def test_binary_encoding_widths_and_values():
    st = Enum("state_t", ["S0", "S1", "S2", "S3"])
    assert st.width.try_eval({}) == 2
    assert [v for _, v in st.members] == [0, 1, 2, 3]


def test_onehot_encoding():
    st = Enum("state_t", ["S0", "S1", "S2", "S3"], encoding="onehot")
    assert st.width.try_eval({}) == 4
    assert [v for _, v in st.members] == [1, 2, 4, 8]


def test_gray_encoding_changes_one_bit_at_a_time():
    st = Enum("state_t", ["A", "B", "C", "D"], encoding="gray")
    values = [v for _, v in st.members]
    assert values == [0, 1, 3, 2]
    for lhs, rhs in zip(values, values[1:]):
        assert bin(lhs ^ rhs).count("1") == 1


def test_five_members_need_three_bits():
    st = Enum("state_t", ["A", "B", "C", "D", "E"])
    assert st.width.try_eval({}) == 3


def test_explicit_values_via_dict():
    st = Enum("cmd_t", {"IDLE": 0, "RUN": 5})
    assert st.width.try_eval({}) == 3
    assert st.RUN.value == 5


def test_declaration_renders_a_typedef():
    st = Enum("state_t", ["S0", "S1"], encoding="onehot")
    text = "\n".join(st.declaration())
    assert text.startswith("typedef enum logic [1:0] {")
    assert "S0 = 2'b01," in text
    assert text.endswith("} state_t;")


def test_single_member_enum_has_no_range():
    st = Enum("only_t", ["ONLY"])
    assert "typedef enum logic {" in "\n".join(st.declaration())


def test_member_access_and_rendering():
    st = Enum("state_t", ["S0", "S1"])
    assert st.S0.render() == "S0"
    assert st.S0.width.try_eval({}) == 1


def test_unknown_member_raises_a_helpful_error():
    st = Enum("state_t", ["S0", "S1"])
    with pytest.raises(AttributeError, match="members are S0, S1"):
        _ = st.S9


def test_bad_encoding_is_rejected():
    with pytest.raises(SvError, match="unknown encoding"):
        Enum("state_t", ["A"], encoding="thermometer")


def test_empty_enum_is_rejected():
    with pytest.raises(SvError, match="at least one member"):
        Enum("state_t", [])


def test_reserved_word_member_is_rejected():
    with pytest.raises(SvError, match="reserved word"):
        Enum("state_t", ["begin"])


def test_enum_typed_signal_carries_the_enum_width():
    """Otherwise every `state <= S0` looks like a truncation onto 1 bit."""
    m = Module("fsm")
    clk, rst = m.input("clk"), m.input("rst_n")
    st = m.enum("state_t", ["S0", "S1", "S2", "S3"], encoding="onehot")
    state = m.logic("state", st)
    assert state.width.try_eval({}) == 4
    m.always_ff(clk, rst, reset=[state.set(st.S0)],
                body=[Case(state, (st.S0, state.set(st.S1)),
                           default=state.set(st.S0))])
    assert "width" not in {w.kind for w in m.check()}


def test_enum_signal_declaration_uses_the_typedef_name():
    m = Module("fsmdecl")
    st = m.enum("state_t", ["S0", "S1"])
    m.logic("state", st)
    assert "state_t state;" in m.emit()


def test_enum_port():
    m = Module("fsmport")
    st = m.enum("state_t", ["S0", "S1"])
    m.output("state_out", st)
    assert "output state_t state_out" in m.emit()


def test_enum_iteration_and_length():
    st = Enum("state_t", ["S0", "S1", "S2"])
    assert len(st) == 3
    assert [m.name for m in st] == ["S0", "S1", "S2"]


# ------------------------------------------------------------------ structs
def test_struct_width_is_the_field_sum():
    cmd = Struct("cmd_pkt_t", [("valid", 1), ("opcode", 3), ("addr", 12),
                               ("data", 16)])
    assert cmd.width.try_eval({}) == 32


def test_struct_declaration_annotates_bit_ranges_msb_first():
    cmd = Struct("cmd_pkt_t", [("valid", 1), ("opcode", 3), ("addr", 12),
                               ("data", 16)])
    text = "\n".join(cmd.declaration())
    assert "typedef struct packed {" in text
    assert "// [31]" in text          # valid, the MSB
    assert "// [30:28]" in text       # opcode
    assert "// [15:0]" in text        # data, the LSBs
    assert "32 bits total" in text


def test_struct_field_access_has_the_field_width():
    cmd = Struct("cmd_pkt_t", [("valid", 1), ("opcode", 3), ("data", 16)])
    m = Module("structuser")
    sig = m.logic("cmd_q", cmd)
    assert sig.opcode.render() == "cmd_q.opcode"
    assert sig.opcode.width.try_eval({}) == 3
    assert sig.width.try_eval({}) == 20


def test_struct_field_can_be_assigned():
    cmd = Struct("cmd_pkt_t", [("valid", 1), ("data", 8)])
    m = Module("structassign")
    sig = m.logic("cmd_q", cmd)
    stmt = sig.valid.set(ZERO)
    assert stmt.targets() == ["cmd_q"]


def test_unknown_struct_field_raises():
    cmd = Struct("cmd_pkt_t", [("valid", 1)])
    m = Module("structbad")
    sig = m.logic("cmd_q", cmd)
    with pytest.raises(AttributeError, match="no field"):
        _ = sig.nonexistent


def test_field_colliding_with_a_signal_attribute_is_rejected():
    """`sig.name` must keep meaning the signal's name, not a struct field."""
    with pytest.raises(SvError, match="collides"):
        Struct("bad_t", [("name", 8)])


def test_struct_port_declaration():
    cmd = Struct("cmd_pkt_t", [("valid", 1), ("data", 8)])
    m = Module("structport")
    m.typedef(cmd)
    m.input("cmd_in", cmd)
    assert "input cmd_pkt_t cmd_in" in m.emit()


def test_struct_registered_through_the_module_emits_the_typedef():
    m = Module("structtypedef")
    m.struct("cmd_pkt_t", [("valid", 1), ("data", 8)])
    m.input("clk")
    text = m.emit()
    assert text.index("typedef struct packed") < text.index("module structtypedef")


def test_typedef_rejects_other_objects():
    m = Module("badtypedef")
    with pytest.raises(SvError, match="Enum or Struct"):
        m.typedef("cmd_pkt_t")


def test_symbolic_struct_field_width():
    """A parameterised field means the bit annotations are simply omitted."""
    m = Module("symstruct")
    width = m.param("W", 8)
    cmd = Struct("cmd_t", [("valid", 1), ("data", width)])
    text = "\n".join(cmd.declaration())
    assert "[W-1:0]" in text
