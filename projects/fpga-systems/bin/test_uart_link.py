#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less tests for port discovery, board selection and programming setup.

Everything here runs with no FPGA attached and without pyserial or Vivado
installed -- which is the point: the logic that decides WHICH board and WHICH
port must be testable, because on real hardware a wrong answer looks like a
timing bug rather than a lookup bug.
"""

from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import uart_link                                        # noqa: E402
import board                                            # noqa: E402
from board import Board, BoardSpec                      # noqa: E402
from boards import get_board, list_boards               # noqa: E402
from uart_link import UartPort, find_port               # noqa: E402


# ---------------------------------------------------------------------------
# UartPort serial matching
# ---------------------------------------------------------------------------

def test_matches_serial_exact():
    p = UartPort("/dev/ttyUSB1", usb_serial="210292B7D46F")
    assert p.matches_serial("210292B7D46F")


def test_matches_serial_tolerates_interface_suffix_either_way():
    # The FT2232 EEPROM serial may reach us with or without the interface
    # letter, from either side. Both must match, or a present board reads as
    # absent.
    assert UartPort("/dev/ttyUSB1", usb_serial="210292B7D46FB").matches_serial("210292B7D46F")
    assert UartPort("/dev/ttyUSB1", usb_serial="210292B7D46F").matches_serial("210292B7D46FB")


def test_matches_serial_is_case_and_punctuation_insensitive():
    assert UartPort("/dev/ttyUSB1", usb_serial="au05x8rm").matches_serial("AU05X8RM")


def test_matches_serial_rejects_other_board():
    p = UartPort("/dev/ttyUSB1", usb_serial="210292B7D46F")
    assert not p.matches_serial("200300B818A0")


def test_matches_serial_false_when_unknown():
    assert not UartPort("/dev/ttyUSB0").matches_serial("210292B7D46F")
    assert not UartPort("/dev/ttyUSB0", usb_serial="X").matches_serial(None)


# ---------------------------------------------------------------------------
# Board -> its own ports
# ---------------------------------------------------------------------------

NEXYS = "210292B7D46F"
GENESYS = "200300B818A0"


@pytest.fixture
def two_boards(monkeypatch):
    """Both lab boards attached: the Nexys A7 UART on the JTAG FT2232, the
    Genesys 2 UART on its separate FT232R."""
    ports = [
        UartPort("/dev/ttyUSB0", usb_serial=NEXYS + "A", description="JTAG"),
        UartPort("/dev/ttyUSB1", usb_serial=NEXYS + "B", description="UART"),
        UartPort("/dev/ttyUSB2", usb_serial=GENESYS + "A", description="JTAG"),
        UartPort("/dev/ttyUSB3", usb_serial="AU05X8RM", description="FT232R"),
    ]
    monkeypatch.setattr(uart_link, "list_uart_ports", lambda *a, **k: list(ports))
    import board as board_mod
    monkeypatch.setattr(board_mod, "list_uart_ports", lambda *a, **k: list(ports))
    return ports


def test_board_finds_only_its_own_ports(two_boards):
    devs = [p.device for p in get_board("nexys_a7_100t").find_uart_ports()]
    assert devs == ["/dev/ttyUSB0", "/dev/ttyUSB1"]


def test_genesys_uart_is_found_via_its_separate_ft232r(two_boards):
    # The gotcha this encodes: matching the Genesys 2 UART against the JTAG
    # serial finds nothing. It must be found by the FT232R's own serial.
    devs = [p.device for p in get_board("genesys2").find_uart_ports()]
    assert devs == ["/dev/ttyUSB3"]


def test_no_visible_serials_returns_all_candidates(monkeypatch):
    # Without pyserial we get bare globbed paths and cannot filter. Returning
    # everything (for a probe to sort out) beats returning nothing, which would
    # read as "board not attached".
    bare = [UartPort("/dev/ttyUSB0"), UartPort("/dev/ttyUSB1")]
    import board as board_mod
    monkeypatch.setattr(board_mod, "list_uart_ports", lambda *a, **k: list(bare))
    assert len(get_board("nexys_a7_100t").find_uart_ports()) == 2


def test_visible_serials_none_ours_returns_empty(monkeypatch):
    other = [UartPort("/dev/ttyUSB0", usb_serial="DEADBEEF")]
    import board as board_mod
    monkeypatch.setattr(board_mod, "list_uart_ports", lambda *a, **k: list(other))
    assert get_board("nexys_a7_100t").find_uart_ports() == []


# ---------------------------------------------------------------------------
# find_port probe loop
# ---------------------------------------------------------------------------

class FakeLink:
    """Stands in for UartLink; `answers` decides which ports respond."""

    opened: list = []

    def __init__(self, port, baudrate=115200, timeout=1.0, settle=0.0):
        self.port = port
        FakeLink.opened.append(port)
        if port in FakeLink.unopenable:
            raise OSError(f"cannot open {port}")

    unopenable: set = set()

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return None


@pytest.fixture(autouse=True)
def reset_fake():
    FakeLink.opened = []
    FakeLink.unopenable = set()
    yield


def _patch_link(monkeypatch):
    monkeypatch.setattr(uart_link, "UartLink", FakeLink)


def test_find_port_returns_the_port_that_answers(monkeypatch):
    _patch_link(monkeypatch)
    port = find_port(probe=lambda link: link.port == "/dev/ttyUSB2",
                     candidates=["/dev/ttyUSB0", "/dev/ttyUSB1", "/dev/ttyUSB2"],
                     verbose=False)
    assert port == "/dev/ttyUSB2"


def test_find_port_tries_want_first_but_still_probes_it(monkeypatch):
    # An explicit --port is a hint, not a bypass: a stale path must fail over
    # rather than silently drive the wrong board.
    _patch_link(monkeypatch)
    port = find_port(probe=lambda link: link.port == "/dev/ttyUSB0",
                     want="/dev/ttyUSB2",
                     candidates=["/dev/ttyUSB0", "/dev/ttyUSB2"],
                     verbose=False)
    assert FakeLink.opened[0] == "/dev/ttyUSB2"   # tried first
    assert port == "/dev/ttyUSB0"                 # but did not win


def test_find_port_skips_unopenable_ports(monkeypatch):
    _patch_link(monkeypatch)
    FakeLink.unopenable = {"/dev/ttyUSB0"}
    port = find_port(probe=lambda link: True,
                     candidates=["/dev/ttyUSB0", "/dev/ttyUSB1"],
                     verbose=False)
    assert port == "/dev/ttyUSB1"


def test_find_port_raises_systemexit_when_nothing_answers(monkeypatch):
    _patch_link(monkeypatch)
    with pytest.raises(SystemExit) as exc:
        find_port(probe=lambda link: False,
                  candidates=["/dev/ttyUSB0"],
                  label="pumice DDR2 char harness", verbose=False)
    assert "pumice DDR2 char harness" in str(exc.value)
    assert "/dev/ttyUSB0" in str(exc.value)


def test_find_port_auto_means_no_preference(monkeypatch):
    _patch_link(monkeypatch)
    port = find_port(probe=lambda link: True, want="auto",
                     candidates=["/dev/ttyUSB5"], verbose=False)
    assert port == "/dev/ttyUSB5"


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

def test_registry_has_both_lab_boards():
    assert "nexys_a7_100t" in list_boards()
    assert "genesys2" in list_boards()


def test_aliases_resolve():
    assert get_board("nexys").name == "nexys_a7_100t"
    assert get_board("genesys").name == "genesys2"


def test_unknown_board_raises_rather_than_defaulting():
    # Silently defaulting would program the wrong board.
    with pytest.raises(KeyError) as exc:
        get_board("spartan3")
    assert "nexys_a7_100t" in str(exc.value)


def test_env_selects_board(monkeypatch):
    monkeypatch.setenv("FPGA_BOARD", "genesys2")
    assert get_board().name == "genesys2"


def test_board_serials_are_distinct():
    assert (get_board("nexys_a7_100t").SPEC.jtag_serial
            != get_board("genesys2").SPEC.jtag_serial)


# ---------------------------------------------------------------------------
# Programming (no Vivado required)
# ---------------------------------------------------------------------------

def test_program_env_carries_board_facts(tmp_path):
    bit = tmp_path / "ddr2_char.bit"
    bit.write_bytes(b"\x00")
    env = get_board("nexys_a7_100t").program_env(str(bit))
    assert env["FPGA_BITSTREAM"] == str(bit)
    assert env["FPGA_JTAG_SERIAL"] == NEXYS
    assert env["FPGA_BOARD"] == "nexys_a7_100t"


def test_env_override_wins_over_spec_serial(monkeypatch):
    monkeypatch.setenv("FPGA_JTAG_SERIAL", "CAFEBABE")
    assert get_board("nexys_a7_100t").jtag_serial == "CAFEBABE"


def test_legacy_per_flow_override_still_honoured(monkeypatch):
    monkeypatch.delenv("FPGA_JTAG_SERIAL", raising=False)
    monkeypatch.setenv("RAPIDS_CHAR_JTAG_SERIAL", "FEEDFACE")
    assert get_board("nexys_a7_100t").jtag_serial == "FEEDFACE"


def test_program_uses_the_single_shared_tcl(tmp_path):
    """Every board programs through ONE tcl, not a per-flow copy.

    Asserted by identity -- the script sits in the shared layer beside
    board.py -- rather than by a hardcoded path. The previous version pinned
    the literal string "fpga/bin/program_fpga.tcl" and failed the moment the
    layer moved, which told us nothing about whether the property still held.
    """
    bit = tmp_path / "x.bit"
    bit.write_bytes(b"\x00")
    cmd = get_board("nexys_a7_100t").program_command(str(bit))
    tcl = cmd[-1]
    shared_layer = os.path.dirname(os.path.abspath(board.__file__))
    assert os.path.basename(tcl) == "program_fpga.tcl"
    assert os.path.dirname(os.path.abspath(tcl)) == shared_layer
    assert os.path.isfile(tcl)


def test_program_fails_fast_on_missing_bitstream():
    # Before a 30-second Vivado startup, not after.
    with pytest.raises(FileNotFoundError) as exc:
        get_board("nexys_a7_100t").program("/nonexistent/x.bit")
    assert "make bitstream" in str(exc.value)


def test_program_dry_run_needs_no_vivado(tmp_path, capsys):
    bit = tmp_path / "x.bit"
    bit.write_bytes(b"\x00")
    assert get_board("nexys_a7_100t").program(str(bit), vivado="definitely-not-installed",
                                              dry_run=True) == 0
    assert NEXYS in capsys.readouterr().out


# ---------------------------------------------------------------------------
# Custom board (the extension path)
# ---------------------------------------------------------------------------

def test_custom_board_from_spec_needs_no_subclass(monkeypatch):
    spec = BoardSpec(name="fake", display_name="Fake", part="xc7z020",
                     jtag_serial="ABC123", uart_glob="/dev/ttyACM*")
    b = Board(spec)
    monkeypatch.setattr("board.list_uart_ports",
                        lambda *a, **k: [UartPort("/dev/ttyACM0", usb_serial="ABC123")])
    assert [p.device for p in b.find_uart_ports()] == ["/dev/ttyACM0"]


# ---------------------------------------------------------------------------
# FPGA_JTAG_SERIAL must reach port discovery, not just programming
# ---------------------------------------------------------------------------

def test_jtag_serial_override_reaches_uart_discovery(monkeypatch):
    """A board whose real serial differs from the registry must still be found.

    The override used to reach `program` but not `find_uart_ports`, which read
    the spec's static serial. The symptom was a board that programmed fine and
    then reported "no UART ports found" quoting the very serial the user had
    just overridden.
    """
    other = [UartPort("/dev/ttyUSB0", usb_serial="210384B2FB17")]
    import board as board_mod
    monkeypatch.setattr(board_mod, "list_uart_ports", lambda *a, **k: list(other))

    b = get_board("nexys_a7_100t")
    assert b.find_uart_ports() == []            # registry serial: no match

    monkeypatch.setenv("FPGA_JTAG_SERIAL", "210384B2FB17")
    assert [p.device for p in b.find_uart_ports()] == ["/dev/ttyUSB0"]


def test_override_does_not_hijack_a_board_with_its_own_uart_serial(monkeypatch):
    """Genesys 2's UART is a separate FT232R, so the JTAG override is irrelevant
    to it -- overriding JTAG must not make it start matching the wrong port."""
    ports = [
        UartPort("/dev/ttyUSB0", usb_serial="210384B2FB17"),
        UartPort("/dev/ttyUSB1", usb_serial="AU05X8RM"),
    ]
    import board as board_mod
    monkeypatch.setattr(board_mod, "list_uart_ports", lambda *a, **k: list(ports))
    monkeypatch.setenv("FPGA_JTAG_SERIAL", "210384B2FB17")

    devs = [p.device for p in get_board("genesys2").find_uart_ports()]
    assert devs == ["/dev/ttyUSB1"]
