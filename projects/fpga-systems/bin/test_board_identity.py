# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""The JTAG identity readback: parsing, and the refusal it drives.

tooling TASK-022's board lock stops two flows driving one board. It cannot detect
a collision that happened anyway -- a harness records the sha256 of the bitstream
IT programmed, not what is on the device, so a board reprogrammed or
re-enumerated mid-run leaves a results file with no error, no timeout and no
mismatch. A lock prevents; a readback detects. These are complements.

EVERYTHING HERE IS HARDWARE-FREE ON PURPOSE. `parse_readback` is pure and
`verify_identity` takes an injected `readback=` dict, so the decision logic is
testable without Vivado and without touching a board. That is not just
convenience: the readback opens the hardware manager, so exercising it for real
while another flow holds the board would violate the very lock this feature
accompanies. The hardware path is therefore unexercised by this suite and is
called out as such in TASK-022.
"""

from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from board import Board, BoardSpec, IdentityError, parse_readback  # noqa: E402

GENESYS2_SERIAL = "200300B818A0"
NEXYS_SERIAL = "210292BFA3EE"

# Both boards really do sit on one JTAG chain in this lab, which is why the
# serial and not the board name is what distinguishes them.
CHAIN = f"""
****** Vivado v2024.1 (64-bit)
  **** SW Build 5076996 on Wed May 22 18:36:09 MDT 2024
JTAG_TARGET localhost:3121/xilinx_tcf/Digilent/{GENESYS2_SERIAL}
JTAG_DEVICE localhost:3121/xilinx_tcf/Digilent/{GENESYS2_SERIAL} xc7k325t_0 xc7k325tffg900-2 0x13631093
JTAG_TARGET localhost:3121/xilinx_tcf/Digilent/{NEXYS_SERIAL}
JTAG_DEVICE localhost:3121/xilinx_tcf/Digilent/{NEXYS_SERIAL} xc7a100t_0 xc7a100tcsg324-1 0x13631093
INFO: [Common 17-206] Exiting Vivado
"""


def _board(serial):
    return Board(BoardSpec(name="t", display_name="T", part="p", jtag_serial=serial))


# ---- parsing ---------------------------------------------------------------

def test_parses_targets_and_devices():
    rb = parse_readback(CHAIN)
    assert [t["serial"] for t in rb["targets"]] == [GENESYS2_SERIAL, NEXYS_SERIAL]
    assert len(rb["devices"]) == 2
    assert rb["devices"][0]["part"] == "xc7k325tffg900-2"
    assert rb["devices"][0]["idcode"] == "0x13631093"


def test_ignores_vivado_banner_and_blank_lines():
    """The readback is scraped from tool stdout, so noise is the normal case."""
    rb = parse_readback(CHAIN)
    assert len(rb["targets"]) == 2, "banner or INFO lines leaked into targets"


def test_target_error_is_not_counted_as_a_target():
    """JTAG_TARGET_ERROR means the target could NOT be opened.

    It must not become a target: a chain of unopenable targets would otherwise
    read as a healthy chain, and verify_identity would pass on a board it never
    actually reached.
    """
    rb = parse_readback(
        f"JTAG_TARGET_ERROR localhost:3121/xilinx_tcf/Digilent/{GENESYS2_SERIAL} busy\n")
    assert rb["targets"] == []
    assert rb["devices"] == []


def test_malformed_lines_are_dropped_not_guessed():
    rb = parse_readback("JTAG_TARGET\nJTAG_DEVICE only three fields\n")
    assert rb["targets"] == [] and rb["devices"] == []


def test_na_properties_survive():
    """The tcl prints n/a rather than failing; that must reach the caller."""
    rb = parse_readback(
        f"JTAG_TARGET x/{NEXYS_SERIAL}\nJTAG_DEVICE x/{NEXYS_SERIAL} dev n/a n/a\n")
    assert rb["devices"][0]["part"] == "n/a"
    assert rb["devices"][0]["idcode"] == "n/a"


# ---- the decision ----------------------------------------------------------

def test_verify_passes_when_our_board_is_on_the_chain():
    rb = parse_readback(CHAIN)
    assert _board(GENESYS2_SERIAL).verify_identity(readback=rb) is rb


def test_verify_refuses_when_our_board_is_absent():
    rb = parse_readback(CHAIN)
    with pytest.raises(IdentityError) as e:
        _board("DEADBEEF0000").verify_identity(readback=rb)
    # The message must name what IS there; "wrong board" without the chain
    # contents sends the reader to the lab rather than to the answer.
    assert GENESYS2_SERIAL in str(e.value)


def test_verify_refuses_a_target_with_no_device_behind_it():
    """A target that enumerates but holds no device is not a usable board.

    This is the case a naive "is my serial in the list" check passes and should
    not: the FTDI answered, the FPGA did not.
    """
    rb = parse_readback(f"JTAG_TARGET localhost/Digilent/{GENESYS2_SERIAL}\n")
    with pytest.raises(IdentityError):
        _board(GENESYS2_SERIAL).verify_identity(readback=rb)


def test_board_without_a_serial_is_returned_unjudged():
    """Nothing to verify, so claim nothing.

    A board with no registry serial cannot be told from any other on the chain.
    Returning success would be a checker that cannot fail -- the exact shape this
    repo has been bitten by repeatedly.
    """
    rb = parse_readback(CHAIN)
    assert _board(None).verify_identity(readback=rb) is rb


def test_env_override_serial_is_what_gets_verified():
    """FPGA_JTAG_SERIAL overrides the registry, so verification must follow it."""
    rb = parse_readback(CHAIN)
    b = _board("DEADBEEF0000")
    os.environ["FPGA_JTAG_SERIAL"] = NEXYS_SERIAL
    try:
        assert b.verify_identity(readback=rb) is rb
    finally:
        os.environ.pop("FPGA_JTAG_SERIAL", None)


# ---- the command, without running it ---------------------------------------

def test_readback_command_is_batch_and_read_only():
    cmd = _board(GENESYS2_SERIAL).readback_command("vivado")
    assert cmd[:4] == ["vivado", "-mode", "batch", "-notrace"]
    assert cmd[-1].endswith("jtag_readback.tcl")
    assert os.path.isfile(cmd[-1]), "the readback tcl is missing from bin/"
