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


# ---------------------------------------------------------------------------
# The verdict, and the artifact it has to land in.
#
# `verify_identity` refuses by raising, which is right for a caller that wants to
# stop. It is NOT enough for the record: a warning printed to a terminal is
# indistinguishable from a pass once it scrolls, so a run that could not look
# would otherwise write exactly what a run that looked and approved writes, and
# six weeks later nobody can tell which one they are holding. These tests exist
# to keep `inconclusive` and `verified` distinguishable in the file.
# ---------------------------------------------------------------------------

def _verdict_board(serial, readback):
    """A board whose readback is `readback`: a dict to return, or an exception
    instance/class to raise."""
    b = _board(serial)

    def fake(vivado="vivado", timeout=240):
        if isinstance(readback, BaseException) or (
                isinstance(readback, type) and issubclass(readback, BaseException)):
            raise readback
        return readback

    b.readback = fake
    return b


def test_verdict_is_verified_when_our_board_is_on_the_chain():
    v = _verdict_board(GENESYS2_SERIAL, parse_readback(CHAIN)).identity_verdict()
    assert v["status"] == "verified"
    assert v["serial"] == GENESYS2_SERIAL
    assert v["chain"] is not None


def test_verdict_reports_wrong_without_raising():
    # The refusal still happens in `program`; the verdict itself must be data,
    # or the wrong-board case cannot be written down before we bail out.
    v = _verdict_board("DEADBEEF", parse_readback(CHAIN)).identity_verdict()
    assert v["status"] == "wrong"
    assert "DEADBEEF" in v["detail"]


def test_verdict_is_inconclusive_when_the_chain_cannot_be_read():
    v = _verdict_board(
        GENESYS2_SERIAL,
        IdentityError("vivado not found on PATH")).identity_verdict()
    assert v["status"] == "inconclusive"
    assert v["chain"] is None


def test_a_wedged_hw_server_is_inconclusive_not_an_exception():
    # A hung hw_server is the commonest way the readback fails to return at all.
    # If TimeoutExpired escaped, it would take `program` down -- turning the
    # deliberately warn-only path into the refusal it was designed not to be.
    import subprocess as sp
    v = _verdict_board(
        GENESYS2_SERIAL,
        sp.TimeoutExpired(cmd=["vivado"], timeout=240)).identity_verdict()
    assert v["status"] == "inconclusive"


def test_a_board_with_no_serial_is_unjudged_not_verified():
    v = _verdict_board(None, parse_readback(CHAIN)).identity_verdict()
    assert v["status"] == "unjudged"


def test_inconclusive_and_verified_are_not_the_same_record():
    good = _verdict_board(GENESYS2_SERIAL, parse_readback(CHAIN)).identity_verdict()
    blind = _verdict_board(GENESYS2_SERIAL,
                           IdentityError("no hw_server")).identity_verdict()
    assert good["status"] != blind["status"]


# ---- the artifact ---------------------------------------------------------

def _programmable(tmp_path, monkeypatch, serial, readback, vivado_rc=0):
    """A board that will run `program` end to end with no Vivado and no board."""
    import board as board_mod
    bit = tmp_path / "top.bit"
    bit.write_bytes(b"\xff" * 4096 + b"bitstream body")
    monkeypatch.setattr(board_mod.shutil, "which", lambda _: "/opt/vivado/bin/vivado")

    class _Proc:
        returncode = vivado_rc

    monkeypatch.setattr(board_mod.subprocess, "run", lambda *a, **k: _Proc())
    return _verdict_board(serial, readback), str(bit)


def _record(path):
    import json
    with open(path) as fh:
        return json.load(fh)


def test_record_carries_the_sha256_of_the_bitstream(tmp_path, monkeypatch):
    import hashlib
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN))
    out = tmp_path / "id.json"
    b.program(bit, identity_json=str(out))
    rec = _record(out)
    assert rec["bitstream_sha256"] == hashlib.sha256(open(bit, "rb").read()).hexdigest()
    assert rec["bitstream"] == os.path.abspath(bit)


def test_record_states_verified_when_the_board_was_confirmed(tmp_path, monkeypatch):
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN))
    out = tmp_path / "id.json"
    b.program(bit, identity_json=str(out))
    rec = _record(out)
    assert rec["identity"]["status"] == "verified"
    assert rec["programmed"] is True


def test_record_states_inconclusive_when_we_could_not_look(tmp_path, monkeypatch):
    # THE POINT OF THE WHOLE FEATURE. Programming still proceeds -- the warning
    # path is deliberately non-fatal -- but the artifact must not read like a
    # confirmed run.
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           IdentityError("hw_server unreachable"))
    out = tmp_path / "id.json"
    assert b.program(bit, identity_json=str(out)) == 0
    rec = _record(out)
    assert rec["identity"]["status"] == "inconclusive"
    assert rec["programmed"] is True


def test_a_skipped_check_says_so_in_the_file(tmp_path, monkeypatch):
    # --no-verify-identity must not produce an artifact-shaped silence. A missing
    # file is not a statement; a harness tolerates it without noticing.
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN))
    out = tmp_path / "id.json"
    b.program(bit, verify_identity=False, identity_json=str(out))
    assert _record(out)["identity"]["status"] == "skipped"


def test_a_refusal_records_that_nothing_was_programmed(tmp_path, monkeypatch):
    # The sha256 here describes a bitstream that never reached the device. Without
    # `programmed`, the record would read as "this bitstream is on that board".
    b, bit = _programmable(tmp_path, monkeypatch, "DEADBEEF", parse_readback(CHAIN))
    out = tmp_path / "id.json"
    with pytest.raises(IdentityError):
        b.program(bit, identity_json=str(out))
    rec = _record(out)
    assert rec["programmed"] is False
    assert rec["identity"]["status"] == "wrong"


def test_a_failed_vivado_run_is_not_recorded_as_programmed(tmp_path, monkeypatch):
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN), vivado_rc=1)
    out = tmp_path / "id.json"
    with pytest.raises(RuntimeError):
        b.program(bit, identity_json=str(out))
    assert _record(out)["programmed"] is False


def test_record_directory_is_created(tmp_path, monkeypatch):
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN))
    out = tmp_path / "artifacts" / "run7" / "id.json"
    b.program(bit, identity_json=str(out))
    assert out.is_file()


def test_no_record_is_written_when_none_was_asked_for(tmp_path, monkeypatch):
    b, bit = _programmable(tmp_path, monkeypatch, GENESYS2_SERIAL,
                           parse_readback(CHAIN))
    b.program(bit)
    assert list(tmp_path.glob("*.json")) == []
