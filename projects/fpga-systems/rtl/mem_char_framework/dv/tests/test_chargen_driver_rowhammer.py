# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 seang galloway
"""Unit test for ChargenDriver.rowhammer() against a fake APB bus.

The macro sim suite proves the engines; this pins the HOST recipe the
methodology doc (docs/rowhammer_methodology.md) specifies:

  1. the recipe lands bit-exactly -- aggressor base = victim - row_pitch,
     stride_0 = 2 x row_pitch, BL1, hammer_en=1, data_mode=FILL with the
     given pattern; the victim readback walks the row expecting the victim
     pattern;
  2. phase order -- writer staged, one GO for the hammer, DONE polled, THEN
     the reader staged, one GO for the readback, ERR_BITS read last;
  3. the returned summary carries the reader's err_bits popcount plus the
     beat-level status;
  4. validation -- odd hammer_txns, misaligned victim, row_pitch that is not
     a whole number of beats, device-edge victims, bad generator index all
     raise BEFORE anything is staged;
  5. hygiene -- an ordinary program_writer() after a hammer run clears
     hammer_en and FILL_PATTERN, so recipe state never leaks into an
     unrelated run.

No simulator: the chargen_regs register file is modeled in-process over the
generated regmap, the same trick as bin/TBClasses/apb/tests/
test_register_map_walk.py.
"""

import asyncio
import contextlib
import io
import logging
import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, *([os.pardir] * 6)))
sys.path.insert(0, os.path.join(_REPO_ROOT, "bin"))
sys.path.insert(0, os.path.abspath(os.path.join(_HERE, "..", "tbclasses")))

import chargen_driver  # noqa: E402
from chargen_driver import ChargenDriver  # noqa: E402
from TBClasses.apb.register_map import RegisterMap  # noqa: E402

_REGMAP = os.path.abspath(os.path.join(_HERE, "..", "tbclasses",
                                       "chargen_regs_regmap.py"))


def _field(word: int, offset: str) -> int:
    """Extract a regmap field ('hi:lo' or single-bit offset) from a word."""
    if ":" not in offset:
        return (word >> int(offset)) & 1
    hi, lo = map(int, offset.split(":"))
    return (word >> lo) & ((1 << (hi - lo + 1)) - 1)


class FakeChargenApb:
    """APBMaster stand-in that models the chargen_regs register file.

    Latches only the sw-writable, non-pulse bits (GO's singlepulse bits read
    back 0; status registers read their default until hardware writes them).
    On GO, completes the selected generators the way the engines do: DONE
    roll-up, per-generator STATUS.done, and the scripted readback results.
    Records every packet in issue order so tests can assert phase order.
    """

    def __init__(self, entity=None, title: str = "", prefix: str = "",
                 clock=None, bus_width: int = 32, addr_width: int = 12,
                 log=None):
        self.log = log if log is not None else logging.getLogger("fake_apb")
        # RegisterMap dumps its dict to stdout at construction (a pprint in
        # the argument list of a debug call) -- keep the pytest output clean.
        with contextlib.redirect_stdout(io.StringIO()):
            self.rm = RegisterMap(_REGMAP, apb_data_width=bus_width,
                                  apb_addr_width=addr_width,
                                  start_address=0x0, log=self.log)
        self.mask = (1 << addr_width) - 1
        self.mem, self.latch, self.dflt = {}, {}, {}
        for name, reg in self.rm.registers.items():
            a = int(reg["address"], 16) & self.mask
            self.dflt[a] = self.rm.reg_default(reg)
            # Hardware latches only writable, non-pulse bits; the rest read
            # their default -- the same model the walk test builds.
            self.latch[a] = (self.rm.sw_writable_mask(reg)
                             & ~self.rm.nonlatching_mask(reg)) & 0xFFFF_FFFF
            self.mem[a] = self.dflt[a]
        self.by_addr = {int(reg["address"], 16) & self.mask: (name, reg)
                        for name, reg in self.rm.registers.items()}
        self.packets = []            # (pwrite, paddr, pwdata|None), in order
        self.auto_done = True
        self.bresp_error = set()     # writer gens that latch BRESP error
        # Scripted readback results, served when the reader's GO arrives.
        self.rd_err_bits = {}        # gen -> RD_GENg_ERR_BITS value
        self.rd_beats_mism = {}      # gen -> RD_GENg_BEATS_MISM value
        self.rd_data_error = set()   # gens whose reader latches data_error

    # -- the only two methods the driver calls -----------------------------

    async def reset_bus(self) -> None:
        pass

    async def busy_send(self, packet) -> None:
        addr = int(packet.paddr) & self.mask
        if int(packet.pwrite):
            data = int(packet.pwdata) & 0xFFFF_FFFF
            self.packets.append((1, addr, data))
            self.mem[addr] = (data & self.latch.get(addr, 0)) \
                | (self.dflt.get(addr, 0) & ~self.latch.get(addr, 0)
                   & 0xFFFF_FFFF)
            if addr == int(self.rm.registers["GO"]["address"], 16):
                self._on_go(data)
        else:
            self.packets.append((0, addr, None))
            packet.fields["prdata"] = self.mem.get(addr, 0)

    # -- the hardware behaviour the tests script ---------------------------

    def _on_go(self, word: int) -> None:
        done_a = int(self.rm.registers["DONE"]["address"], 16)
        err_a = int(self.rm.registers["ERRORS"]["address"], 16)
        for g in range(ChargenDriver.NUM_GEN):
            if (word >> g) & 1:                      # wr_gog pulse
                if not self.auto_done:
                    continue
                self.mem[done_a] |= 1 << g
                if g in self.bresp_error:
                    self.mem[err_a] |= 1 << g
            if (word >> (8 + g)) & 1:                # rd_gog pulse
                if not self.auto_done:
                    continue
                self.mem[done_a] |= 1 << (8 + g)
                st_a = int(self.rm.registers[f"RD_GEN{g}_STATUS"]["address"],
                           16)
                self.mem[st_a] |= 0x3                # done | crc_valid
                if g in self.rd_data_error:
                    self.mem[st_a] |= 0x4            # data_error
                self.mem[int(self.rm.registers[f"RD_GEN{g}_ERR_BITS"]
                             ["address"], 16)] = self.rd_err_bits.get(g, 0)
                self.mem[int(self.rm.registers[f"RD_GEN{g}_BEATS_MISM"]
                             ["address"], 16)] = self.rd_beats_mism.get(g, 0)

    # -- assertion helpers --------------------------------------------------

    def reg_word(self, name: str) -> int:
        return self.mem[int(self.rm.registers[name]["address"], 16)]

    def field(self, name: str, fld: str) -> int:
        return _field(self.reg_word(name),
                      self.rm.registers[name][fld]["offset"])

    def writes_to(self, reg_prefix: str) -> list[int]:
        addrs = {a for a, (n, _r) in self.by_addr.items()
                 if n.startswith(reg_prefix)}
        return [i for i, (wr, a, _d) in enumerate(self.packets)
                if wr and a in addrs]

    def reads_of(self, reg: str) -> list[int]:
        a = int(self.rm.registers[reg]["address"], 16) & self.mask
        return [i for i, (wr, ad, _d) in enumerate(self.packets)
                if not wr and ad == a]

    def go_writes(self) -> list[tuple[int, int]]:
        a = int(self.rm.registers["GO"]["address"], 16) & self.mask
        return [(i, d) for i, (wr, ad, d) in enumerate(self.packets)
                if wr and ad == a]


async def _noop_rising_edge(_clk):
    """RisingEdge replacement: an await that costs nothing."""


@pytest.fixture
def board(monkeypatch):
    """A ChargenDriver whose APB path is the fake register file."""
    monkeypatch.setattr(chargen_driver, "APBMaster", FakeChargenApb)
    monkeypatch.setattr(chargen_driver, "RisingEdge", _noop_rising_edge)
    with contextlib.redirect_stdout(io.StringIO()):
        drv = ChargenDriver(object(), clock=object(), prefix="s_chargen_apb",
                            addr_width=12, log=logging.getLogger("t"))
    return drv


VICTIM = 0x0008_0000
ROW_PITCH = 0x4000            # row_stride_same_bank on the ROW_MAJOR map
HAMMER_TXNS = 50_000
AGG_PATTERN = 0x00000000
VIC_PATTERN = 0xFFFFFFFF


def _run(coro):
    return asyncio.run(coro)


def test_rowhammer_double_sided_recipe_lands(board):
    fake = board.apb
    fake.rd_err_bits[1] = 37
    fake.rd_beats_mism[1] = 2
    fake.rd_data_error.add(1)

    result = _run(board.rowhammer(
        1, victim_addr=VICTIM, row_pitch=ROW_PITCH,
        hammer_txns=HAMMER_TXNS, aggressor_pattern=AGG_PATTERN,
        victim_pattern=VIC_PATTERN))

    # -- the recipe, bit level ------------------------------------------
    wr, rd = "WR_GEN1", "RD_GEN1"
    assert board.apb.field(wr + "_START_ADDR", "addr") == VICTIM - ROW_PITCH
    assert board.apb.field(wr + "_STRIDE_0", "stride") == 2 * ROW_PITCH
    assert board.apb.field(wr + "_STRIDE_1", "stride") == 0
    assert board.apb.field(wr + "_WRAP_MASK_0", "mask") == 0
    assert board.apb.field(wr + "_WRAP_MASK_1", "mask") == 0
    assert board.apb.field(wr + "_BLEN_TXN", "burst_len") == 1    # BL1
    assert board.apb.field(wr + "_BLEN_TXN", "txn_count") == HAMMER_TXNS
    assert board.apb.field(wr + "_BLEN_TXN", "gap") == 0
    assert board.apb.field(wr + "_AXI_ATTR", "data_mode") == 2    # FILL
    assert board.apb.field(wr + "_AXI_ATTR", "hammer_en") == 1
    assert board.apb.field(wr + "_AXI_ATTR", "axi_size") == 3
    assert board.apb.field(wr + "_AXI_ATTR", "axi_burst") == 1
    assert board.apb.field(wr + "_AXI_ATTR", "axi_id") == 1
    assert board.apb.field(wr + "_FILL_PATTERN", "pattern") == AGG_PATTERN

    assert board.apb.field(rd + "_START_ADDR", "addr") == VICTIM
    assert board.apb.field(rd + "_STRIDE_0", "stride") == 8       # one beat
    assert board.apb.field(rd + "_BLEN_TXN", "burst_len") == 1
    assert board.apb.field(rd + "_BLEN_TXN", "txn_count") \
        == ROW_PITCH // 8                                        # whole row
    assert board.apb.field(rd + "_AXI_ATTR", "data_mode") == 2
    assert board.apb.field(rd + "_AXI_ATTR", "hammer_en") == 0
    assert board.apb.field(rd + "_FILL_PATTERN", "pattern") == VIC_PATTERN

    # -- phase order: stage, GO, ..., stage, GO, read err_bits ------------
    wr_w = fake.writes_to(wr + "_")
    rd_w = fake.writes_to(rd + "_")
    gos = fake.go_writes()
    assert len(gos) == 2, f"expected one GO per phase, got {gos}"
    wr_go_i, wr_go_word = gos[0]
    rd_go_i, rd_go_word = gos[1]
    assert wr_go_word & 0xFF == 1 << 1, "hammer GO must start writer 1 only"
    assert (rd_go_word >> 8) & 0xFF == 1 << 1, "readback GO must start reader 1 only"
    err_reads = fake.reads_of(rd + "_ERR_BITS")
    assert max(wr_w) < wr_go_i < min(rd_w)
    assert max(rd_w) < rd_go_i < min(err_reads)

    # -- the summary --------------------------------------------------------
    assert result["gen"] == 1
    assert result["double_sided"] is True
    assert result["aggressor_base"] == VICTIM - ROW_PITCH
    assert result["aggressor_stride"] == 2 * ROW_PITCH
    assert result["hammer_txns"] == HAMMER_TXNS
    assert result["victim_addr"] == VICTIM
    assert result["victim_beats"] == ROW_PITCH // 8
    assert result["err_bits"] == 37, "the popcount is the observable"
    assert result["beats_mismatched"] == 2
    assert result["data_error"] is True
    assert result["rresp_error"] is False
    assert result["stray_beat_error"] is False


def test_rowhammer_single_sided_uses_one_aggressor(board):
    fake = board.apb
    _run(board.rowhammer(
        0, victim_addr=VICTIM, row_pitch=ROW_PITCH, hammer_txns=64,
        aggressor_pattern=0xFFFFFFFF, double_sided=False))

    assert fake.field("WR_GEN0_START_ADDR", "addr") == VICTIM + ROW_PITCH
    assert fake.field("WR_GEN0_STRIDE_0", "stride") == 0
    assert fake.field("WR_GEN0_AXI_ATTR", "hammer_en") == 1
    # Readback is identical to the double-sided case: walk the victim row.
    assert fake.field("RD_GEN0_START_ADDR", "addr") == VICTIM


def test_program_clears_stale_hammer_state(board):
    fake = board.apb
    _run(board.rowhammer(
        1, victim_addr=VICTIM, row_pitch=ROW_PITCH, hammer_txns=64,
        aggressor_pattern=0xFFFFFFFF))
    assert fake.field("WR_GEN1_AXI_ATTR", "hammer_en") == 1

    # An ordinary run afterwards must not inherit the recipe: hammer_en and
    # FILL_PATTERN are written on every program call, exactly like strides.
    _run(board.program_writer(1, start_addr=0x1000, txn_count=4))
    assert fake.field("WR_GEN1_AXI_ATTR", "hammer_en") == 0
    assert fake.field("WR_GEN1_AXI_ATTR", "data_mode") == 0
    assert fake.field("WR_GEN1_FILL_PATTERN", "pattern") == 0
    assert fake.field("WR_GEN1_START_ADDR", "addr") == 0x1000


_BAD_GEOMETRY = [
    # (id, kwargs overrides)
    ("odd_txns", dict(hammer_txns=63)),
    ("zero_txns", dict(hammer_txns=0)),
    ("txns_over_16_bits", dict(hammer_txns=0x1_0000)),
    ("mid_row_victim", dict(victim_addr=VICTIM + 8)),
    ("pitch_not_beats", dict(row_pitch=12)),
    ("zero_pitch", dict(row_pitch=0)),
    ("no_row_below", dict(victim_addr=0)),
    ("stride_over_24_bit", dict(victim_addr=0x400000, row_pitch=0x400000)),
    ("walk_over_16_bit", dict(victim_addr=0x100000, row_pitch=0x100000)),
    ("upper_wrap", dict(victim_addr=0xFFFF_F000, row_pitch=0x1000)),
]
_BAD_GEOMETRY_IDS = [r[0] for r in _BAD_GEOMETRY]
_BAD_GEOMETRY_KW = [r[1] for r in _BAD_GEOMETRY]


@pytest.mark.parametrize("overrides", _BAD_GEOMETRY_KW, ids=_BAD_GEOMETRY_IDS)
def test_rowhammer_rejects_bad_geometry(board, overrides):
    kwargs = dict(victim_addr=VICTIM, row_pitch=ROW_PITCH, hammer_txns=64,
                  aggressor_pattern=0)
    kwargs.update(overrides)
    with pytest.raises(ValueError):
        _run(board.rowhammer(1, **kwargs))
    assert board.apb.packets == [], "a rejected recipe must not touch the bus"


def test_rowhammer_rejects_edge_victim_single_sided(board):
    with pytest.raises(ValueError):
        _run(board.rowhammer(
            1, victim_addr=0xFFFF_F000, row_pitch=0x1000, hammer_txns=64,
            aggressor_pattern=0, double_sided=False))
    assert board.apb.packets == []


def test_rowhammer_rejects_bad_generator(board):
    with pytest.raises(IndexError):
        _run(board.rowhammer(
            ChargenDriver.NUM_GEN, victim_addr=VICTIM, row_pitch=ROW_PITCH,
            hammer_txns=64, aggressor_pattern=0))
    assert board.apb.packets == []


def test_rowhammer_times_out_when_engine_never_finishes(board):
    board.apb.auto_done = False
    with pytest.raises(TimeoutError):
        _run(board.rowhammer(
            1, victim_addr=VICTIM, row_pitch=ROW_PITCH, hammer_txns=64,
            aggressor_pattern=0, timeout=5))
    # The writer staged and launched; the reader never did.
    gos = board.apb.go_writes()
    assert len(gos) == 1 and gos[0][1] & 0xFF == 1 << 1


def test_rowhammer_bresp_error_aborts_before_readback(board):
    board.apb.bresp_error.add(1)
    with pytest.raises(RuntimeError, match="BRESP"):
        _run(board.rowhammer(
            1, victim_addr=VICTIM, row_pitch=ROW_PITCH, hammer_txns=64,
            aggressor_pattern=0))
    gos = board.apb.go_writes()
    assert len(gos) == 1, "a BRESP error must stop the recipe before readback"
