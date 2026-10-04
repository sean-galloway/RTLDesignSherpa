# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_addr_mapper` -- flat AXI address to (rank,bank,row,col).

pumice's equivalent test compares the RTL against a Python `decode_ref` that
was written from the same mental model as the RTL. That is the shape that let
andesite's mode-register bug live: the encoder and the decoder agreed with each
other, and the pair was wrong. So the checks here are mostly PROPERTIES of the
geometry rather than a re-implementation of the shifts:

  * INJECTIVITY. The map must be one-to-one over the device's address space. A
    field that overlaps its neighbour, a column that fails to reassemble, or a
    bank hash that folds two addresses together all show up as a collision,
    and none of them need a reference model to detect. This is the check that
    matters: a non-injective map silently aliases two AXI addresses onto one
    DRAM location, which corrupts data rather than slowing it down.
  * PAGE CONTIGUITY. Ascending addresses must walk a page's columns in order
    before leaving the page -- that is the whole point of the row-major
    setting, and a bank field in the wrong place breaks it.
  * BYTE-OFFSET INVARIANCE. The low BYTE_OFFSET_WIDTH bits are lane select,
    carried by WSTRB, and must not move the column.

A small reference appears only for row-major (`bank_lsb == COL_WIDTH`), where
the field boundaries are unambiguous from the geometry alone -- col is the low
CW bits of the word address, bank the next BW, row the next RW -- and the
hand-written vectors in `genesys2_vectors` are computed from the Genesys 2
design point (2x MT41J256M16, 32-bit bus, row 15 / col 10 / bank 3, so
BYTE_OFFSET_WIDTH = 2, 4 KiB page, 1 GiB device), not from this RTL.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

# The Genesys 2 design point, mirrored into the pytest parameters below.
AW, RW, CW, BW, BO = 32, 15, 10, 3, 2
BGW = 2   # andesite: bank-group field above bank (BG_WIDTH)
PAGE_BYTES = (1 << CW) << BO            # 4 KiB
WORD_BYTES = 1 << BO                    # 4


class AmTB(TBBase):
    """No clock and no reset: the mapper is one combinational stage.

    The three mandatory TB methods are present because every TB in this repo
    has them, but there is nothing for them to drive -- the module has neither
    a clock nor a reset port. Settling is a Timer, not an edge.
    """

    async def setup_clocks_and_reset(self):
        await self.cfg()

    async def assert_reset(self):
        pass

    async def deassert_reset(self):
        pass

    async def cfg(self, *, bank_lsb=CW, hash_en=0, hash_seed=0):
        self.dut.bank_lsb_i.value = bank_lsb
        self.dut.hash_en_i.value = hash_en
        self.dut.hash_seed_i.value = hash_seed
        self.dut.axi_addr_i.value = 0
        await Timer(1, 'ns')

    async def decode(self, addr):
        """Drive one address; return (rank, bank, row, col); bg in last_bg."""
        self.dut.axi_addr_i.value = addr
        await Timer(1, 'ns')
        d = self.dut
        self.last_bg = int(d.bg_o.value)
        return (int(d.rank_o.value), int(d.bank_o.value),
                int(d.row_o.value), int(d.col_o.value))

    async def decode5(self, addr):
        """decode() with bg in the tuple -- for injectivity/permutation keys."""
        t = await self.decode(addr)
        return (t[0], t[1], self.last_bg, t[2], t[3])


def ref_row_major(addr, *, nbanks=1 << BW):
    """Row-major decode from the GEOMETRY, independent of the RTL's shifts.

    Word address = addr >> BO. The column is the low CW bits (one page), the
    bank the next BW, the row the next RW. This is the only setting whose field
    boundaries the geometry fixes on its own, so it is the only one with a
    reference here.
    """
    w = addr >> BO
    col = w & ((1 << CW) - 1)
    bank = (w >> CW) % nbanks
    bg = (w >> (CW + BW)) & ((1 << BGW) - 1)
    row = (w >> (CW + BW + BGW)) & ((1 << RW) - 1)
    return bank, bg, row, col


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_andesite_addr_mapper(dut):
    tt = os.environ.get("TEST_TYPE", "genesys2_vectors")
    nranks = int(os.environ.get("NUM_RANKS", "1"))
    tb = AmTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "genesys2_vectors":
        # Hand-computed against the board's geometry: 32-bit bus, 4 KiB page,
        # 8 banks, 15-bit row. Every number below comes from the datasheet
        # organisation, not from reading this RTL.
        await tb.cfg(bank_lsb=CW)
        # andesite geometry: bank, then BANK GROUP (BGW=2), then row -- bg
        # absorbs what the DDR3 map spent on row bits.
        vectors = [
            (0x0000_0000, (0, 0, 0, 0)),          # origin
            (0x0000_0004, (0, 0, 0, 1)),          # +1 device word -> +1 column
            (0x0000_0FFC, (0, 0, 0, 1023)),       # last column of the page
            (0x0000_1000, (1, 0, 0, 0)),          # +4 KiB -> next BANK
            (0x0000_7000, (7, 0, 0, 0)),          # last bank of the group
            (0x0000_8000, (0, 1, 0, 0)),          # +32 KiB -> next BANK GROUP
            (0x0001_0000, (0, 2, 0, 0)),
            (0x3FFF_8000, (0, 3, 0x1FFF, 0)),     # top row within a group
        ]
        for addr, (eb, ebg, er, ec) in vectors:
            _, b, r, c = await tb.decode(addr)
            g = tb.last_bg
            chk((b, g, r, c) == (eb, ebg, er, ec),
                f"0x{addr:08X}: got bank={b} bg={g} row={r} col={c}, expected "
                f"bank={eb} bg={ebg} row={er} col={ec} (32-bit bus, "
                f"{PAGE_BYTES // 1024} KiB page, 8 banks, {BGW} bg bits)")

    elif tt == "byte_offset_is_ignored":
        # The low BO bits select lanes inside a device word and are carried by
        # WSTRB. If they reached the column, an unaligned beat would land one
        # column on and leave the requested address untouched.
        await tb.cfg(bank_lsb=CW)
        rng = random.Random(7)
        for _ in range(40):
            base = rng.randrange(0, 1 << 28) << BO
            want = await tb.decode(base)
            for off in range(1, WORD_BYTES):
                got = await tb.decode(base + off)
                chk(got == want,
                    f"0x{base + off:08X} decodes to {got} but 0x{base:08X} "
                    f"(same device word) decodes to {want} -- byte lanes "
                    f"inside a word must not move the column")
            nxt = await tb.decode(base + WORD_BYTES)
            chk(nxt != want,
                f"0x{base + WORD_BYTES:08X} decodes identically to "
                f"0x{base:08X}; the next device word must be a new location")

    elif tt == "row_major_page_walk":
        # Ascending addresses must exhaust a page's columns IN ORDER before
        # touching another bank. A bank field one bit low splits the page.
        await tb.cfg(bank_lsb=CW)
        for page in (0, 5, 8, 137):
            base = page * PAGE_BYTES
            eb, ebg, er, _ = ref_row_major(base)
            for i in range(0, 1 << CW, 37):
                _, b, r, c = await tb.decode(base + i * WORD_BYTES)
                chk((b, tb.last_bg, r, c) == (eb, ebg, er, i),
                    f"page {page} word {i}: got bank={b} row={r} col={c}, "
                    f"expected bank={eb} row={er} col={i} -- a page must be "
                    f"one bank's contiguous column run")

    elif tt == "row_major_matches_geometry":
        await tb.cfg(bank_lsb=CW)
        rng = random.Random(11)
        for _ in range(300):
            addr = rng.randrange(0, 1 << 30)
            _, b, r, c = await tb.decode(addr)
            eb, ebg, er, ec = ref_row_major(addr)
            chk((b, tb.last_bg, r, c) == (eb, ebg, er, ec),
                f"0x{addr:08X}: got bank={b} row={r} col={c}, geometry says "
                f"bank={eb} row={er} col={ec}")

    elif tt == "injective_across_bank_lsb":
        # THE check. For every legal bank_lsb, the map over a contiguous chunk
        # of the device must be one-to-one: two AXI addresses sharing a DRAM
        # location is silent corruption, and it needs no reference model to
        # see. 4 banks' worth of pages covers every field boundary the knob
        # can move.
        n = 2048
        for blsb in range(0, CW + 1):
            await tb.cfg(bank_lsb=blsb)
            seen = {}
            for i in range(n):
                addr = i * WORD_BYTES
                t = await tb.decode5(addr)
                if t in seen:
                    chk(False,
                        f"bank_lsb={blsb}: 0x{addr:08X} and 0x{seen[t]:08X} "
                        f"both decode to {t} -- the map is not one-to-one and "
                        f"two AXI addresses share one DRAM location")
                    break
                seen[t] = addr
            chk(len(seen) == n or fails,
                f"bank_lsb={blsb}: {len(seen)} distinct locations for {n} "
                f"addresses")

    elif tt == "bank_interleave_spreads":
        # bank_lsb below COL_WIDTH inserts the bank into the column, so
        # consecutive BURST-sized runs land on consecutive banks. That is the
        # entire purpose of the setting: a linear stream hits every bank
        # instead of serialising on one.
        burst = 8                       # device words per DRAM burst
        # Minimal col_lo == the burst's OWN column bits, i.e.
        # bank_lsb = log2(burst), measured in minimum_bank_lsb_is_measured.
        # BOTH written-down versions of that bound were wrong, in opposite
        # directions, and both are corrected now: the module header said
        # `log2(cols/burst)` (7 here -- too restrictive, interleaves every 512
        # bytes instead of every burst) and the RDL said `log2(BL/DFI_RATE)`
        # (1 here -- too permissive, and at that setting an 8-word burst spans
        # four banks). Doc bugs, not RTL: the knob does what it says.
        blsb = 3                        # log2(burst)
        await tb.cfg(bank_lsb=blsb)
        banks = []
        for k in range(8):
            _, b, r, c = await tb.decode(k * burst * WORD_BYTES)
            banks.append(b)
        chk(sorted(banks) == list(range(8)),
            f"bank_lsb={blsb}: the first 8 bursts hit banks {banks}; an "
            f"interleaving map must spread a linear stream over all 8, or the "
            f"setting buys nothing over row-major")
        # And a burst never straddles banks -- the software constraint
        # log2(DRAM_BL) <= bank_lsb exists to guarantee exactly this.
        for k in (0, 3, 6):
            base = k * burst * WORD_BYTES
            bset = set()
            for i in range(burst):
                _, b, _, _ = await tb.decode(base + i * WORD_BYTES)
                bset.add(b)
            chk(len(bset) == 1,
                f"burst at 0x{base:08X} spans banks {sorted(bset)} -- a DRAM "
                f"burst walks columns inside ONE bank")

    elif tt == "minimum_bank_lsb_is_measured":
        # MEASURE the software constraint instead of restating it. The bound
        # that keeps a DRAM burst inside one bank is a property of the geometry,
        # and both andesite_csr.rdl and the module header state it as a FORMULA --
        # so the formula is what gets checked here, by finding the smallest
        # bank_lsb at which an aligned burst does not straddle banks.
        #
        # One JEDEC burst is DRAM_BL columns at this mapper's granularity: the
        # mapper indexes device words (BYTE_OFFSET_WIDTH = log2(device bytes))
        # and andesite_core derives SUB_COL_STRIDE = DRAM_BL in exactly those
        # units. So the minimum should be log2(DRAM_BL) -- NOT
        # log2(DRAM_BL/DFI_RATE), which is log2(DFI_RATE) bits too permissive
        # and is what both comments say.
        for burst in (4, 8, 16):
            smallest = None
            for blsb in range(0, CW + 1):
                await tb.cfg(bank_lsb=blsb)
                ok = True
                for base_i in (0, 1, 7, 64):
                    base = base_i * burst * WORD_BYTES
                    banks = set()
                    for i in range(burst):
                        _, b, _, _ = await tb.decode(base + i * WORD_BYTES)
                        banks.add(b)
                    if len(banks) != 1:
                        ok = False
                        break
                if ok:
                    smallest = blsb
                    break
            want = burst.bit_length() - 1          # log2(burst)
            tb.log.info(f"burst={burst} words: smallest bank_lsb keeping it in "
                        f"one bank = {smallest} (log2(burst) = {want})")
            chk(smallest == want,
                f"burst={burst}: measured minimum bank_lsb {smallest}, "
                f"geometry says log2(burst)={want}. If this is now lower, a "
                f"burst spans banks at the stated minimum and the constraint "
                f"in andesite_csr.rdl is unsafe to follow.")

    elif tt == "clamp_above_col_width":
        # Software is constrained to bank_lsb <= COL_WIDTH; the RTL clamps so a
        # bad value cannot produce a negative col_hi width. An unclamped shift
        # would drop column bits, which aliases addresses.
        await tb.cfg(bank_lsb=CW)
        rng = random.Random(3)
        addrs = [rng.randrange(0, 1 << 30) for _ in range(60)]
        want = [await tb.decode(a) for a in addrs]
        for bad in (CW + 1, CW + 7, 31):
            await tb.cfg(bank_lsb=bad)
            for a, w in zip(addrs, want):
                got = await tb.decode(a)
                chk(got == w,
                    f"bank_lsb={bad} (> COL_WIDTH={CW}) decodes 0x{a:08X} to "
                    f"{got}; the clamp must make it behave as bank_lsb={CW}, "
                    f"expected {w}")

    elif tt == "hash_off_is_the_raw_field":
        # The OFF state needs its own case: with hash_en=0 the bank must be the
        # plain address field, seed and all. A hash that leaks when disabled
        # scrambles the map the software thinks it programmed.
        await tb.cfg(bank_lsb=CW, hash_en=0, hash_seed=0xA5)
        rng = random.Random(5)
        for _ in range(200):
            addr = rng.randrange(0, 1 << 30)
            _, b, r, c = await tb.decode(addr)
            eb, ebg, er, ec = ref_row_major(addr)
            chk((b, tb.last_bg, r, c) == (eb, ebg, er, ec),
                f"hash_en=0 seed=0xA5, 0x{addr:08X}: got bank={b} row={r} "
                f"col={c}, expected the raw fields bank={eb} row={er} "
                f"col={ec} -- a disabled hash must not touch the bank")

    elif tt == "hash_on_is_active_and_injective":
        # Two claims, and the second is the load-bearing one. A hash that
        # changes nothing is dead logic; a hash that collides costs addresses.
        rng = random.Random(9)
        addrs = [i * PAGE_BYTES for i in range(512)]
        await tb.cfg(bank_lsb=CW, hash_en=0)
        raw = [await tb.decode5(a) for a in addrs]
        for seed in (0x00, 0x03, 0xFF):
            await tb.cfg(bank_lsb=CW, hash_en=1, hash_seed=seed)
            hashed = [await tb.decode5(a) for a in addrs]
            moved = sum(1 for x, y in zip(raw, hashed) if x[1] != y[1])
            chk(moved > 0,
                f"hash_en=1 seed=0x{seed:02X} left every bank unchanged -- the "
                f"XOR-hash exists to break power-of-two-stride hot-banking and "
                f"is doing nothing")
            for (_, _, _, r0, c0), (_, _, _, r1, c1), a in zip(raw, hashed, addrs):
                chk((r0, c0) == (r1, c1),
                    f"seed=0x{seed:02X}: 0x{a:08X} row/col moved from "
                    f"({r0},{c0}) to ({r1},{c1}) -- the hash folds into the "
                    f"BANK only")
            seen = {}
            for a, t in zip(addrs, hashed):
                if t in seen:
                    chk(False,
                        f"seed=0x{seed:02X}: 0x{a:08X} and 0x{seen[t]:08X} "
                        f"both hash to {t} -- the fold must be a permutation "
                        f"of the bank index, not a many-to-one hash")
                    break
                seen[t] = a

    elif tt == "rank_field_sits_above_row":
        # REQUIRES NUM_RANKS=2. The rank is the top field, so it changes only
        # at the device boundary. andesite: the bg field sits between bank and
        # row, so this build narrows ROW_WIDTH by BGW (the runner passes
        # RW-BGW) to keep the 1 GiB boundary inside the 32-bit bus.
        chk(nranks == 2, f"case needs NUM_RANKS=2, built with {nranks}")
        await tb.cfg(bank_lsb=CW)
        dev_words = 1 << (CW + BW + BGW + (RW - BGW))
        dev_bytes = dev_words << BO
        chk(dev_bytes == 1 << 30,
            f"geometry says {dev_bytes} bytes per rank; the design point is "
            f"exactly 1 GiB")
        for addr, exp in ((0, 0), (dev_bytes - WORD_BYTES, 0),
                          (dev_bytes, 1), (dev_bytes + PAGE_BYTES, 1)):
            k, _, _, _ = await tb.decode(addr)
            chk(k == exp,
                f"0x{addr:08X}: rank {k}, expected {exp} -- the rank field is "
                f"above the row, so it flips at the {dev_bytes >> 30} GiB "
                f"device boundary")
        # The second rank repeats the first rank's (bank,row,col) exactly.
        for i in (0, 1, 1234):
            a = i * PAGE_BYTES
            k0, b0, r0, c0 = await tb.decode(a)
            k1, b1, r1, c1 = await tb.decode(a + dev_bytes)
            chk((k0, k1) == (0, 1) and (b0, r0, c0) == (b1, r1, c1),
                f"0x{a:08X} -> rank{k0} ({b0},{r0},{c0}) but +1 GiB -> "
                f"rank{k1} ({b1},{r1},{c1}); the ranks are identical devices")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '23')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        rounds = {"GATE": 6, "FUNC": 20, "FULL": 60}.get(lvl, 20)
        for _ in range(rounds):
            blsb = rng.randrange(0, CW + 1)
            hen = rng.randint(0, 1)
            seed = rng.randrange(0, 256)
            await tb.cfg(bank_lsb=blsb, hash_en=hen, hash_seed=seed)
            # A contiguous window, so injectivity is a real claim about the
            # field layout rather than luck over a sparse sample.
            # 2^18 pages * 4 KiB = the 1 GiB device; larger overflows
            # axi_addr_i and the assignment raises rather than wraps.
            base = rng.randrange(0, (1 << 18) - 1) * PAGE_BYTES
            seen = {}
            for i in range(256):
                a = base + i * WORD_BYTES
                t = await tb.decode5(a)
                if t in seen:
                    chk(False,
                        f"bank_lsb={blsb} hash={hen} seed=0x{seed:02X}: "
                        f"0x{a:08X} and 0x{seen[t]:08X} both decode to {t}")
                    break
                seen[t] = a
            # The row never depends on the bank knob or the hash: its LSB is
            # invariant at CW+BW by construction, and the CAMs rely on that.
            _, _, r_now, _ = await tb.decode(base)
            await tb.cfg(bank_lsb=CW, hash_en=0)
            _, _, r_ref, _ = await tb.decode(base)
            chk(r_now == r_ref,
                f"bank_lsb={blsb} hash={hen}: row {r_now} at 0x{base:08X} but "
                f"{r_ref} with the knobs at rest -- the row position is "
                f"INVARIANT, only the bank moves")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["genesys2_vectors", "byte_offset_is_ignored", "injective_across_bank_lsb"]
_FUNC = _GATE + ["minimum_bank_lsb_is_measured", "row_major_page_walk", "row_major_matches_geometry",
                 "bank_interleave_spreads", "clamp_above_col_width",
                 "hash_off_is_the_raw_field",
                 "hash_on_is_active_and_injective",
                 "rank_field_sits_above_row", "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_addr_mapper(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_addr_mapper"
    test_name = f"test_andesite_addr_mapper_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_addr_mapper.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    nranks = 2 if test_type == "rank_field_sits_above_row" else 1
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_addr_mapper",
        sim_build=sim_build, simulator="verilator",
        parameters={"AXI_ADDR_WIDTH": str(AW), "NUM_RANKS": str(nranks),
                    "NUM_BANKS": str(1 << BW),
                    # andesite: the 2-rank build narrows the row field by the
                    # bg width so the device boundary stays reachable on the
                    # 32-bit bus (rank case computes the same boundary).
                    "ROW_WIDTH": str(RW - BGW if nranks == 2 else RW),
                    "COL_WIDTH": str(CW), "BYTE_OFFSET_WIDTH": str(BO)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "NUM_RANKS": str(nranks),
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
