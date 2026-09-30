# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_mode_register` -- MR storage plus the DDR3 live decode.

Adapted from pumice's test_mode_register, but the DDR3 decodes are NOT the DDR2
ones and three of them are where this module is most likely to be wrong:

  CL   MR0[6:4] with MR0[2] as the HIGH bit. A DDR2-shaped test would only ever
       drive [6:4] and would never notice bit 2 was ignored.
  CWL  MR2[5:3] + 5. DDR3 does NOT tie CWL = CL-1 the way DDR2 does, so a test
       that asserts cwl == cl-1 passes on DDR2 and is meaningless here.
  WR   MR0[11:9], and the encoding is NOT MONOTONIC -- 000 is 16, not 4. A
       linear formula fits seven of the eight points, which is exactly the
       shape of bug that survives a sweep that starts at 001.

The encoders below are written from JESD79-3F, independently of the RTL's
decode. That is the point: an encoder derived from the decode would agree with
it whatever either says.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

MEMTYPE_DDR3   = 0
MEMTYPE_LPDDR3 = 1

#: JESD79-3F Table: MR0[11:9] -> tWR in cycles. Transcribed from the spec, not
#: from the RTL. 000 == 16 is the non-monotonic entry.
WR_TABLE = {0b000: 16, 0b001: 5, 0b010: 6, 0b011: 7,
            0b100: 8, 0b101: 10, 0b110: 12, 0b111: 14}


def enc_mr0(*, cl: int = 5, wr_code: int = 0b001, bl_code: int = 0b00) -> int:
    """MR0: CL split across [6:4] and [2], WR at [11:9], BL at [1:0].

    CL encoding is purely arithmetic per JESD79-3F Figure 9: {A6,A5,A4} = CL-4
    with A2 as a +8 high bit. So CL 5 is 001, CL 11 is 111, CL 12 is 000 with
    A2=1, CL 14 is 010 with A2=1. [6:4]==000 with A2=0 is RESERVED.

    This function ORIGINALLY special-cased CL 5 to 000 -- mirroring a special
    case the RTL had rather than reading the table -- so the encoder and the
    decoder shared one mistake and agreed with each other. That is precisely
    the failure an "independent" encoder is supposed to prevent, and it is why
    the first version of this test passed while CL 12 was unreachable.
    """
    v = cl - 4
    cl_lo, cl_hi = v & 0x7, 1 if v & 0x8 else 0
    return ((wr_code & 0x7) << 9) | ((cl_lo & 0x7) << 4) \
        | ((cl_hi & 1) << 2) | (bl_code & 0x3)


def enc_mr1(*, al_code: int = 0, wrlvl: int = 0) -> int:
    """MR1: AL at [4:3], write-leveling enable at [7] (A7)."""
    return ((wrlvl & 1) << 7) | ((al_code & 0x3) << 3)


def enc_mr2(*, cwl: int = 5) -> int:
    """MR2: CWL-5 at [5:3]."""
    return ((cwl - 5) & 0x7) << 3


class MrTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_RANKS = int(os.environ.get("NUM_RANKS", "1"))

    async def setup(self, memtype: int):
        await self.start_clock('mc_clk', 10, 'ns')
        self.dut.memtype_i.value = memtype
        self.dut.mr_we_i.value = 0
        self.dut.mr_index_i.value = 0
        self.dut.mr_data_i.value = 0
        self.dut.mr_rank_i.value = 0
        self.dut.mr_grant_i.value = 1
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 5)

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup(MEMTYPE_DDR3)

    async def write_mr(self, rank: int, idx: int, data: int):
        self.dut.mr_rank_i.value = rank
        self.dut.mr_index_i.value = idx
        self.dut.mr_data_i.value = data
        self.dut.mr_we_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        self.dut.mr_we_i.value = 0
        await RisingEdge(self.dut.mc_clk)

    def live(self):
        return {
            'cl':       int(self.dut.cl_o.value),
            'cwl':      int(self.dut.cwl_o.value),
            'bl':       int(self.dut.bl_o.value),
            'al':       int(self.dut.al_o.value),
            'wr':       int(self.dut.wr_o.value),
            'wrlvl_en': int(self.dut.wrlvl_en_o.value),
        }


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_scoria_mode_register(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_ddr3")
    tb = MrTB(dut)
    fails = []

    def chk(cond, msg):
        if not cond:
            fails.append(msg)
            tb.log.error(msg)

    if test_type == "smoke_ddr3":
        # The board's own calibrated numbers: the LiteDRAM BIOS reported
        # "1.0GiB 32-bit @ 800MT/s (CL-6 CWL-5)" on this exact part, so these
        # are measured values, not a datasheet pick.
        await tb.setup(MEMTYPE_DDR3)
        await tb.write_mr(0, 0, enc_mr0(cl=6, wr_code=0b100))   # WR 8
        await tb.write_mr(0, 1, enc_mr1(al_code=0))
        await tb.write_mr(0, 2, enc_mr2(cwl=5))
        await tb.wait_clocks('mc_clk', 2)
        lv = tb.live()
        chk(lv['cl'] == 6,  f"CL: got {lv['cl']}, expected 6 (board-reported)")
        chk(lv['cwl'] == 5, f"CWL: got {lv['cwl']}, expected 5 (board-reported)")
        chk(lv['wr'] == 8,  f"WR: got {lv['wr']}, expected 8")
        chk(lv['bl'] == 8,  f"BL: got {lv['bl']}, expected 8 (DDR3 fixed BL8)")

    elif test_type == "ddr3_cl_sweep":
        # CL 5..14. Stopping at 11 was a REAL hole: cl-4 fits in three bits up
        # to 11, so MR0[2] -- the CL high bit -- is never driven and a decode
        # that ignores it passes the whole sweep. Mutation-tested: deleting the
        # `+ (w_mr0[2] ? 8 : 0)` term from the RTL passed a 5..11 sweep and
        # fails this one. CL 5 is separately the 000 special case.
        await tb.setup(MEMTYPE_DDR3)
        for cl in range(5, 15):
            await tb.write_mr(0, 0, enc_mr0(cl=cl))
            await tb.wait_clocks('mc_clk', 2)
            got = tb.live()['cl']
            chk(got == cl, f"CL={cl}: got {got}"
                           + ("  <- needs MR0[2]" if cl >= 12 else ""))

    elif test_type == "ddr3_cwl_independent_of_cl":
        # The check DDR2 cannot express: CWL must NOT track CL.
        await tb.setup(MEMTYPE_DDR3)
        await tb.write_mr(0, 0, enc_mr0(cl=10))
        for cwl in range(5, 13):
            await tb.write_mr(0, 2, enc_mr2(cwl=cwl))
            await tb.wait_clocks('mc_clk', 2)
            lv = tb.live()
            chk(lv['cwl'] == cwl, f"CWL={cwl}: got {lv['cwl']}")
            chk(lv['cl'] == 10,
                f"CWL={cwl} perturbed CL: got {lv['cl']}, expected 10")
        chk(tb.live()['cwl'] != tb.live()['cl'] - 1
            or True, "")   # informational; the per-point checks are the test

    elif test_type == "ddr3_wr_table":
        # EVERY code, including 000 -> 16. A linear fit passes 7 of 8.
        await tb.setup(MEMTYPE_DDR3)
        for code, want in sorted(WR_TABLE.items()):
            await tb.write_mr(0, 0, enc_mr0(cl=6, wr_code=code))
            await tb.wait_clocks('mc_clk', 2)
            got = tb.live()['wr']
            chk(got == want,
                f"WR code {code:03b}: got {got}, expected {want} (JESD79-3F)")

    elif test_type == "ddr3_wrlvl_en":
        # MR1[7] drives wrlvl_en_o, and only on DDR3.
        await tb.setup(MEMTYPE_DDR3)
        await tb.write_mr(0, 1, enc_mr1(wrlvl=0))
        await tb.wait_clocks('mc_clk', 2)
        chk(tb.live()['wrlvl_en'] == 0, "wrlvl_en set with MR1[7]=0")
        await tb.write_mr(0, 1, enc_mr1(wrlvl=1))
        await tb.wait_clocks('mc_clk', 2)
        chk(tb.live()['wrlvl_en'] == 1, "wrlvl_en clear with MR1[7]=1")
        await tb.write_mr(0, 1, enc_mr1(wrlvl=0))
        await tb.wait_clocks('mc_clk', 2)
        chk(tb.live()['wrlvl_en'] == 0, "wrlvl_en stuck after MR1[7] cleared")

    elif test_type == "lpddr3_wr_is_zero":
        # LPDDR3 carries tWR in its own MR/CSR, so wr_o must read 0 regardless
        # of what MR0[11:9] holds -- a DDR3 table leaking into LPDDR3 would be
        # invisible on the DDR3 path.
        await tb.setup(MEMTYPE_LPDDR3)
        await tb.write_mr(0, 0, enc_mr0(cl=6, wr_code=0b110))
        await tb.wait_clocks('mc_clk', 2)
        got = tb.live()['wr']
        chk(got == 0, f"LPDDR3 wr_o: got {got}, expected 0")
        chk(tb.live()['wrlvl_en'] == 0, "LPDDR3 must never assert wrlvl_en")

    elif test_type == "ddr3_al_tracks_cl":
        await tb.setup(MEMTYPE_DDR3)
        await tb.write_mr(0, 0, enc_mr0(cl=8))
        for code, expect in ((0b00, 0), (0b01, 7), (0b10, 6), (0b11, 0)):
            await tb.write_mr(0, 1, enc_mr1(al_code=code))
            await tb.wait_clocks('mc_clk', 2)
            got = tb.live()['al']
            chk(got == expect, f"AL code {code:02b}: got {got}, expected {expect}")

    elif test_type == "reset_values":
        await tb.setup(MEMTYPE_DDR3)
        lv = tb.live()
        # MR0 = 0 -> CL field 000 with A2=0, which JESD79-3F Figure 9 lists as
        # RESERVED. The arithmetic decode yields 4, not a legal DDR3 CL, and
        # that is deliberate: the init sequencer programs MR0 before anything
        # consumes cl_o, and a reserved code returning a plausible 5 hid the
        # fact that CL 12 was unreachable.
        chk(lv['cl'] == 4,
            f"reset CL: got {lv['cl']}, expected 4 (000/A2=0 is reserved)")
        chk(lv['wr'] == 16, f"reset WR: got {lv['wr']}, expected 16 (000 is 16)")
        chk(lv['bl'] == 8,  f"reset BL: got {lv['bl']}, expected 8")
        chk(lv['wrlvl_en'] == 0, "reset wrlvl_en must be 0")

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 50, "FUNC": 200, "FULL": 1000}.get(lvl, 200)
        await tb.setup(MEMTYPE_DDR3)
        for _ in range(n):
            await tb.write_mr(rng.randint(0, tb.NUM_RANKS - 1),
                              rng.randint(0, 3), rng.randrange(0x10000))
            await tb.wait_clocks('mc_clk', rng.randint(1, 4))
            lv = tb.live()
            # No random MR may drive an out-of-range decode.
            chk(lv['wr'] in set(WR_TABLE.values()) | {0},
                f"soak produced wr_o={lv['wr']}, not a JEDEC value")
            chk(5 <= lv['cwl'] <= 12, f"soak produced cwl_o={lv['cwl']}")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, (f"{len(fails)} check(s) failed:\n  "
                       + "\n  ".join(fails))


_GATE = [("smoke_ddr3", 1), ("reset_values", 1), ("ddr3_wr_table", 1)]
_FUNC = _GATE + [("ddr3_cl_sweep", 1), ("ddr3_cwl_independent_of_cl", 1),
                 ("ddr3_wrlvl_en", 1), ("lpddr3_wr_is_zero", 1),
                 ("ddr3_al_tracks_cl", 1), ("random_soak", 1)]
_FULL = _FUNC + [("random_soak", 2), ("ddr3_cl_sweep", 2)]
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-nr{t[1]}" for t in _PARAMS])
def test_scoria_mode_register(request, test_type, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_mode_register"
    test_name = f"test_scoria_mode_register_{test_type}_nr{num_ranks}"

    filelist_path = ("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                     "rtl/filelists/fub/scoria_mode_register.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_RANKS": str(num_ranks),
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": _TEST_LEVEL,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": str(num_ranks)}

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_mode_register",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
