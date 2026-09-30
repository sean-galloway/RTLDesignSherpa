# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_dfi_cmd_formatter` -- the DDR3 command truth table.

The encodings in this module were originally checked BY INSPECTION against
JESD79-3F Table 6 and reported as twelve matches with zero mismatches. That
method has already failed once today in a way worth remembering: the mode
register's CL encoder and its decoder shared the same mistake, so reading one
against the other agreed perfectly and CL 12 was unreachable.

So the table below is transcribed from Table 6 (pages 33-34 of JESD79-3F,
"Command Truth Table"), independently of the RTL, and the test drives commands
and reads the actual DFI pin buses back.

Table 6, the RAS#/CAS#/WE# and A10 columns:

    MRS   L L L    A10 = OP code        REF   L L H    A10 = V
    PRE   L H L    A10 = L              PREA  L H L    A10 = H
    ACT   L H H    A10 = row address
    WR    H L L    A10 = L              WRA   H L L    A10 = H
    RD    H L H    A10 = L              RDA   H L H    A10 = H
    ZQCL  H H L    A10 = H              ZQCS  H H L    A10 = L
    NOP   H H H    A10 = V

A10 is the AP (auto-precharge) column for column commands and the
all-banks/long-calibration selector otherwise -- which is why PRE/PREA and
ZQCL/ZQCS differ ONLY in that bit. Getting it inverted swaps a single-bank
precharge for an all-bank one, and a short calibration for a long one.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

# dram_op_e, scoria_pkg.
OP = {"NOP": 0x0, "ACT": 0x1, "RD": 0x2, "RDA": 0x3, "WR": 0x4, "WRA": 0x5,
      "PRE": 0x6, "PREA": 0x7, "REF": 0x8, "REFPB": 0x9, "MRS": 0xA,
      "ZQCS": 0xB, "ZQCL": 0xC}

L, H, V = 0, 1, None          # V = don't care, not asserted on

#: TRANSCRIBED FROM JESD79-3F TABLE 6. Do not derive these from the RTL.
#: (ras_n, cas_n, we_n, a10)
TRUTH = {
    "MRS":  (L, L, L, V),
    "REF":  (L, L, H, V),
    "PRE":  (L, H, L, L),
    "PREA": (L, H, L, H),
    "ACT":  (L, H, H, V),
    "WR":   (H, L, L, L),
    "WRA":  (H, L, L, H),
    "RD":   (H, L, H, L),
    "RDA":  (H, L, H, H),
    "ZQCL": (H, H, L, H),
    "ZQCS": (H, H, L, L),
    "NOP":  (H, H, H, V),
}

MEMTYPE_DDR3 = 0
DFI_RATE = int(os.environ.get("DFI_RATE_P", "4"))
ADDR_W = 14


class FmtTB(TBBase):
    async def setup(self):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.memtype_i.value = MEMTYPE_DDR3
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value = OP["NOP"]
        d.cmd_rank_i.value = 0
        d.cmd_bank_i.value = 0
        d.cmd_row_i.value = 0
        d.cmd_col_i.value = 0
        d.cmd_len_i.value = 8
        d.rd_phase_i.value = 0
        d.wr_phase_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 3)

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def issue(self, op, *, bank=0, row=0, col=0, rank=0, limit=40):
        """Drive one command and return the phase that carries it.

        The formatter packs DFI_RATE phases per word; a command lands on the
        phase selected by rd_phase_i/wr_phase_i, and every other phase must
        read as NOP. Returning the decoded phase lets the caller assert on the
        command AND on the quiet phases.
        """
        d = self.dut
        d.cmd_op_i.value = op
        d.cmd_bank_i.value = bank
        d.cmd_row_i.value = row
        d.cmd_col_i.value = col
        d.cmd_rank_i.value = rank
        d.cmd_valid_i.value = 1
        for _ in range(limit):
            await RisingEdge(d.mc_clk)
            if int(d.cmd_ready_o.value):
                break
        d.cmd_valid_i.value = 0
        await RisingEdge(d.mc_clk)
        return self.phases()

    def phases(self):
        d = self.dut
        ras = int(d.dfi_ras_n_o.value)
        cas = int(d.dfi_cas_n_o.value)
        we = int(d.dfi_we_n_o.value)
        addr = int(d.dfi_address_o.value)
        bank = int(d.dfi_bank_o.value)
        out = []
        for p in range(DFI_RATE):
            out.append({
                'ras_n': (ras >> p) & 1,
                'cas_n': (cas >> p) & 1,
                'we_n':  (we >> p) & 1,
                'addr':  (addr >> (p * ADDR_W)) & ((1 << ADDR_W) - 1),
                'bank':  (bank >> (p * 3)) & 0x7,
            })
        return out

    @staticmethod
    def active(phs):
        """Phases that are NOT a NOP (ras/cas/we all high)."""
        return [p for p in phs
                if not (p['ras_n'] and p['cas_n'] and p['we_n'])]


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_scoria_dfi_cmd_formatter(dut):
    tt = os.environ.get("TEST_TYPE", "truth_table")
    tb = FmtTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "truth_table":
        # Every command, against the spec transcription.
        await tb.setup()
        for name, (ras, cas, we, a10) in TRUTH.items():
            if name == "NOP":
                continue                       # covered by quiet_phases
            phs = await tb.issue(OP[name], bank=5, row=0x1234, col=0x155)
            act = tb.active(phs)
            chk(len(act) == 1,
                f"{name}: {len(act)} active phases, expected exactly 1")
            if not act:
                continue
            p = act[0]
            chk(p['ras_n'] == ras,
                f"{name}: RAS# {p['ras_n']} != {ras} (JESD79-3F Table 6)")
            chk(p['cas_n'] == cas,
                f"{name}: CAS# {p['cas_n']} != {cas} (JESD79-3F Table 6)")
            chk(p['we_n'] == we,
                f"{name}: WE# {p['we_n']} != {we} (JESD79-3F Table 6)")
            if a10 is not None:
                got = (p['addr'] >> 10) & 1
                chk(got == a10,
                    f"{name}: A10 {got} != {a10} -- that bit is the only thing "
                    f"separating PRE/PREA and ZQCS/ZQCL")

    elif tt == "a10_separates_the_pairs":
        # The pairs that differ ONLY in A10. An inverted bit turns a
        # single-bank precharge into an all-bank one and a short calibration
        # into a long one, with everything else looking correct.
        await tb.setup()
        for lo, hi in (("PRE", "PREA"), ("ZQCS", "ZQCL"),
                       ("RD", "RDA"), ("WR", "WRA")):
            a = tb.active(await tb.issue(OP[lo], bank=3, col=0x155))
            b = tb.active(await tb.issue(OP[hi], bank=3, col=0x155))
            chk(a and b, f"{lo}/{hi}: no active phase")
            if not (a and b):
                continue
            chk((a[0]['addr'] >> 10) & 1 == 0, f"{lo}: A10 should be 0")
            chk((b[0]['addr'] >> 10) & 1 == 1, f"{hi}: A10 should be 1")
            chk((a[0]['ras_n'], a[0]['cas_n'], a[0]['we_n'])
                == (b[0]['ras_n'], b[0]['cas_n'], b[0]['we_n']),
                f"{lo}/{hi} differ in RAS/CAS/WE -- Table 6 says they differ "
                f"ONLY in A10")

    elif tt == "quiet_phases":
        # A command occupies ONE phase; every other phase must be a NOP.
        # A command leaking onto a second phase issues it twice to the DRAM.
        await tb.setup()
        for name in ("ACT", "RD", "WR", "PRE", "REF", "ZQCS", "MRS"):
            phs = await tb.issue(OP[name], bank=2, row=0x55, col=0x0AA)
            chk(len(tb.active(phs)) == 1,
                f"{name}: {len(tb.active(phs))} active phases of {DFI_RATE}, "
                f"expected 1 -- a leak issues the command more than once")

    elif tt == "act_carries_row":
        await tb.setup()
        for row in (0x0000, 0x1555, 0x2AAA, 0x3FFF):
            phs = await tb.issue(OP["ACT"], bank=6, row=row)
            act = tb.active(phs)
            chk(act, "ACT: no active phase")
            if act:
                chk(act[0]['addr'] == (row & ((1 << ADDR_W) - 1)),
                    f"ACT row 0x{row:04X}: addr 0x{act[0]['addr']:04X}")
                chk(act[0]['bank'] == 6,
                    f"ACT bank {act[0]['bank']} != 6")

    elif tt == "mrs_carries_index_and_data":
        # MRS puts the MR INDEX on the bank field and the data on the address.
        await tb.setup()
        for idx in range(4):
            data = 0x0123 + idx
            phs = await tb.issue(OP["MRS"], bank=idx, row=data)
            act = tb.active(phs)
            chk(act, f"MRS{idx}: no active phase")
            if act:
                chk(act[0]['bank'] == idx,
                    f"MRS: bank(index) {act[0]['bank']} != {idx}")
                chk(act[0]['addr'] == (data & ((1 << ADDR_W) - 1)),
                    f"MRS{idx}: addr 0x{act[0]['addr']:04X} != 0x{data:04X}")

    elif tt == "zq_pair_full_encoding":
        # ZQ is new in scoria -- DDR2 has no ZQ command, so this encoding has
        # never been exercised anywhere in the repo.
        await tb.setup()
        for name in ("ZQCS", "ZQCL"):
            ras, cas, we, a10 = TRUTH[name]
            act = tb.active(await tb.issue(OP[name]))
            chk(len(act) == 1, f"{name}: expected one active phase")
            if act:
                p = act[0]
                chk((p['ras_n'], p['cas_n'], p['we_n']) == (ras, cas, we),
                    f"{name}: RAS/CAS/WE {(p['ras_n'], p['cas_n'], p['we_n'])} "
                    f"!= {(ras, cas, we)}")
                chk((p['addr'] >> 10) & 1 == a10,
                    f"{name}: A10 != {a10}")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '3')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 40, "FUNC": 150, "FULL": 500}.get(lvl, 150)
        await tb.setup()
        names = [k for k in TRUTH if k != "NOP"]
        for _ in range(n):
            name = rng.choice(names)
            ras, cas, we, a10 = TRUTH[name]
            act = tb.active(await tb.issue(
                OP[name], bank=rng.randrange(8),
                row=rng.randrange(1 << 14), col=rng.randrange(1 << 10)))
            chk(len(act) == 1, f"{name}: {len(act)} active phases")
            if act:
                p = act[0]
                chk((p['ras_n'], p['cas_n'], p['we_n']) == (ras, cas, we),
                    f"{name} under soak: RAS/CAS/WE wrong")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["truth_table", "a10_separates_the_pairs", "quiet_phases"]
_FUNC = _GATE + ["act_carries_row", "mrs_carries_index_and_data",
                 "zq_pair_full_encoding", "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_dfi_cmd_formatter(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_dfi_cmd_formatter"
    test_name = f"test_scoria_dfi_cmd_formatter_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_dfi_cmd_formatter.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_dfi_cmd_formatter",
        sim_build=sim_build, simulator="verilator",
        parameters={"DFI_RATE": "4", "DFI_ADDR_WIDTH": "14"},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "DFI_RATE_P": "4",
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
