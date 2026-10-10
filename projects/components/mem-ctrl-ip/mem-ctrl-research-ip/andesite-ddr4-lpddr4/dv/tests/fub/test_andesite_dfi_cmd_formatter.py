# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_dfi_cmd_formatter` -- the DDR4 truth table at the pins.

Every anchored command from MAS Table 2.3 (via the generated kmap table) is
driven and the DFI 4.0 pins are checked: ACT_n/RAS_n/CAS_n/WE_n encodings, the
activate's BG+row packing, A10 as the address-input variant select (PREA/ZQCL/
RDA/WRA share pins with PRE/ZQCL/RD/WR -- AP is an input, not a pin), and the
parity qualifier. LPDDR4 behavior is P1-out-of-scope: only the DDR4-idle
posture is checked for a non-DDR4 memtype.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_dfi_cmd_formatter_tb import (  # noqa: E402
    AndesiteDfiCmdFormatterTB, OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA,
    OP_PRE, OP_PREA, OP_REF, OP_MRS, OP_ZQCS, OP_ZQCL,
)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_andesite_dfi_cmd_formatter(dut):
    tb = AndesiteDfiCmdFormatterTB(dut)
    await tb.setup_clock()
    await tb.reset()

    # Anchored encodings: (op, bank, bg, row, col) -> (cs, act, ras, cas, we, bank, bg, address)
    # Expected values: docs/kmaps/generated/01_ddr4_command_table.md (MAS Table 2.3).
    cases = [
        # NOP: 1111, quiescent address/bank
        (OP_NOP, 1, 2, 0x1234, 0x55, (0, 1, 1, 1, 1, 1, 2, 0x55)),
        # ACT: 0 1 1 1, row on address, bg on dfi_bg
        (OP_ACT, 1, 2, 0x155, 0x0, (0, 0, 1, 1, 1, 1, 2, 0x155)),
        # RD: 1 1 0 1, col on address
        (OP_RD, 3, 1, 0x0, 0x2AA, (0, 1, 1, 0, 1, 3, 1, 0x2AA)),
        # WR: 1 1 0 0
        (OP_WR, 3, 1, 0x0, 0x2AA, (0, 1, 1, 0, 0, 3, 1, 0x2AA)),
        # RDA == RD pins, A10 set -- AP is an address input, not a pin
        (OP_RDA, 3, 1, 0x0, 0x401, (0, 1, 1, 0, 1, 3, 1, 0x401)),
        # MRS: 0 0 0 0; MR index in bank_i, data in col_i -> address
        (OP_MRS, 3, 0, 0x0, 0x14, (0, 0, 0, 0, 0, 3, 0, 0x14)),
        # REF: 0 0 0 1
        (OP_REF, 0, 0, 0x0, 0x0, (0, 0, 0, 0, 1, 0, 0, 0x0)),
        # PRE: 1 0 1 0; PREA same pins, col[10]=1
        (OP_PRE, 2, 0, 0x0, 0x0, (0, 1, 0, 1, 0, 2, 0, 0x0)),
        (OP_PREA, 2, 0, 0x0, 0x400, (0, 1, 0, 1, 0, 2, 0, 0x400)),
        # ZQ: 1 1 1 0; ZQCL with A10=1
        (OP_ZQCS, 0, 0, 0x0, 0x0, (0, 1, 1, 1, 0, 0, 0, 0x0)),
        (OP_ZQCL, 0, 0, 0x0, 0x400, (0, 1, 1, 1, 0, 0, 0, 0x400)),
    ]
    for op, bank, bg, row, col, exp in cases:
        got = await tb.issue(op, bank=bank, bg=bg, row=row, col=col)
        assert got == exp, \
            f"op {op:#x}: pins {got} != expected {exp}"

    # Parity qualification: disabled -> constant 0; enabled -> an address bit
    # flip changes the parity bit (functional; no fabricated polynomial).
    dut.parity_en_i.value = 0
    await tb.issue(OP_ACT, bank=1, bg=0, row=0x100, col=0)
    assert int(dut.dfi_parity_in.value) == 0, "parity must be 0 when disabled"
    dut.parity_en_i.value = 1
    await tb.issue(OP_ACT, bank=1, bg=0, row=0x100, col=0)
    p0 = int(dut.dfi_parity_in.value)
    await tb.issue(OP_ACT, bank=1, bg=0, row=0x101, col=0)
    p1 = int(dut.dfi_parity_in.value)
    assert p0 != p1, "parity must change when one address bit flips"

    # Non-DDR4 memtype: DDR4 pins held at the idle posture (LPDDR4 breadth is
    # a follow-on; the check pins P1's no-half-built-branches rule).
    dut.memtype_i.value = 0x6      # MEMTYPE_LPDDR4
    got = await tb.issue(OP_ACT, bank=1, bg=1, row=0x55, col=0)
    assert got[0:5] == (1, 1, 1, 1, 1), \
        f"non-DDR4 memtype must idle the DDR4 pins, got {got[0:5]}"


@pytest.mark.parametrize("seed", [None])
def test_andesite_dfi_cmd_formatter(seed):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_dfi_cmd_formatter"
    test_name = "test_andesite_dfi_cmd_formatter"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_dfi_cmd_formatter.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_dfi_cmd_formatter",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
