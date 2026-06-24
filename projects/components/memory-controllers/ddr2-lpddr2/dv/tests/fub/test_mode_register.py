# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `mode_register`. Verifies MR storage + live
decode of CL/CWL/BL/AL.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)


MEMTYPE_DDR2   = 0
MEMTYPE_LPDDR2 = 1


def _encode_ddr2_mr0(cl: int, bl: int) -> int:
    """Encode CL into [6:4], BL into [2:0] of MR0."""
    bl_code = 0b010 if bl == 4 else 0b011
    return ((cl & 0x7) << 4) | (bl_code & 0x7)


def _encode_ddr2_mr1(al: int, dll_en: int = 0, ods: int = 0,
                      rtt_lo: int = 0, rtt_hi: int = 0) -> int:
    """Encode AL into [5:3] of MR1."""
    return (((al & 0x7) << 3)
            | ((rtt_hi & 1) << 6)
            | ((rtt_lo & 1) << 2)
            | ((ods & 1) << 1)
            | (dll_en & 1))


class MrTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_RANKS  = int(os.environ.get('NUM_RANKS', '1'))
        self.MAX_MR_IDX = int(os.environ.get('MAX_MR_IDX', '17'))
        self.RKW = max(1, (self.NUM_RANKS - 1).bit_length()) \
                   if self.NUM_RANKS > 1 else 1

    async def setup(self, memtype: int = MEMTYPE_DDR2):
        self.dut.memtype_i.value   = memtype
        self.dut.mr_we_i.value     = 0
        self.dut.mr_index_i.value  = 0
        self.dut.mr_data_i.value   = 0
        self.dut.mr_rank_i.value   = 0
        self.dut.mr_grant_i.value  = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def write_mr(self, rank: int, idx: int, data: int):
        self.dut.mr_we_i.value    = 1
        self.dut.mr_index_i.value = idx
        self.dut.mr_data_i.value  = data & 0xFFFF
        self.dut.mr_rank_i.value  = rank
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.mr_we_i.value = 0

    def read_live(self):
        return {
            'cl':   int(self.dut.cl_o.value),
            'cwl':  int(self.dut.cwl_o.value),
            'bl':   int(self.dut.bl_o.value),
            'al':   int(self.dut.al_o.value),
            'drv':  int(self.dut.drv_strength_o.value),
            'odt':  int(self.dut.odt_o.value),
        }


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_mode_register(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_ddr2")
    tb = MrTB(dut)

    if test_type == "smoke_ddr2":
        await tb.setup(MEMTYPE_DDR2)
        await tb.write_mr(0, 0, _encode_ddr2_mr0(cl=5, bl=4))
        await tb.write_mr(0, 1, _encode_ddr2_mr1(al=2))
        await tb.wait_clocks('mc_clk', 2)
        live = tb.read_live()
        assert live['cl']  == 5, f"CL got {live['cl']}"
        assert live['cwl'] == 4, f"CWL got {live['cwl']}"
        assert live['bl']  == 4, f"BL got {live['bl']}"
        assert live['al']  == 2, f"AL got {live['al']}"

    elif test_type == "ddr2_cl_sweep":
        await tb.setup(MEMTYPE_DDR2)
        for cl in range(3, 8):
            await tb.write_mr(0, 0, _encode_ddr2_mr0(cl=cl, bl=4))
            await tb.wait_clocks('mc_clk', 1)
            live = tb.read_live()
            assert live['cl']  == cl, f"CL={cl}: got {live['cl']}"
            assert live['cwl'] == cl - 1

    elif test_type == "ddr2_bl_sweep":
        await tb.setup(MEMTYPE_DDR2)
        for bl in [4, 8]:
            await tb.write_mr(0, 0, _encode_ddr2_mr0(cl=4, bl=bl))
            await tb.wait_clocks('mc_clk', 1)
            assert tb.read_live()['bl'] == bl, \
                f"BL={bl}: got {tb.read_live()['bl']}"

    elif test_type == "ddr2_al_sweep":
        await tb.setup(MEMTYPE_DDR2)
        for al in range(0, 7):
            await tb.write_mr(0, 1, _encode_ddr2_mr1(al=al))
            await tb.wait_clocks('mc_clk', 1)
            assert tb.read_live()['al'] == al, \
                f"AL={al}: got {tb.read_live()['al']}"

    elif test_type == "multi_rank":
        await tb.setup(MEMTYPE_DDR2)
        # Write different MR0 to rank 0 and rank 1
        await tb.write_mr(0, 0, _encode_ddr2_mr0(cl=5, bl=4))
        await tb.write_mr(1, 0, _encode_ddr2_mr0(cl=6, bl=8))
        await tb.wait_clocks('mc_clk', 2)
        # Live outputs decode from rank 0
        live = tb.read_live()
        assert live['cl'] == 5, f"rank0 CL got {live['cl']}"

    elif test_type == "reset_values":
        await tb.setup(MEMTYPE_DDR2)
        live = tb.read_live()
        # MR0 = 0 → CL = 0; BL decode default = 4
        assert live['cl'] == 0
        assert live['bl'] == 4

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 50, "FUNC": 200, "FULL": 1000}.get(test_level, 200)
        await tb.setup(MEMTYPE_DDR2)

        for _ in range(n):
            rank = rng.randint(0, tb.NUM_RANKS - 1)
            idx  = rng.randint(0, 3)
            data = rng.randrange(0x10000)
            await tb.write_mr(rank, idx, data)
            await tb.wait_clocks('mc_clk', rng.randint(1, 4))

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke_ddr2", 1), ("ddr2_cl_sweep", 1), ("reset_values", 1)]
_FUNC = _GATE + [("ddr2_bl_sweep", 1), ("ddr2_al_sweep", 1), ("multi_rank", 2),
                 ("random_soak", 1)]
_FULL = _FUNC + [("ddr2_cl_sweep", 2), ("random_soak", 2)]
# Dedupe — defensive; keeps every (type, rank) tuple unique so pytest IDs
# stay distinct and parallel workers don't race on local_sim_build/.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-nr{t[1]}" for t in _PARAMS])
def test_mode_register(request, test_type, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mode_register"
    test_name = f"test_mode_register_{test_type}_nr{num_ranks}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/mode_register.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_RANKS": str(num_ranks),
        "MAX_MR_IDX": "17",
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": str(num_ranks), "MAX_MR_IDX": "17"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_mode_register",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
