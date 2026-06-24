"""
Unit test for page_predictor FUB.

Verifies the per-(rank, bank) 2-bit saturating predictor:
  * First ACT on a bank → no update (just records)
  * Same-row ACT → counter saturates up
  * Different-row ACT → counter saturates down
  * predict_open_o tracks counter[1] (the MSB)
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

from tbclasses.trackers import PagePredictorTracker  # noqa: E402


class PredTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_RANKS = int(os.environ.get('NUM_RANKS', '1'))
        self.NUM_BANKS = int(os.environ.get('NUM_BANKS', '8'))

    async def setup(self):
        self.dut.evt_act_i.value  = 0
        self.dut.evt_rank_i.value = 0
        self.dut.evt_bank_i.value = 0
        self.dut.evt_row_i.value  = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def pulse_act(self, rank=0, bank=0, row=0):
        self.dut.evt_rank_i.value = rank
        self.dut.evt_bank_i.value = bank
        self.dut.evt_row_i.value  = row
        self.dut.evt_act_i.value  = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.evt_act_i.value = 0

    def predict_open(self, rank=0, bank=0) -> int:
        bit_index = rank * self.NUM_BANKS + bank
        return (int(self.dut.predict_open_o.value) >> bit_index) & 0x1


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_page_predictor(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = PredTB(dut)
    # Tracker auto-dumps <sim_build>/pgpred.out at end of sim.
    pgpred_tracker = PagePredictorTracker(
        dut, num_ranks=tb.NUM_RANKS, num_banks=tb.NUM_BANKS,
    )
    cocotb.start_soon(pgpred_tracker.run())

    if test_type == "smoke":
        # Default: predictor starts at counter=0 (predict_open = 0).
        await tb.setup()
        assert tb.predict_open(0, 0) == 0

    elif test_type == "row_hit_saturates_up":
        await tb.setup()
        # First ACT on row 5 → no update (counter stays 0)
        await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.wait_clocks('mc_clk', 2)
        # Outputs are registered → +1 cycle of lag
        assert tb.predict_open(0, 0) == 0, "after first ACT"
        # Now several ACTs on the same row → counter saturates up
        for _ in range(4):
            await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.predict_open(0, 0) == 1, "after 4 hits counter MSB=1"

    elif test_type == "row_miss_saturates_down":
        await tb.setup()
        # Bootstrap counter to "open" by hitting twice
        await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.pulse_act(rank=0, bank=0, row=5)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.predict_open(0, 0) == 1
        # Now several misses → counter saturates down
        for i in range(4):
            await tb.pulse_act(rank=0, bank=0, row=10 + i)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.predict_open(0, 0) == 0, "after 4 misses MSB=0"

    elif test_type == "independent_banks":
        # Bank 0 hits, bank 1 misses — they should track independently.
        await tb.setup()
        for _ in range(4):
            await tb.pulse_act(rank=0, bank=0, row=5)
        # bank 1: alternate rows
        for r in range(4):
            await tb.pulse_act(rank=0, bank=1, row=r * 10)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.predict_open(0, 0) == 1, "bank 0 should be open"
        assert tb.predict_open(0, 1) == 0, "bank 1 should be closed"

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 50, "FUNC": 300, "FULL": 1500}.get(test_level, 300)
        await tb.setup()

        for _ in range(n):
            rank = rng.randrange(tb.NUM_RANKS)
            bank = rng.randrange(tb.NUM_BANKS)
            if rng.random() < 0.5:
                row = 0x10 + bank
            else:
                row = rng.randrange(1 << 14)
            await tb.pulse_act(rank=rank, bank=bank, row=row)
            await tb.wait_clocks('mc_clk', rng.randint(0, 3))

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",)]
_FUNC = _GATE + [("row_hit_saturates_up",),
                 ("row_miss_saturates_down",),
                 ("independent_banks",),
                 ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_page_predictor(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "page_predictor"
    test_name = f"test_page_predictor_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/page_predictor.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_RANKS":  "1",
        "NUM_BANKS":  "8",
        "ROW_WIDTH":  "14",
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "NUM_RANKS":  "1",
        "NUM_BANKS":  "8",
        "ROW_WIDTH":  "14",
    }

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
        testcase="cocotb_test_page_predictor",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
