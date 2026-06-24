# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `init_sequencer`. Walks the FSM from RESET
through DONE, verifies dfi_init_start_o asserts, verifies the MR
write sequence (MR2 → MR3 → MR1 → MR0), and checks ZQCL handshake.
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

from tbclasses.trackers import InitSequencerTracker  # noqa: E402


MEMTYPE_DDR2   = 0
MEMTYPE_LPDDR2 = 1

# Default MR values per init_sequencer
DDR2_MR0_DEFAULT = 0x0152
DDR2_MR1_DEFAULT = 0x0000
DDR2_MR2_DEFAULT = 0x0000
DDR2_MR3_DEFAULT = 0x0000


class InitTB(TBBase):
    CLK = 10

    async def setup(self, memtype: int = MEMTYPE_DDR2):
        self.dut.memtype_i.value             = memtype
        self.dut.dfi_init_complete_i.value   = 0
        self.dut.zqcl_grant_i.value          = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def init_start(self) -> int:
        return int(self.dut.dfi_init_start_o.value)

    def init_busy(self) -> int:
        return int(self.dut.init_busy_o.value)

    def init_done(self) -> int:
        return int(self.dut.init_done_o.value)

    def mr_we(self) -> int:
        return int(self.dut.mr_seq_we_o.value)

    def mr_idx(self) -> int:
        return int(self.dut.mr_seq_index_o.value)

    def mr_data(self) -> int:
        return int(self.dut.mr_seq_data_o.value)

    def zqcl_req(self) -> int:
        return int(self.dut.zqcl_req_o.value)

    async def capture_mr_seq(self, max_cycles: int = 20):
        """Watch for MR write strobes; return list of (index, data) seen."""
        seen = []
        for _ in range(max_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, units='ps')
            if self.mr_we():
                seen.append((self.mr_idx(), self.mr_data()))
        return seen


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_init_sequencer(dut):
    test_type = os.environ.get("TEST_TYPE", "ddr2_init_walk")
    tb = InitTB(dut)
    # Tracker auto-dumps <sim_build>/init.out at end of sim.
    init_tracker = InitSequencerTracker(dut)
    cocotb.start_soon(init_tracker.run())

    if test_type == "ddr2_init_walk":
        await tb.setup(MEMTYPE_DDR2)
        # After reset deassertion, dfi_init_start_o should be high.
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        assert tb.init_busy() == 1
        assert tb.init_done() == 0
        # PHY completes init
        tb.dut.dfi_init_complete_i.value = 1
        # Capture MR sequence
        seen = await tb.capture_mr_seq(max_cycles=10)
        # Should see MR2, MR3, MR1, MR0 in order
        seq = [(idx, data) for idx, data in seen]
        expected = [
            (2, DDR2_MR2_DEFAULT),
            (3, DDR2_MR3_DEFAULT),
            (1, DDR2_MR1_DEFAULT),
            (0, DDR2_MR0_DEFAULT),
        ]
        assert seq == expected, f"MR seq mismatch: got {seq}, want {expected}"
        # ZQCL request follows
        await tb.wait_clocks('mc_clk', 1)
        assert tb.zqcl_req() == 1
        # Grant; advance to DONE
        tb.dut.zqcl_grant_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        tb.dut.zqcl_grant_i.value = 0
        await tb.wait_clocks('mc_clk', 2)
        assert tb.init_done() == 1
        assert tb.init_busy() == 0

    elif test_type == "wait_for_complete":
        await tb.setup(MEMTYPE_DDR2)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        # Don't assert dfi_init_complete; init should stay busy
        await tb.wait_clocks('mc_clk', 30)
        assert tb.init_busy() == 1
        assert tb.init_done() == 0

    elif test_type == "lpddr2_smoke":
        await tb.setup(MEMTYPE_LPDDR2)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.init_start() == 1
        tb.dut.dfi_init_complete_i.value = 1
        # LPDDR2 v2 defaults — see init_sequencer.sv LPDDR2_MR{1,2,3}_DEFAULT.
        # MR0 is read-only in LPDDR2, so the sequencer writes 0 there.
        expected_lpddr2 = {
            0: 0x0000,
            1: 0x0082,   # BL4, nWR=3
            2: 0x0004,   # RL3/WL1
            3: 0x0001,   # DS=34Ω
        }
        seen = await tb.capture_mr_seq(max_cycles=10)
        for idx, data in seen:
            assert data == expected_lpddr2.get(idx, 0), (
                f"LPDDR2 MR{idx} got {data:#x} want {expected_lpddr2.get(idx, 0):#x}"
            )
        tb.dut.zqcl_grant_i.value = 1
        await tb.wait_clocks('mc_clk', 5)
        assert tb.init_done() == 1

    elif test_type == "random_soak":
        # Soak the init flow by repeatedly pulsing reset and walking the
        # init sequence with random PHY-complete / ZQCL-grant delays.
        # Clock is started only once (via the initial setup); subsequent
        # iterations toggle mc_rst_n manually rather than calling setup()
        # again (which would spawn duplicate clock coroutines).
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 8, "FUNC": 40, "FULL": 200}.get(test_level, 40)

        await tb.setup(MEMTYPE_DDR2)   # starts clock + initial reset
        for _ in range(n):
            memtype = rng.choice([MEMTYPE_DDR2, MEMTYPE_LPDDR2])
            tb.dut.memtype_i.value           = memtype
            tb.dut.dfi_init_complete_i.value = 0
            tb.dut.zqcl_grant_i.value        = 0
            # Pulse reset to restart the init FSM.
            tb.dut.mc_rst_n.value = 0
            await tb.wait_clocks('mc_clk', 3)
            tb.dut.mc_rst_n.value = 1
            await tb.wait_clocks('mc_clk', rng.randint(2, 6))
            # Variable PHY-complete delay
            tb.dut.dfi_init_complete_i.value = 1
            # FSM walks S_DFI_INIT → MR2 → MR3 → MR1 → MR0 → S_ZQCL,
            # which is 5 cycles minimum. Give it ≥6 to be safe; add
            # randomness on top.
            await tb.wait_clocks('mc_clk', 6 + rng.randint(0, 6))
            # Variable ZQCL-grant delay
            tb.dut.zqcl_grant_i.value = 1
            await tb.wait_clocks('mc_clk', 4 + rng.randint(0, 4))
            assert tb.init_done() == 1, f"init not done with memtype={memtype}"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("ddr2_init_walk",)]
_FUNC = _GATE + [("wait_for_complete",), ("lpddr2_smoke",), ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_init_sequencer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "init_sequencer"
    test_name = f"test_init_sequencer_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/init_sequencer.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
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
        testcase="cocotb_test_init_sequencer",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
