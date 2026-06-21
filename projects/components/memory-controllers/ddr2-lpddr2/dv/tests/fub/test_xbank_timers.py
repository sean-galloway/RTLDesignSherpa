# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `xbank_timers`. Verifies per-(rank,bank)
state machine + countdown timers (tRCD, tWR/tRTP, tRP) and the
combinational ready vectors derived from them.
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


# bank_state_e (from ddr2_lpddr2_pkg.sv)
BANK_IDLE        = 0
BANK_ACTIVATING  = 1
BANK_ACTIVE      = 2
BANK_RD_BUSY     = 3
BANK_WR_BUSY     = 4
BANK_PRECHARGING = 5
BANK_REFRESHING  = 6


class XbTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_RANKS = int(os.environ.get('NUM_RANKS', '1'))
        self.NUM_BANKS = int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = int(os.environ.get('ROW_WIDTH', '14'))

    async def setup(self, t_rcd=4, t_rp=4, t_wr=3, t_rtp=2):
        self.dut.t_rcd_i.value    = t_rcd
        self.dut.t_rp_i.value     = t_rp
        self.dut.t_ras_i.value    = 8
        self.dut.t_rc_i.value     = 12
        self.dut.t_wr_i.value     = t_wr
        self.dut.t_wtr_i.value    = 2
        self.dut.t_rtp_i.value    = t_rtp
        self.dut.evt_act_i.value  = 0
        self.dut.evt_rd_i.value   = 0
        self.dut.evt_wr_i.value   = 0
        self.dut.evt_pre_i.value  = 0
        self.dut.evt_ap_i.value   = 0
        self.dut.evt_rank_i.value = 0
        self.dut.evt_bank_i.value = 0
        self.dut.evt_row_i.value  = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def pulse_event(self, kind: str, rank=0, bank=0, row=0, ap=False):
        sig = {'act': self.dut.evt_act_i,
               'rd':  self.dut.evt_rd_i,
               'wr':  self.dut.evt_wr_i,
               'pre': self.dut.evt_pre_i}[kind]
        self.dut.evt_rank_i.value = rank
        self.dut.evt_bank_i.value = bank
        self.dut.evt_row_i.value  = row
        self.dut.evt_ap_i.value   = 1 if ap else 0
        sig.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        sig.value = 0
        self.dut.evt_ap_i.value = 0

    def _vec(self, sig, rank, bank) -> int:
        full = int(sig.value)
        return (full >> (rank * self.NUM_BANKS + bank)) & 1

    def act_ready(self, r=0, b=0)  -> bool: return bool(self._vec(self.dut.bank_act_ready_o, r, b))
    def rdwr_ready(self, r=0, b=0) -> bool: return bool(self._vec(self.dut.bank_rdwr_ready_o, r, b))
    def pre_ready(self, r=0, b=0)  -> bool: return bool(self._vec(self.dut.bank_pre_ready_o, r, b))
    def row_active(self, r=0, b=0) -> bool: return bool(self._vec(self.dut.bank_row_active_o, r, b))

    def state(self, r=0, b=0) -> int:
        # bank_state_o is a packed 3D array: [RANK][BANK][3 bits]
        full = int(self.dut.bank_state_o.value)
        bit_offset = (r * self.NUM_BANKS + b) * 3
        return (full >> bit_offset) & 0x7

    def open_row(self, r=0, b=0) -> int:
        full = int(self.dut.bank_open_row_o.value)
        bit_offset = (r * self.NUM_BANKS + b) * self.ROW_WIDTH
        mask = (1 << self.ROW_WIDTH) - 1
        return (full >> bit_offset) & mask


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_xbank_timers(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = XbTB(dut)

    if test_type == "smoke":
        await tb.setup(t_rcd=4, t_rp=4, t_wr=3, t_rtp=2)
        # Initial: bank 0 idle, act_ready=1
        assert tb.state(0, 0) == BANK_IDLE
        assert tb.act_ready(0, 0)
        assert not tb.rdwr_ready(0, 0)
        # ACT bank 0
        await tb.pulse_event('act', bank=0, row=0x123)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.state(0, 0) == BANK_ACTIVATING
        assert tb.open_row(0, 0) == 0x123
        assert not tb.act_ready(0, 0)
        assert not tb.rdwr_ready(0, 0)
        # Wait tRCD = 4 cycles → ACTIVATING → ACTIVE
        await tb.wait_clocks('mc_clk', 4)
        assert tb.state(0, 0) == BANK_ACTIVE
        assert tb.rdwr_ready(0, 0)

    elif test_type == "act_to_wr_to_pre":
        # Output bank_state is registered (+1 cycle vs the FSM state).
        # Wait one extra cycle at each transition-observation point.
        await tb.setup(t_rcd=3, t_rp=3, t_wr=2, t_rtp=2)
        await tb.pulse_event('act', bank=2, row=0x456)
        await tb.wait_clocks('mc_clk', 4)
        assert tb.state(0, 2) == BANK_ACTIVE
        await tb.pulse_event('wr', bank=2)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.state(0, 2) == BANK_WR_BUSY
        await tb.wait_clocks('mc_clk', 2)
        assert tb.state(0, 2) == BANK_ACTIVE
        await tb.pulse_event('pre', bank=2)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.state(0, 2) == BANK_PRECHARGING
        await tb.wait_clocks('mc_clk', 3)
        assert tb.state(0, 2) == BANK_IDLE

    elif test_type == "independent_banks":
        await tb.setup()
        # ACT bank 0 and bank 5 in different cycles; each one independent
        await tb.pulse_event('act', bank=0, row=0x100)
        await tb.pulse_event('act', bank=5, row=0x200)
        await tb.wait_clocks('mc_clk', 5)
        assert tb.state(0, 0) == BANK_ACTIVE
        assert tb.state(0, 5) == BANK_ACTIVE
        assert tb.open_row(0, 0) == 0x100
        assert tb.open_row(0, 5) == 0x200
        # bank 3 untouched
        assert tb.state(0, 3) == BANK_IDLE
        assert tb.act_ready(0, 3)

    elif test_type == "rd_path":
        await tb.setup(t_rcd=3, t_rtp=2)
        await tb.pulse_event('act', bank=1, row=0x300)
        await tb.wait_clocks('mc_clk', 3)
        await tb.pulse_event('rd', bank=1)
        await tb.wait_clocks('mc_clk', 1)
        assert tb.state(0, 1) == BANK_RD_BUSY
        assert not tb.rdwr_ready(0, 1)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.state(0, 1) == BANK_ACTIVE

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke", 1, 8)]
_FUNC = _GATE + [("act_to_wr_to_pre", 1, 8),
                 ("independent_banks", 1, 8),
                 ("rd_path", 1, 8)]
_FULL = _FUNC + [(t, 2, 8) for t, _, _ in _FUNC]
# Dedupe — otherwise pytest disambiguates colliding IDs with _0/_1 suffixes
# and parallel workers race on the same local_sim_build/ directory.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,num_ranks,num_banks", _PARAMS,
                         ids=[f"{t[0]}-nr{t[1]}-nb{t[2]}" for t in _PARAMS])
def test_xbank_timers(request, test_type, num_ranks, num_banks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "xbank_timers"
    test_name = f"test_xbank_timers_{test_type}_nr{num_ranks}_nb{num_banks}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/xbank_timers.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_RANKS": str(num_ranks),
        "NUM_BANKS": str(num_banks),
        "ROW_WIDTH": "14",
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {"NUM_RANKS": str(num_ranks),
                  "NUM_BANKS": str(num_banks),
                  "ROW_WIDTH": "14"}

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_xbank_timers",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
