# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `ddr2_lpddr2_csr_slave`.

Mirrors stream's CSR test pattern: drives the APB port through a
hand-rolled write/read sequence (no BFM) and uses
DDR2LPDDR2RegisterMap for named offsets + field-pack helpers from
ddr2_lpddr2_csr_tb. obs_words readback lives in the F1f core_macro
integration test, since hwif_in struct ports can't be driven from
cocotb directly without a TB shim.
"""

import os
import random
import sys
import pytest

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.ddr2_lpddr2_csr_tb import (  # noqa: E402
    DDR2LPDDR2RegisterMap as R,
    apb_read, apb_write,
    encode_sched_tuning, encode_refresh_tuning,
)


async def _init_dut(dut) -> None:
    dut.s_apb_PSEL.value    = 0
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PADDR.value   = 0
    dut.s_apb_PWRITE.value  = 0
    dut.s_apb_PWDATA.value  = 0
    dut.s_apb_PSTRB.value   = 0
    dut.s_apb_PPROT.value   = 0

    # Default status + obs feeds = 0; individual tests override.
    dut.status_init_done_i.value        = 0
    dut.status_init_error_i.value       = 0
    dut.status_power_state_i.value      = 0
    dut.status_pasr_active_i.value      = 0
    dut.status_init_step_dbg_i.value    = 0
    dut.status_version_match_i.value    = 0
    dut.status_history_i.value          = 0
    dut.status_temp_class_rank0_i.value = 0
    dut.cap_lookahead_max_i.value       = 0
    dut.cap_synth_mask_i.value          = 0
    dut.obs_words_i.value               = 0
    dut.obs_row_hit_i.value             = 0
    dut.obs_ref_latency_i.value         = 0
    dut.obs_txn_queue_depth_max_i.value = 0
    dut.obs_txn_queue_depth_avg_i.value = 0
    dut.obs_refresh_pending_max_i.value = 0
    dut.obs_refresh_defer_hist_i.value  = 0
    dut.obs_page_pred_accuracy_i.value  = 0
    dut.obs_axi_r_latency_avg_i.value   = 0
    dut.obs_axi_r_latency_p99_i.value   = 0
    dut.obs_axi_w_latency_avg_i.value   = 0

    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())
    cocotb.start_soon(Clock(dut.mc_clk, 7, units="ns").start())
    dut.presetn.value  = 0
    dut.mc_rst_n.value = 0
    await Timer(80, units="ns")
    dut.presetn.value  = 1
    dut.mc_rst_n.value = 1
    await Timer(120, units="ns")


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_ddr2_lpddr2_csr_slave(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    await _init_dut(dut)
    pclk = dut.pclk

    if test_type == "smoke":
        # ID has hard-coded RO reset values: module_id=0xD2, n_phases=2,
        # memtype=0, version=1.
        rd, err = await apb_read(dut, pclk, R.ID)
        expected = (0xD2 << 24) | (0x02 << 16) | (0x00 << 8) | 0x01
        assert err == 0, "PSLVERR set on ID read"
        assert rd == expected, (
            f"{R.name(R.ID)} readback 0x{rd:08X} != 0x{expected:08X}"
        )

    elif test_type == "ctrl_rw":
        # pwr_req_low_power persists (no swmod). init_start / soft_reset
        # are swmod self-clearing — skip those for the persistence check.
        await apb_write(dut, pclk, R.CTRL, 1 << 4)
        rd, err = await apb_read(dut, pclk, R.CTRL)
        assert err == 0
        assert (rd & (1 << 4)) != 0, (
            f"{R.name(R.CTRL)}.pwr_req_low_power not retained: 0x{rd:08X}"
        )

    elif test_type == "timings_rw":
        # Write all four fields packed
        val = (0x40 << 0) | (0x10 << 8) | (0x10 << 16) | (0x2A << 24)
        await apb_write(dut, pclk, R.TIMINGS_RC_RCD_RP_RAS, val)
        rd, err = await apb_read(dut, pclk, R.TIMINGS_RC_RCD_RP_RAS)
        assert err == 0
        assert rd == val, (
            f"{R.name(R.TIMINGS_RC_RCD_RP_RAS)} readback 0x{rd:08X} != 0x{val:08X}"
        )

    elif test_type == "sched_tuning_rw":
        val = encode_sched_tuning(
            lookahead=5, force_inorder=True, happy_enable=True,
            age_max_runtime=0xAA, txn_queue_high_water=0x12,
        )
        await apb_write(dut, pclk, R.SCHED_TUNING, val)
        rd, err = await apb_read(dut, pclk, R.SCHED_TUNING)
        assert err == 0
        # Bits we wrote (mask out the RO lookahead_max_obs window)
        wmask = 0x00FF_FFFF
        assert (rd & wmask) == (val & wmask), (
            f"SCHED_TUNING expect 0x{val & wmask:08X} got 0x{rd & wmask:08X}"
        )

    elif test_type == "refresh_tuning_rw":
        val = encode_refresh_tuning(
            refpb_policy_or=2, page_policy_or=3,
            refresh_defer_active=4, zqcs_freq_hz=1234,
        )
        await apb_write(dut, pclk, R.REFRESH_TUNING, val)
        rd, err = await apb_read(dut, pclk, R.REFRESH_TUNING)
        assert err == 0
        # All fields in REFRESH_TUNING are writable; no RO mask needed.
        assert rd == val, (
            f"{R.name(R.REFRESH_TUNING)} expect 0x{val:08X} got 0x{rd:08X}"
        )

    elif test_type == "mr_rw":
        # Mode registers: low 16 bits writable
        for addr in (R.MR0, R.MR1, R.MR2, R.MR3):
            val = random.randint(0, 0xFFFF)
            await apb_write(dut, pclk, addr, val)
            rd, err = await apb_read(dut, pclk, addr)
            assert err == 0
            assert (rd & 0xFFFF) == val, (
                f"{R.name(addr)} write/read mismatch 0x{rd:08X} vs 0x{val:04X}"
            )

    elif test_type == "status_readback":
        # Drive the status feeds with a recognizable pattern and verify
        # APB reads come back through the regblock.
        dut.status_init_done_i.value     = 1
        dut.status_init_error_i.value    = 0
        dut.status_power_state_i.value   = 0xA           # bits 7:4
        dut.status_pasr_active_i.value   = 1             # bit 8
        dut.status_init_step_dbg_i.value = 0x42          # bits 23:16
        dut.status_version_match_i.value = 1             # bit 31
        # Wait one mc_clk so the regblock samples the .next inputs.
        await Timer(50, units="ns")
        rd, err = await apb_read(dut, pclk, R.STATUS)
        assert err == 0
        expected = (
            (1 << 0)            # init_done
            | (0xA << 4)        # power_state
            | (1 << 8)          # pasr_active
            | (0x42 << 16)      # init_step_dbg
            | (1 << 31)         # version_match
        )
        assert rd == expected, (
            f"STATUS readback 0x{rd:08X} != expected 0x{expected:08X}"
        )

    elif test_type == "status_history_readback":
        pattern = 0xDEADBEEF
        dut.status_history_i.value = pattern
        await Timer(50, units="ns")
        rd, err = await apb_read(dut, pclk, R.STATUS_HISTORY)
        assert err == 0
        assert rd == pattern, f"STATUS_HISTORY: 0x{rd:08X} != 0x{pattern:08X}"

    elif test_type == "obs_words_readback":
        # Inject 9 distinct patterns into the obs_words array and read
        # each back through OBS_WORDS[i] @ 0x1C0 + i*4.
        patterns = [(0xC0DE_0000 | (i << 8) | (i * 0x11)) & 0xFFFFFFFF
                    for i in range(9)]
        # Pack the patterns into the flat array signal (LSB = idx 0).
        packed = 0
        for i, val in enumerate(patterns):
            packed |= (val & 0xFFFFFFFF) << (i * 32)
        dut.obs_words_i.value = packed
        await Timer(50, units="ns")
        for i, val in enumerate(patterns):
            rd, err = await apb_read(dut, pclk, R.obs_word(i))
            assert err == 0
            assert rd == val, (
                f"OBS_WORDS[{i}] @ 0x{R.obs_word(i):03X}: "
                f"0x{rd:08X} != injected 0x{val:08X}"
            )

    elif test_type == "obs_per_bank_readback":
        # 8 distinct row-hit counters, one per bank.
        patterns = [0x10000 + i * 0x1111 for i in range(8)]
        packed = 0
        for i, val in enumerate(patterns):
            packed |= (val & 0xFFFFFFFF) << (i * 32)
        dut.obs_row_hit_i.value = packed
        await Timer(50, units="ns")
        for bank, val in enumerate(patterns):
            rd, err = await apb_read(dut, pclk, R.obs_row_hit(bank))
            assert err == 0
            # OBS_ROW_HIT has onread=rclr, so the very next read returns 0.
            assert rd == val, (
                f"OBS_ROW_HIT[{bank}]: 0x{rd:08X} != injected 0x{val:08X}"
            )

    elif test_type == "obs_system_readback":
        # System obs registers — drive each, read back.
        dut.obs_txn_queue_depth_max_i.value = 0xAA00_0001
        dut.obs_txn_queue_depth_avg_i.value = 0xAA00_0002
        dut.obs_refresh_pending_max_i.value = 0xAA00_0003
        dut.obs_page_pred_accuracy_i.value  = 0xAA00_0004
        dut.obs_axi_r_latency_avg_i.value   = 0xAA00_0005
        dut.obs_axi_r_latency_p99_i.value   = 0xAA00_0006
        dut.obs_axi_w_latency_avg_i.value   = 0xAA00_0007
        await Timer(50, units="ns")
        for offset, expected in (
            (R.OBS_TXN_QUEUE_DEPTH_MAX, 0xAA00_0001),
            (R.OBS_TXN_QUEUE_DEPTH_AVG, 0xAA00_0002),
            (R.OBS_REFRESH_PENDING_MAX, 0xAA00_0003),
            (R.OBS_PAGE_PRED_ACCURACY,  0xAA00_0004),
            (R.OBS_AXI_R_LATENCY_AVG,   0xAA00_0005),
            (R.OBS_AXI_R_LATENCY_P99,   0xAA00_0006),
            (R.OBS_AXI_W_LATENCY_AVG,   0xAA00_0007),
        ):
            rd, err = await apb_read(dut, pclk, offset)
            assert err == 0
            assert rd == expected, (
                f"{R.name(offset)}: 0x{rd:08X} != 0x{expected:08X}"
            )

    elif test_type == "ctrl_cfg_drive":
        # Verify that an APB write to CTRL drives the flat cfg_*_o
        # outputs that core_macro will consume.
        await apb_write(dut, pclk, R.CTRL, 1 << 4)
        # cfg path is combinational from hwif_out.value → output. Sample.
        await Timer(20, units="ns")
        assert int(dut.cfg_pwr_req_low_power_o.value) == 1, (
            f"cfg_pwr_req_low_power_o not set: "
            f"{int(dut.cfg_pwr_req_low_power_o.value)}"
        )

    elif test_type == "hole_read_returns_zero":
        # PeakRDL --cpuif passthrough does not raise rd_err on unmapped
        # holes; it just returns 0. Verify the slave still completes the
        # transaction cleanly (no hang) and returns zero data.
        rd, _ = await apb_read(dut, pclk, 0x0F0)
        assert rd == 0, f"unmapped hole 0x0F0 returned 0x{rd:08X}, expected 0"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await Timer(100, units="ns")


_GATE = [("smoke",), ("ctrl_rw",), ("ctrl_cfg_drive",)]
_FUNC = _GATE + [("timings_rw",), ("sched_tuning_rw",),
                 ("refresh_tuning_rw",), ("mr_rw",),
                 ("status_readback",), ("status_history_readback",),
                 ("obs_words_readback",), ("obs_per_bank_readback",),
                 ("obs_system_readback",), ("hole_read_returns_zero",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_ddr2_lpddr2_csr_slave(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_lpddr2_csr_slave"
    test_name = f"test_ddr2_lpddr2_csr_slave_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/macro/ddr2_lpddr2_csr_slave.f")
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
    # PeakRDL-generated SV emits per-field always_comb that Verilator flags
    # as MULTIDRIVEN. Other suppressions match stream's CSR test.
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN",
        "-Wno-UNUSED",
        "-Wno-UNDRIVEN",
        "-Wno-UNUSEDSIGNAL",
        "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE",
        "-Wno-SELRANGE",
        "-Wno-DECLFILENAME",
    ]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    from cocotb_test.simulator import run
    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_ddr2_lpddr2_csr_slave",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
