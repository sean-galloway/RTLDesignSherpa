# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""End-to-end tests for ddr2_lpddr2_top.

Workload-mix tests use AXI4Sequence to drive the canonical 60/40 W:R
mix with 128B/256B/512B/1024B at 20/20/40/20. Configure the controller
through APB (RegisterMap), then issue traffic through the AXI4 slave.

DFI loopback is a stub today — reads return garbage, but writes
exercise the full AXI → CAM → scheduler → DFI path.
"""

import logging
import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.ddr2_lpddr2_top_tb import DDR2LPDDR2TopTB  # noqa: E402

from CocoTBFramework.components.axi4.axi4_sequence import AXI4Sequence  # noqa: E402


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_ddr2_lpddr2_top(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    seed = int(os.environ.get("SEED", "12345"))

    tb = DDR2LPDDR2TopTB(dut)
    await tb.reset()
    tb.init_register_map()
    tb.init_apb_master()
    await tb.apb_master.reset_bus()

    if test_type == "smoke":
        # Read the ID register (fixed RO values).
        rd = await tb.apb_read_register(0xFF0)
        expected = (0xD2 << 24) | (0x02 << 16) | (0x00 << 8) | 0x01
        assert rd == expected, f"ID readback 0x{rd:08X} != 0x{expected:08X}"

        # Wait for init_done to come up through the DFI stub.
        await tb.wait_for_init_done()

    elif test_type == "configure_via_apb":
        # Program a couple of timing registers via RegisterMap + APB, then
        # verify they read back.
        await tb.apb_program_register("REFRESH_TUNING", "page_policy_or", 0x2)
        await tb.apb_program_register("SCHED_TUNING", "force_inorder", 0x1)
        rt = await tb.apb_read_register(0x048)  # REFRESH_TUNING
        st = await tb.apb_read_register(0x040)  # SCHED_TUNING
        assert ((rt >> 2) & 0x3) == 0x2, f"page_policy_or not set: 0x{rt:08X}"
        assert ((st >> 4) & 0x1) == 0x1, f"force_inorder not set: 0x{st:08X}"

    elif test_type == "axi_write_smoke":
        # Init AXI masters and drive a single short write to make sure the
        # AXI → CAM → scheduler path doesn't hang. Read will not return
        # valid data yet (DFI stub) but the write completion should fire.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("smoke_wr", data_width=64, seed=seed)
        seq.add_write(0x0000_1000, [0xDEAD_BEEF_DEAD_0000], axid=0)
        results = await tb.run_sequence(seq)
        assert len(results) == 1
        # We accept either success or a timeout-style error here — the goal is
        # that the run_sequence call returns without hanging the harness.
        tb.log.info("smoke wr result: %s", results[0])

    elif test_type == "workload_mix":
        # The canonical 60/40 + 128/256/512/1024 distribution. Modest count
        # so the test finishes in reasonable time; iterate up after the
        # DFI loopback lands.
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("workload_mix", data_width=64, seed=seed)
        seq.add_random_workload(
            count=8,
            addr_range=(0x0, 0x4000),
            write_ratio=0.6,
            size_weights={128: 0.2, 256: 0.2, 512: 0.4, 1024: 0.2},
            qos_choices=[0, 4, 8, 15],
        )
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("workload_mix: %d / %d bursts completed without error",
                    n_done, len(results))

    elif test_type == "row_hit_pattern":
        tb.init_axi_masters()
        await tb.axi_master_wr.aw_channel.reset_bus()
        await tb.axi_master_wr.w_channel.reset_bus()
        await tb.axi_master_rd.ar_channel.reset_bus()
        await tb.axi_master_rd.r_channel.reset_bus()
        await tb.wait_for_init_done()

        seq = AXI4Sequence("row_hit", data_width=64, seed=seed)
        seq.add_row_hit_burst(
            base_addr=0x0000_1000, n_followups=3,
            burst_bytes=64, is_write=True, qos=8,
        )
        results = await tb.run_sequence(seq)
        n_done = sum(1 for r in results if r["error"] is None)
        tb.log.info("row_hit: %d / %d bursts completed", n_done, len(results))

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


_GATE = [("smoke",)]
_FUNC = _GATE + [("configure_via_apb",), ("axi_write_smoke",),
                 ("workload_mix",), ("row_hit_pattern",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_ddr2_lpddr2_top(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_lpddr2_top"
    test_name = f"test_ddr2_lpddr2_top_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/top/ddr2_lpddr2_top.f")
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
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP",
    ]
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
        testcase="cocotb_test_ddr2_lpddr2_top",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
