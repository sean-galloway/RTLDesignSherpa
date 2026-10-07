# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_regfile
# Purpose: Functional tests for the kestrel-rv32i register file.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Created: 2026-10-06

"""Register-file unit tests for kestrel-rv32i."""

import os
import random

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_kestrel_regfile(dut):
    """Verify reset, write/read, read-during-write, and x0 discard."""
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.rs1_addr.value = 0
    dut.rs2_addr.value = 0
    dut.rd_addr.value = 0
    dut.rd_data.value = 0
    dut.rd_wen.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)

    # Helper coroutines
    async def read_ports(rs1=None, rs2=None):
        """Drive optional read addresses and sample both read ports."""
        if rs1 is not None:
            dut.rs1_addr.value = rs1
        if rs2 is not None:
            dut.rs2_addr.value = rs2
        await Timer(1, units="ns")
        return int(dut.rs1_data.value), int(dut.rs2_data.value)

    async def write_reg(addr, data):
        dut.rd_addr.value = addr
        dut.rd_data.value = data
        dut.rd_wen.value = 1
        await RisingEdge(dut.clk)
        dut.rd_wen.value = 0

    # 1) Reset leaves every register at 0.
    for addr in range(32):
        rs1, rs2 = await read_ports(addr, addr)
        assert rs1 == 0, f"reset: x{addr} rs1_data != 0 ({rs1})"
        assert rs2 == 0, f"reset: x{addr} rs2_data != 0 ({rs2})"

    # 2) Write-then-read same address next cycle.
    seed = int(os.environ.get("SEED", "0"))
    random.seed(seed)
    dut._log.info(f"kestrel_regfile test with seed {seed}")

    written = {addr: 0 for addr in range(32)}
    test_addrs = random.sample(range(1, 32), 10)
    for addr in test_addrs:
        data = random.randint(0, 0xFFFFFFFF)
        await write_reg(addr, data)
        written[addr] = data

    for addr in test_addrs:
        rs1, rs2 = await read_ports(addr, addr)
        assert rs1 == written[addr], f"write-read: x{addr} rs1_data mismatch"
        assert rs2 == written[addr], f"write-read: x{addr} rs2_data mismatch"

    # 3) Read-during-write returns the OLD value on the same cycle.
    old_value = 0xAABBCCDD
    new_value = 0x11223344
    target = test_addrs[0]
    await write_reg(target, old_value)
    written[target] = old_value

    dut.rd_addr.value = target
    dut.rd_data.value = new_value
    dut.rd_wen.value = 1
    rs1, rs2 = await read_ports(target, target)
    assert rs1 == old_value, "read-during-write rs1 old value"
    assert rs2 == old_value, "read-during-write rs2 old value"

    await RisingEdge(dut.clk)
    dut.rd_wen.value = 0
    written[target] = new_value

    rs1, rs2 = await read_ports(target, target)
    assert rs1 == new_value, "read-during-write rs1 new value after clock"
    assert rs2 == new_value, "read-during-write rs2 new value after clock"

    # 4) Writes to x0 are discarded.
    await write_reg(0, 0xDEADBEEF)
    rs1, rs2 = await read_ports(0, 0)
    assert rs1 == 0, "x0 write discarded rs1"
    assert rs2 == 0, "x0 write discarded rs2"

    dut._log.info("kestrel_regfile test PASSED")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_regfile {lvl}") for lvl in reg_level_grid()])
def test_kestrel_regfile(request, test_level, description):
    """Pytest wrapper for the kestrel register-file cocotb test."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    dut_name = "kestrel_regfile"
    test_name_plus_params = f"test_kestrel_regfile_{test_level}"

    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/rtl/filelists/kestrel_all.f",
    )

    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-CASEINCOMPLETE",
        "-Wno-BLKANDNBLK", "-Wno-MULTIDRIVEN", "-Wno-TIMESCALEMOD",
        "-Wno-MODDUP", "-Wno-GENUNNAMED", "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-SYNCASYNCNET",
        "-Wno-DECLFILENAME", "-Wno-VARHIDDEN",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_kestrel_regfile",
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
