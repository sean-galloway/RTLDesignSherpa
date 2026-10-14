# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_amber_pair_harness_uart
# Purpose: Drive amber_pair_harness through the real UART bridge (USE_DIRECT_HOST=0)
#   using the shared CocotbUartChannel + UARTAxiBridge stack. The SAME host
#   program/sequences that run on the board are imported and executed here,
#   so this is the sim/silicon equivalence path.

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb._bridge import bridge
from cocotb.triggers import RisingEdge, Timer

repo_root = os.path.dirname(
    os.path.dirname(
        os.path.dirname(
            os.path.dirname(
                os.path.dirname(
                    os.path.dirname(
                        os.path.dirname(
                            os.path.dirname(os.path.abspath(__file__)))))))))
sys.path.insert(0, repo_root)

AMBER_FRAMEWORK_ROOT = os.path.join(
    repo_root, "projects", "fpga-systems", "Genesys2", "cache-ip", "amber")

# Area layers must be importable in both the cocotb process and the worker.
sys.path.insert(0, os.path.join(AMBER_FRAMEWORK_ROOT, "bin"))
sys.path.insert(0, os.path.join(AMBER_FRAMEWORK_ROOT, "host"))

import amber_env  # noqa: F401  (path setup)

from TBClasses.shared.utilities import (get_repo_root, get_paths, create_view_cmd,
                                       sim_build_path)
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import reg_level_grid, level_env
from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
from run_smoke import run_campaign
from uart_axi_bridge import UARTAxiBridge

# Bridge address map
ADDR_HARNESS_CSR = 0x0001_0000
ADDR_CYCLE_INJECTOR0 = 0x0002_0000
ADDR_CYCLE_INJECTOR1 = 0x0003_0000
ADDR_TALLY_CNT = 0x0004_0000

# Run the UART fast in simulation so the smoke campaign finishes in ms.
CLK_HZ = 90_000_000
UART_BAUD = 12_500_000
CLKS_PER_BIT = CLK_HZ // UART_BAUD  # 7

CLK_PERIOD_NS = 11.110
HALF_CLK_NS = 5.555


def _build_bridge(dut):
    """Build a UARTAxiBridge over the one shared CocotbUartChannel."""
    channel = make_uart_channel(dut, dut.aclk, CLKS_PER_BIT,
                                rx_signal="i_uart_rx", tx_signal="o_uart_tx")
    return UARTAxiBridge(channel=channel)


async def _manual_clock(dut):
    dut.aclk.value = 1
    while True:
        await Timer(HALF_CLK_NS, unit='ns')
        dut.aclk.value = 0
        await Timer(HALF_CLK_NS, unit='ns')
        dut.aclk.value = 1


async def _reset(dut):
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    for _ in range(12):
        await cocotb.triggers.RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await cocotb.triggers.RisingEdge(dut.aclk)


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def uart_bridge_probe(dut):
    """Smoke the shared UART bridge path: W/R harness CSR and all apertures."""
    cocotb.start_soon(_manual_clock(dut))
    await _reset(dut)

    br = _build_bridge(dut)

    def probe():
        br.write(ADDR_HARNESS_CSR, 0x0000_0000)
        ctrl = br.read(ADDR_HARNESS_CSR)

        cyc0 = br.read(ADDR_HARNESS_CSR + 0x08)
        # Burn a few read transactions so time advances.
        _ = br.read(ADDR_CYCLE_INJECTOR0)
        _ = br.read(ADDR_CYCLE_INJECTOR1)
        _ = br.read(ADDR_TALLY_CNT)
        cyc1 = br.read(ADDR_HARNESS_CSR + 0x08)

        for addr in [ADDR_CYCLE_INJECTOR0, ADDR_CYCLE_INJECTOR1, ADDR_TALLY_CNT]:
            br.read(addr)

        return ctrl, cyc0, cyc1

    ctrl, cyc0, cyc1 = await bridge(probe)()

    assert ctrl == 0x0000_0000, f"CTRL readback mismatch: 0x{ctrl:08x}"
    assert cyc1 > cyc0, f"cycle counter did not advance: {cyc0} -> {cyc1}"

    br.close()


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def uart_smoke_via_host(dut):
    """Run the board's smoke campaign through the real UART bridge."""
    cocotb.start_soon(_manual_clock(dut))
    await _reset(dut)

    br = _build_bridge(dut)
    count = int(os.environ.get('AMBER_SMOKE_COUNT', '200'))

    def campaign():
        return run_campaign(
            br,
            sequences=["init", "smoke"],
            params={
                "count": count,
                "we_mix": 64,
                # In sim the worker must not wall-clock sleep; polling is fine.
                "sleep_fn": lambda _poll: None,
            },
        )

    report = await bridge(campaign)()
    assert report.ok, report.summary()

    br.close()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_pair_harness_uart(request, test_level):
    module = "test_amber_pair_harness_uart"
    dut_name = "amber_pair_harness_uart_tb"
    toplevel = dut_name

    log_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests", "log")
    tests_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests")
    test_name = f"{module}_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    os.environ['AMBER_FRAMEWORK_ROOT'] = AMBER_FRAMEWORK_ROOT

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/fpga-systems/Genesys2/cache-ip/amber/dv/filelists/amber_pair_harness_uart_tb.f'
    )

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '600000',
        'AMBER_FRAMEWORK_ROOT': AMBER_FRAMEWORK_ROOT,
        **level_env(test_level),
    }

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    compile_args = [
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]

    area_bin = os.path.join(AMBER_FRAMEWORK_ROOT, "bin")
    area_host = os.path.join(AMBER_FRAMEWORK_ROOT, "host")

    run(
        python_search=[tests_dir, repo_root, area_bin, area_host],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        extra_env=extra_env,
        parameters={"UART_BAUD": UART_BAUD},
        waves=True,
        # Verilator compiles trace support in via waves=True but the dump is
        # only written when the sim binary gets the runtime switch; the
        # runner forwards plus_args to the binary argv (sim_args is ignored).
        plus_args=(["--trace", "--trace-file",
                    os.path.join(sim_build, "dump.fst")] +
                   (["+verilator+rand+reset+2"]
                    if os.environ.get("AMBER_RAND_RESET") else [])),
        keep_files=True,
        compile_args=compile_args,
    )
