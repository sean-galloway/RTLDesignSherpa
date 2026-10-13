# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_amber_pair_harness_uart
# Purpose: Drive amber_pair_harness through the real uart_axil_bridge
#   (USE_DIRECT_HOST=0) with bit-banged 115200 8N1 UART. Reproduces the
#   Genesys2 read hang that only appears when the bridge is in the loop.

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

repo_root = os.path.dirname(
    os.path.dirname(
        os.path.dirname(
            os.path.dirname(
                os.path.dirname(
                    os.path.dirname(
                        os.path.dirname(
                            os.path.dirname(os.path.abspath(__file__)))))))))
sys.path.insert(0, repo_root)

from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import reg_level_grid, level_env
from TBClasses.shared.tbbase import TBBase


AMBER_FRAMEWORK_ROOT = os.path.join(
    repo_root, "projects", "fpga-systems", "Genesys2", "cache-ip", "amber")

# Bridge address map
ADDR_HARNESS_CSR = 0x0001_0000
ADDR_CYCLE_INJECTOR0 = 0x0002_0000
ADDR_CYCLE_INJECTOR1 = 0x0003_0000
ADDR_TALLY_CNT = 0x0004_0000

# Harness CSR word offsets
HCSR_CTRL = 0x00
HCSR_STATUS = 0x04
HCSR_CYCLE_LO = 0x08

# 90 MHz / 115200 baud = 781.25; amber_pair_harness truncates to integer.
# In simulation we approximate the 90 MHz period to a value representable
# with 1 ps simulator precision: 11.110 ns period / 5.555 ns half-period.
CLK_HZ = 90_000_000
BAUD = 115_200
CLKS_PER_BIT = CLK_HZ // BAUD  # 781
CLK_PERIOD_NS = 11.110
HALF_CLK_NS = 5.555


def _trace_signal(dut, name, value):
    dut._log.info(f"trace: {name}={value}")


class UARTDriver:
    """Bit-banged 8N1 UART driver for a single RX/TX pair."""

    def __init__(self, dut, clk, rx_pin, tx_pin):
        self.dut = dut
        self.clk = clk
        self.rx_pin = rx_pin
        self.tx_pin = tx_pin

    async def _wait_cycles(self, n):
        for _ in range(n):
            await cocotb.triggers.RisingEdge(self.clk)

    async def send_byte(self, b):
        """Transmit one byte on the DUT's RX pin (host -> FPGA)."""
        self.rx_pin.value = 0  # start bit
        await self._wait_cycles(CLKS_PER_BIT)
        for i in range(8):
            self.rx_pin.value = (b >> i) & 1
            await self._wait_cycles(CLKS_PER_BIT)
        self.rx_pin.value = 1  # stop bit
        await self._wait_cycles(CLKS_PER_BIT)

    async def send_str(self, s):
        for ch in s:
            await self.send_byte(ord(ch))

    async def recv_byte(self, timeout_bits=None):
        """Receive one byte from the DUT's TX pin (FPGA -> host)."""
        if timeout_bits is None:
            timeout_bits = CLKS_PER_BIT * 100
        # Wait for start bit (high -> low)
        waited = 0
        while int(self.tx_pin.value) == 1:
            await self._wait_cycles(1)
            waited += 1
            if waited > timeout_bits:
                raise TimeoutError("UART recv_byte: no start bit")
        # Sample in the middle of the start bit
        await self._wait_cycles(CLKS_PER_BIT // 2)
        if int(self.tx_pin.value) != 0:
            raise RuntimeError("UART recv_byte: start bit glitch")
        await self._wait_cycles(CLKS_PER_BIT)
        byte_val = 0
        for i in range(8):
            byte_val |= (int(self.tx_pin.value) << i)
            await self._wait_cycles(CLKS_PER_BIT)
        # Stop bit
        if int(self.tx_pin.value) != 1:
            raise RuntimeError("UART recv_byte: bad stop bit")
        await self._wait_cycles(CLKS_PER_BIT // 2)
        return byte_val

    async def recv_line(self, timeout_bits=None):
        chars = []
        while True:
            b = await self.recv_byte(timeout_bits=timeout_bits)
            c = chr(b)
            if c == '\n':
                break
            chars.append(c)
        return ''.join(chars)


class AmberPairHarnessUARTTest(TBBase):
    def __init__(self, dut, clock_task):
        super().__init__(dut)
        self.clock_task = clock_task
        self.uart = UARTDriver(dut, dut.aclk, dut.i_uart_rx, dut.o_uart_tx)

    async def reset(self):
        self.dut.i_uart_rx.value = 1
        self.dut.aresetn.value = 0
        for _ in range(12):
            await cocotb.triggers.RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await cocotb.triggers.RisingEdge(self.dut.aclk)
        self.dut._log.info("reset complete")

    async def cmd(self, s, timeout_bits=None):
        self.dut._log.info(f"uart tx: {s!r}")
        await self.uart.send_str(s + "\n")
        line = await self.uart.recv_line(timeout_bits=timeout_bits)
        self.dut._log.info(f"uart rx: {line!r}")
        return line

    async def write32(self, addr, data):
        resp = await self.cmd(f"W {addr:08x} {data:08x}")
        if resp != "OK":
            raise RuntimeError(f"write response mismatch: {resp!r}")

    async def read32(self, addr):
        resp = await self.cmd(f"R {addr:08x}")
        if not resp.startswith("0x"):
            raise RuntimeError(f"read response mismatch: {resp!r}")
        return int(resp[2:], 16)

    def log_r_channel(self, tag=""):
        dut = self.dut
        info = (
            f"RCH{tag}: "
            f"host32_rvalid={int(dut.probe_host_32b_rvalid.value)} "
            f"host32_rready={int(dut.probe_host_32b_rready.value)} "
            f"host32_rlast={int(dut.probe_host_32b_rlast.value)} "
            f"fub_rvalid={int(dut.probe_fub_axi_rvalid.value)} "
            f"fub_rready={int(dut.probe_fub_axi_rready.value)} "
            f"fub_rlast={int(dut.probe_fub_axi_rlast.value)} "
            f"conv_rvalid={int(dut.probe_converter_rvalid.value)} "
            f"conv_rlast={int(dut.probe_converter_rlast.value)} "
            f"slave_rvalid={int(dut.probe_slave_rvalid.value)} "
            f"slave_rready={int(dut.probe_slave_rready.value)}"
        )
        self.dut._log.info(info)


async def _manual_clock(dut):
    dut.aclk.value = 1
    while True:
        await cocotb.triggers.Timer(HALF_CLK_NS, unit='ns')
        dut.aclk.value = 0
        await cocotb.triggers.Timer(HALF_CLK_NS, unit='ns')
        dut.aclk.value = 1


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def uart_write_then_read_hang_probe(dut):
    """Reproduce the read hang via real UART bridge and trace R channel."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessUARTTest(dut, clk_task)
    await tb.reset()

    # First, prove a write works through the UART path.
    await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x0000_0000)

    # Read it back. This is where the board hangs.
    try:
        data = await tb.read32(ADDR_HARNESS_CSR + HCSR_CTRL)
        tb.log_r_channel(tag=" after read response")
    except TimeoutError as e:
        tb.log_r_channel(tag=" TIMEOUT")
        raise AssertionError(f"read hung: {e}") from e

    assert data == 0x0000_0000, f"readback mismatch: 0x{data:08x}"

    # Cycle counter should advance.
    cyc0 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
    for _ in range(10):
        await cocotb.triggers.RisingEdge(dut.aclk)
    cyc1 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
    assert cyc1 > cyc0, f"cycle counter did not advance: {cyc0} -> {cyc1}"

    # Probe reads from every aperture to exercise both 32b and 64b paths.
    for addr in [ADDR_CYCLE_INJECTOR0, ADDR_CYCLE_INJECTOR1, ADDR_TALLY_CNT]:
        await tb.read32(addr)


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def uart_read_only_stress_probe(dut):
    """Issue several reads back-to-back through the UART bridge."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessUARTTest(dut, clk_task)
    await tb.reset()

    for addr in [ADDR_HARNESS_CSR + HCSR_CTRL,
                 ADDR_HARNESS_CSR + HCSR_STATUS,
                 ADDR_HARNESS_CSR + HCSR_CYCLE_LO,
                 ADDR_CYCLE_INJECTOR0,
                 ADDR_CYCLE_INJECTOR1,
                 ADDR_TALLY_CNT]:
        await tb.read32(addr)


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

    run(
        python_search=[tests_dir, repo_root],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
        keep_files=True,
        compile_args=compile_args,
    )
