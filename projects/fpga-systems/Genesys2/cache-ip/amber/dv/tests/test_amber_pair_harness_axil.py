# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_amber_pair_harness_axil
# Purpose: Drive amber_pair_harness's direct AXIL4-Lite host interface with the
#   house AXIL4 master BFM, bypassing the UART bridge. This is the FAST low-level
#   path for exercising the DUT; it is NOT the UART equivalence evidence. The
#   equivalence evidence is test_amber_pair_harness_uart, which imports and runs
#   the same host sequences through the real uart_axil_bridge.

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
from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)


AMBER_FRAMEWORK_ROOT = os.path.join(
    repo_root, "projects", "fpga-systems", "Genesys2", "cache-ip", "amber")

# Bridge address map (matches bridge_amber_axil.toml)
ADDR_HARNESS_CSR = 0x0001_0000
ADDR_CYCLE_INJECTOR0 = 0x0002_0000
ADDR_CYCLE_INJECTOR1 = 0x0003_0000
ADDR_TALLY_CNT = 0x0004_0000
ADDR_TALLY_CFGW = 0x0005_0000
ADDR_TALLY_CFGR = 0x0006_0000

# Cycle-injector CSR word offsets (32-bit)
CI_CTRL = 0x00
CI_SEED = 0x04
CI_ADDR_BASE = 0x08
CI_ADDR_MASK = 0x0C
CI_TRANS_COUNT = 0x10
CI_STATUS = 0x14
CI_ACC_COUNT = 0x18
CI_RSP_COUNT = 0x1C
CI_ERR_FLAG = 0x20
CI_RSP_CRC_LO = 0x30
CI_RSP_CRC_HI = 0x34
CI_WDATA_CRC_LO = 0x38
CI_WDATA_CRC_HI = 0x3C

# Harness CSR word offsets
HCSR_CTRL = 0x00
HCSR_STATUS = 0x04
HCSR_CYCLE_LO = 0x08
HCSR_CYCLE_HI = 0x0C
HCSR_FABRIC_DBG = 0x10

# Tally config register offsets (64-bit stride)
TALLY_CAM_CLEAR = 0x100
TALLY_CAM_KEY = 0x108
TALLY_CAM_LOAD = 0x110


def _key(agent: int, protocol: int, pkt_type: int, event: int) -> int:
    return ((agent & 0xFFFF) << 16) | ((protocol & 0xF) << 12) | \
           ((pkt_type & 0xF) << 8) | (event & 0xFF)


def _default_profile():
    # Wire-truth keys (BUG-004 board capture): all amber monlites emit agent
    # 0x00A0; control events are CORE/PktTypePerf with l1_pkg codes 0x00-0x09;
    # the AXI rd/wr monlites share PktTypeCompletion code 0 and merge into one
    # CAM bin because unit_id is not part of the tally key.
    a = 0x00A0
    return [
        (_key(a, 4, 4, 0x00), 0),  # hit
        (_key(a, 4, 4, 0x01), 1),  # miss
        (_key(a, 4, 4, 0x02), 2),  # snoop accepted
        (_key(a, 4, 4, 0x03), 3),  # evict
        (_key(a, 4, 4, 0x04), 5),  # tag state transition
        (_key(a, 0, 0, 0x0E), 4),  # AXI monlite drop report (health bin)
        (_key(a, 4, 4, 0x05), 6),  # fill start
        (_key(a, 4, 4, 0x06), 7),  # fill end
        (_key(a, 4, 4, 0x07), 8),  # drain start
        (_key(a, 4, 4, 0x08), 9),  # drain end
        (_key(a, 4, 0, 0x09), 10),  # control monlite drop report
    ]


class AmberPairHarnessAXILTest(TBBase):
    def __init__(self, dut, clock_task):
        super().__init__(dut)
        self.clock_task = clock_task
        self.axil = create_axil4_master(
            dut,
            clock=dut.aclk,
            prefix='host_axi_',
            data_width=32,
            addr_width=32,
            multi_sig=True,
            timeout_cycles=5000,
            log=self.log,
        )

    async def reset(self):
        self.dut.aresetn.value = 0
        for _ in range(12):
            await cocotb.triggers.RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await cocotb.triggers.RisingEdge(self.dut.aclk)

        # Sanity check: sample clock at opposite phases to confirm toggling.
        await cocotb.triggers.FallingEdge(self.dut.aclk)
        s0 = int(self.dut.aclk.value)
        await cocotb.triggers.RisingEdge(self.dut.aclk)
        s1 = int(self.dut.aclk.value)
        self.log.info(f"reset complete: aclk sampled {s0} -> {s1}")

    async def write32(self, addr: int, data: int):
        return await self.axil['write'].single_write(addr, data)

    async def read32(self, addr: int):
        return await self.axil['read'].single_read(addr)

    async def write64(self, addr: int, data: int):
        await self.write32(addr, data & 0xFFFF_FFFF)
        await self.write32(addr + 4, (data >> 32) & 0xFFFF_FFFF)

    async def read64(self, addr: int):
        lo = await self.read32(addr)
        hi = await self.read32(addr + 4)
        return (hi << 32) | lo


async def _manual_clock(dut):
    dut.aclk.value = 1
    while True:
        await cocotb.triggers.Timer(5, unit='ns')
        dut.aclk.value = 0
        await cocotb.triggers.Timer(5, unit='ns')
        dut.aclk.value = 1


@cocotb.test(timeout_time=1000, timeout_unit="ms")
async def aperture_probe_test(dut):
    """Write then read every slave aperture to reproduce the bring-up hang."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    failures = []

    # harness_csr: write CTRL then read it back
    try:
        await tb.write32(ADDR_HARNESS_CSR + HCSR_CTRL, 0x0000_0000)
        ctrl = await tb.read32(ADDR_HARNESS_CSR + HCSR_CTRL)
        if ctrl != 0x0000_0000:
            failures.append(f"harness_csr CTRL readback mismatch: 0x{ctrl:08x}")
    except Exception as e:
        failures.append(f"harness_csr access failed: {e}")

    # harness_csr cycle counter should advance
    try:
        cyc0 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
        for _ in range(10):
            await cocotb.triggers.RisingEdge(dut.aclk)
        cyc1 = await tb.read32(ADDR_HARNESS_CSR + HCSR_CYCLE_LO)
        if cyc1 <= cyc0:
            failures.append(f"cycle counter did not advance: {cyc0} -> {cyc1}")
    except Exception as e:
        failures.append(f"harness_csr cycle counter read failed: {e}")

    # cycle_injector0: write/read a config register
    try:
        await tb.write32(ADDR_CYCLE_INJECTOR0 + CI_SEED, 0x1234_5678)
        seed = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_SEED)
        if seed != 0x1234_5678:
            failures.append(f"cycle_injector0 SEED readback mismatch: 0x{seed:08x}")
    except Exception as e:
        failures.append(f"cycle_injector0 access failed: {e}")

    # cycle_injector1: write/read a config register
    try:
        await tb.write32(ADDR_CYCLE_INJECTOR1 + CI_SEED, 0xDEAD_BEEF)
        seed = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_SEED)
        if seed != 0xDEAD_BEEF:
            failures.append(f"cycle_injector1 SEED readback mismatch: 0x{seed:08x}")
    except Exception as e:
        failures.append(f"cycle_injector1 access failed: {e}")

    # tally_cfgw: write the CAM clear/key/load aperture (32-bit registers;
    # single 32-bit writes only -- see smoke_test's BUG-003 comment).
    # We verify the write completes (no hang); the exact readback of CAM_KEY
    # depends on the generated regblock update timing and is covered by the
    # smoke sequence that checks tally bins.
    try:
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_KEY, _default_profile()[0][0])
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, (1 << 31) | 0)
    except Exception as e:
        failures.append(f"tally_cfgw/cfgr access failed: {e}")

    # tally_cnt: read only, should not hang
    try:
        await tb.read64(ADDR_TALLY_CNT)
    except Exception as e:
        failures.append(f"tally_cnt read failed: {e}")

    assert not failures, "; ".join(failures)


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def smoke_test(dut):
    """Run the amber_board.py smoke sequence in simulation."""
    clk_task = cocotb.start_soon(_manual_clock(dut))
    tb = AmberPairHarnessAXILTest(dut, clk_task)
    await tb.reset()

    # Configure tally legal-set profile. The CAM registers are 32-bit and
    # MUST be written with single 32-bit accesses: a 64-bit decomposition
    # (write64) writes the high word at +4, which aliases onto the same
    # register in the 64-bit cfgw port wrapper (it ignores WSTRB and takes
    # wdata[31:0]), zeroing CAM_KEY before the load and re-firing CAM_LOAD
    # with INDEX=0/VALID=0 (BUG-003). CAM_LOAD = {VALID[31], INDEX[7:0]}
    # per tally_regs.rdl.
    await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_CLEAR, 0)
    for key, idx in _default_profile():
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_KEY, key)
        await tb.write32(ADDR_TALLY_CFGW + TALLY_CAM_LOAD, (1 << 31) | (idx & 0xFF))

    # Both injectors target the same 4 KB region
    mask = 0x0000_0FFF
    base = 0x0000_0000
    count = int(os.environ.get('AMBER_SMOKE_COUNT', '200'))

    for ci_base, seed in [(ADDR_CYCLE_INJECTOR0, 0x1234_5678),
                          (ADDR_CYCLE_INJECTOR1, 0xDEAD_BEEF)]:
        await tb.write32(ci_base + CI_SEED, seed)
        await tb.write32(ci_base + CI_ADDR_BASE, base)
        await tb.write32(ci_base + CI_ADDR_MASK, mask)
        await tb.write32(ci_base + CI_TRANS_COUNT, count)
        ctrl = (64 << 8) | 0x00
        await tb.write32(ci_base + CI_CTRL, ctrl)

    # Start both injectors
    await tb.write32(ADDR_CYCLE_INJECTOR0 + CI_CTRL, (64 << 8) | 0x01)
    await tb.write32(ADDR_CYCLE_INJECTOR1 + CI_CTRL, (64 << 8) | 0x01)

    # Poll for done with a generous but bounded timeout.
    max_cycles = 500_000
    done = False
    for _ in range(max_cycles):
        status = await tb.read32(ADDR_HARNESS_CSR + HCSR_STATUS)
        done0 = bool(status & 0x01)
        done1 = bool(status & 0x02)
        if done0 and done1:
            done = True
            break
    assert done, f"cycle injectors did not finish within {max_cycles} cycles"

    # Read injector status and CRCs
    status0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_STATUS)
    status1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_STATUS)
    err0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_ERR_FLAG)
    err1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_ERR_FLAG)

    assert err0 == 0, f"ci0 error flag: 0x{err0:08x}"
    assert err1 == 0, f"ci1 error flag: 0x{err1:08x}"

    rsp_lo0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_RSP_CRC_LO)
    rsp_hi0 = await tb.read32(ADDR_CYCLE_INJECTOR0 + CI_RSP_CRC_HI)
    rsp_lo1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_RSP_CRC_LO)
    rsp_hi1 = await tb.read32(ADDR_CYCLE_INJECTOR1 + CI_RSP_CRC_HI)
    rsp_crc0 = (rsp_hi0 << 32) | rsp_lo0
    rsp_crc1 = (rsp_hi1 << 32) | rsp_lo1

    dut._log.info(f"ci0 status=0x{status0:08x} err=0x{err0:08x} rsp_crc=0x{rsp_crc0:016x}")
    dut._log.info(f"ci1 status=0x{status1:08x} err=0x{err1:08x} rsp_crc=0x{rsp_crc1:016x}")

    # Read a few tally bins
    bins = []
    for i in range(8):
        val = await tb.read64(ADDR_TALLY_CNT + i * 8)
        bins.append(val)
        dut._log.info(f"tally bin[{i}] = {val}")

    # Observation-alive check: the MonBus path (cache monlite -> arbiter ->
    # group -> tally) must actually count events. A config mistake that
    # silences it (BUG-004: group filter masks all-ones, which the group
    # interprets as "drop every packet type") passes every other assertion
    # in this test -- only the bins catch it.
    assert sum(bins) > 0, \
        "tally bins all zero: MonBus observation path is silent"


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_amber_pair_harness_axil(request, test_level):
    module = "test_amber_pair_harness_axil"
    dut_name = "amber_pair_harness_host_tb"
    toplevel = dut_name

    log_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests", "log")
    tests_dir = os.path.join(AMBER_FRAMEWORK_ROOT, "dv", "tests")
    test_name = f"{module}_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")

    # The amber Genesys2 framework root is not in the global env_python defaults.
    os.environ['AMBER_FRAMEWORK_ROOT'] = AMBER_FRAMEWORK_ROOT

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/fpga-systems/Genesys2/cache-ip/amber/dv/filelists/amber_pair_harness_host_tb.f'
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

    # Match the harness-integration lint waiver set from make/fpga_flow.mk so
    # the cocotb simulation elaborates the same design `make lint` gates.
    compile_args = [
        FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
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
