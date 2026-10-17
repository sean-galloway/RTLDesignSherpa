# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_hive_c_loader
# Purpose: TDD test for hive_c_loader (Block 1 VexRiscv + memories + loader)
#
# Documentation: projects/components/compute-eng-ip/hive-serv/dv/testplans/hive_c_loader_testplan.yaml
# Subsystem: hive-serv
#
# Author: sean galloway
# Created: 2026-10-13

"""
Test for hive_c_loader

Validates the VexRiscv "Small" RV32IM core integration with two 32 KB
BRAM memories and the kestrel-pattern AXI4-Lite loader window.

Scenarios:
  LDR-01: reset hold / staged release (first fetch at 0x0000_0000)
  LDR-02: AXIL writes/readback across both memories, wstrb, SLVERR
  LDR-03: load a hand-assembled RV32IM program, run, observe fetch + store
  LDR-04: loader window closed in run mode (writes return SLVERR)
  LDR-05: M-extension smoke (mul / div / rem) with golden compare
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, sim_build_path
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from cov_utils.conftest_coverage import get_coverage_compile_args

repo_root = get_repo_root()

rtl_under_test = os.path.join(repo_root,
    "projects/components/compute-eng-ip/hive-serv/rtl/hive_c_controller/hive_c_loader.sv")
pytestmark = pytest.mark.skipif(not os.path.exists(rtl_under_test),
    reason="RTL not written yet — see vault hive-serv TASK-000")
sys.path.insert(0, repo_root)


# ---------------------------------------------------------------------------
# Level-dependent scaling
# ---------------------------------------------------------------------------
_LVL = current_level()
_D = {
    'gate': dict(axil_iters=2,  timeout_us=120),
    'func': dict(axil_iters=8,  timeout_us=200),
    'full': dict(axil_iters=32, timeout_us=400),
}[_LVL]


# ---------------------------------------------------------------------------
# RV32I/M instruction encoders (no compressed instructions)
# ---------------------------------------------------------------------------
OP_LUI   = 0x37
OP_AUIPC = 0x17
OP_JAL   = 0x6F
OP_JALR  = 0x67
OP_BRANCH = 0x63
OP_LOAD  = 0x03
OP_STORE = 0x23
OP_IMM   = 0x13
OP_REG   = 0x33

F3_ADDI = 0
F3_ADD  = 0
F3_MUL  = 0
F3_SW   = 2
F3_LW   = 2
F3_DIV  = 5  # 0b100 in RV32M
F3_REM  = 6  # 0b110 in RV32M

F7_ADD = 0b0000000
F7_MUL = 0b0000001


def _sext(value, bits):
    """Sign-extend an unsigned bit pattern to a Python int."""
    if value & (1 << (bits - 1)):
        return value - (1 << bits)
    return value


def encode_i(rd, rs1, imm12, funct3, opcode):
    imm = imm12 & 0xFFF
    return (imm << 20) | ((rs1 & 0x1F) << 15) | ((funct3 & 0x7) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F)


def encode_u(rd, imm20, opcode):
    return ((imm20 & 0xFFFFF) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F)


def encode_r(rd, rs1, rs2, funct3, funct7, opcode):
    return ((funct7 & 0x7F) << 25) | ((rs2 & 0x1F) << 20) | ((rs1 & 0x1F) << 15) | ((funct3 & 0x7) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F)


def encode_s(rs1, rs2, imm12, funct3, opcode):
    imm = imm12 & 0xFFF
    imm_hi = (imm >> 5) & 0x7F
    imm_lo = imm & 0x1F
    return (imm_hi << 25) | ((rs2 & 0x1F) << 20) | ((rs1 & 0x1F) << 15) | ((funct3 & 0x7) << 12) | (imm_lo << 7) | (opcode & 0x7F)


def encode_j(rd, imm21, opcode=OP_JAL):
    """Encode a J-type instruction.  imm21 is a signed byte offset."""
    imm = imm21 & 0x1FFFFF
    bit20 = (imm >> 20) & 1
    bits10_1 = (imm >> 1) & 0x3FF
    bit11 = (imm >> 11) & 1
    bits19_12 = (imm >> 12) & 0xFF
    inst = (bit20 << 31) | (bits10_1 << 21) | (bit11 << 20) | (bits19_12 << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F)
    # Python may have produced a negative-looking int because bit20; mask to 32 bits.
    return inst & 0xFFFFFFFF


def instr_lui(rd, imm20):
    return encode_u(rd, imm20, OP_LUI)


def instr_addi(rd, rs1, imm12):
    return encode_i(rd, rs1, imm12, F3_ADDI, OP_IMM)


def instr_add(rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_ADD, F7_ADD, OP_REG)


def instr_mul(rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_MUL, F7_MUL, OP_REG)


def instr_div(rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_DIV, F7_MUL, OP_REG)


def instr_rem(rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_REM, F7_MUL, OP_REG)


def instr_sw(rs1, rs2, imm12):
    return encode_s(rs1, rs2, imm12, F3_SW, OP_STORE)


def instr_lw(rd, rs1, imm12):
    return encode_i(rd, rs1, imm12, F3_LW, OP_LOAD)


def instr_jal(rd, imm21):
    return encode_j(rd, imm21)


# ---------------------------------------------------------------------------
# Cocotb test
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=_D['timeout_us'], timeout_unit='us')
async def cocotb_test_hive_c_loader(dut):
    """Run all hive_c_loader testplan scenarios."""
    log = dut._log
    level = current_level()
    log.info("=" * 80)
    log.info(f"Starting hive_c_loader TDD test  level={level}")
    log.info("=" * 80)

    # Clock and reset
    clock = Clock(dut.clk, 10, units="ns")  # 100 MHz
    cocotb.start_soon(clock.start())

    # Default inputs
    dut.rst_n.value = 0
    dut.run.value = 0

    dut.s_axil_awaddr.value = 0
    dut.s_axil_awvalid.value = 0
    dut.s_axil_wdata.value = 0
    dut.s_axil_wstrb.value = 0
    dut.s_axil_wvalid.value = 0
    dut.s_axil_bready.value = 0

    dut.s_axil_araddr.value = 0
    dut.s_axil_arvalid.value = 0
    dut.s_axil_rready.value = 0

    await Timer(100, units="ns")
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    log.info("Reset complete")

    # -----------------------------------------------------------------------
    # AXIL helpers (single outstanding transaction)
    # -----------------------------------------------------------------------
    async def axil_write(addr, data, wstrb=0xF):
        dut.s_axil_awaddr.value = addr
        dut.s_axil_awvalid.value = 1
        dut.s_axil_wdata.value = data
        dut.s_axil_wstrb.value = wstrb & 0xF
        dut.s_axil_wvalid.value = 1
        dut.s_axil_bready.value = 1

        aw_done = False
        w_done = False
        while not (aw_done and w_done):
            await RisingEdge(dut.clk)
            if not aw_done and dut.s_axil_awready.value == 1:
                aw_done = True
                dut.s_axil_awvalid.value = 0
            if not w_done and dut.s_axil_wready.value == 1:
                w_done = True
                dut.s_axil_wvalid.value = 0

        while dut.s_axil_bvalid.value == 0:
            await RisingEdge(dut.clk)
        resp = int(dut.s_axil_bresp.value)
        await RisingEdge(dut.clk)
        dut.s_axil_bready.value = 0
        return resp

    async def axil_read(addr):
        dut.s_axil_araddr.value = addr
        dut.s_axil_arvalid.value = 1
        dut.s_axil_rready.value = 1
        while dut.s_axil_arready.value == 0:
            await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
        dut.s_axil_arvalid.value = 0
        while dut.s_axil_rvalid.value == 0:
            await RisingEdge(dut.clk)
        rdata = int(dut.s_axil_rdata.value)
        resp = int(dut.s_axil_rresp.value)
        await RisingEdge(dut.clk)
        dut.s_axil_rready.value = 0
        return rdata, resp

    async def load_program(words):
        """Write a list of 32-bit instruction words to I-mem starting at 0x0."""
        for i, w in enumerate(words):
            resp = await axil_write(i * 4, w & 0xFFFFFFFF)
            assert resp == 0, f"load_program write @0x{i*4:04X} returned SLVERR"

    # Internal observation signals (defined in the RTL for simulation visibility)
    ibus_valid = dut.core_ibus_cmd_valid
    ibus_pc = dut.core_ibus_pc
    dbus_valid = dut.core_dbus_cmd_valid
    dbus_wr = dut.core_dbus_wr
    dbus_addr = dut.core_dbus_addr
    dbus_data = dut.core_dbus_data
    dbus_mask = dut.core_dbus_mask

    # -----------------------------------------------------------------------
    # LDR-01: Reset hold and staged release
    # -----------------------------------------------------------------------
    log.info("=== Scenario LDR-01: reset hold and staged release ===")
    await Timer(200, units="ns")
    assert int(ibus_valid.value) == 0, "LDR-01: ibus activity while held in reset"
    assert int(dbus_valid.value) == 0, "LDR-01: dbus activity while held in reset"

    dut.run.value = 1
    # Wait for the first instruction fetch
    for _ in range(50):
        await RisingEdge(dut.clk)
        if int(ibus_valid.value) == 1:
            break
    assert int(ibus_valid.value) == 1, "LDR-01: no ibus cmd after run release"
    pc = int(ibus_pc.value)
    assert pc == 0x00000000, f"LDR-01: first fetch pc = 0x{pc:08X}, expected 0x00000000"
    log.info("LDR-01: first fetch at 0x00000000 - PASS")

    # Halt the core again for the loader tests below
    dut.run.value = 0
    await Timer(100, units="ns")
    await RisingEdge(dut.clk)

    # -----------------------------------------------------------------------
    # LDR-02: AXIL window writes/readback both memories
    # -----------------------------------------------------------------------
    log.info("=== Scenario LDR-02: AXIL writes and readback ===")
    for i in range(_D['axil_iters']):
        # I-mem word, full strobe
        iaddr = 0x0000_1000 + (i * 4)
        idata = 0x1111_2222 + i
        assert await axil_write(iaddr, idata) == 0
        rdata, rresp = await axil_read(iaddr)
        assert rresp == 0, f"LDR-02 I-mem read resp={rresp}"
        assert rdata == idata, f"LDR-02 I-mem readback mismatch @0x{iaddr:08X}: {rdata:08X} != {idata:08X}"

        # D-mem word, full strobe
        daddr = 0x0000_9000 + (i * 4)
        ddata = 0xDEAD_BEEF - i
        assert await axil_write(daddr, ddata) == 0
        rdata, rresp = await axil_read(daddr)
        assert rresp == 0, f"LDR-02 D-mem read resp={rresp}"
        assert rdata == ddata, f"LDR-02 D-mem readback mismatch @0x{daddr:08X}: {rdata:08X} != {ddata:08X}"

    # Sub-word strobes
    await axil_write(0x0000_2000, 0x12345678, wstrb=0x1)
    rdata, _ = await axil_read(0x0000_2000)
    assert rdata == 0x00000078, f"LDR-02 byte strobe expected 0x00000078, got 0x{rdata:08X}"
    await axil_write(0x0000_2000, 0xAABBCCDD, wstrb=0xC)
    rdata, _ = await axil_read(0x0000_2000)
    assert rdata == 0xCCDD0078, f"LDR-02 half strobe expected 0xCCDD0078, got 0x{rdata:08X}"

    # Out-of-window / unaligned -> SLVERR
    assert await axil_write(0x0001_0000, 0x0) == 2, "LDR-02: out-of-window write should SLVERR"
    assert await axil_write(0x0000_0001, 0x0) == 2, "LDR-02: unaligned write should SLVERR"
    _, rresp = await axil_read(0x0001_0000)
    assert rresp == 2, "LDR-02: out-of-window read should SLVERR"
    _, rresp = await axil_read(0x0000_0001)
    assert rresp == 2, "LDR-02: unaligned read should SLVERR"
    log.info("LDR-02: AXIL window readback and SLVERR - PASS")

    # -----------------------------------------------------------------------
    # LDR-03: Load-then-run handoff
    # -----------------------------------------------------------------------
    log.info("=== Scenario LDR-03: load-then-run handoff ===")
    prog = [
        instr_addi(5, 0, 5),      # x5 = 5
        instr_addi(6, 0, 7),      # x6 = 7
        instr_add(7, 5, 6),       # x7 = x5 + x6 = 12
        instr_lui(10, 0x00008),   # x10 = 0x00008000
        instr_sw(10, 7, 0),       # mem[0x8000] = x7
        instr_jal(0, 0),          # infinite loop at this address
    ]
    await load_program(prog)

    dut.run.value = 1
    await RisingEdge(dut.clk)

    # Collect the first several fetch PCs
    pcs = []
    for _ in range(80):
        await RisingEdge(dut.clk)
        if int(ibus_valid.value) == 1:
            pcs.append(int(ibus_pc.value))
        if len(pcs) >= 8:
            break
    expected_pcs = [0x00000000, 0x00000004, 0x00000008, 0x0000000C, 0x00000010, 0x00000014, 0x00000014, 0x00000014]
    assert pcs[:8] == expected_pcs, f"LDR-03: fetch sequence {['0x{:08X}'.format(p) for p in pcs[:8]]} != expected"

    # Wait for the store to appear on the dbus
    store_ok = False
    for _ in range(120):
        await RisingEdge(dut.clk)
        if (int(dbus_valid.value) == 1 and int(dbus_wr.value) == 1 and
                int(dbus_addr.value) == 0x00008000 and int(dbus_data.value) == 12):
            store_ok = True
            break
    assert store_ok, "LDR-03: expected store of 0x0000000C to 0x00008000 not observed"
    log.info("LDR-03: load-then-run handoff - PASS")

    dut.run.value = 0
    await Timer(100, units="ns")
    await RisingEdge(dut.clk)

    # -----------------------------------------------------------------------
    # LDR-04: Loader window closed in run mode
    # -----------------------------------------------------------------------
    log.info("=== Scenario LDR-04: loader window closed in run mode ===")
    # Put a known pattern in D-mem first
    await axil_write(0x0000_8000, 0xCAFE_BABE)
    # Run the core
    dut.run.value = 1
    await RisingEdge(dut.clk)
    # Loader writes must now return SLVERR
    resp = await axil_write(0x0000_8004, 0x0)
    assert resp == 2, "LDR-04: run-mode loader write should SLVERR"
    log.info("LDR-04: run-mode loader access blocked - PASS")
    dut.run.value = 0
    await Timer(100, units="ns")
    await RisingEdge(dut.clk)

    # -----------------------------------------------------------------------
    # LDR-05: M-extension smoke
    # -----------------------------------------------------------------------
    log.info("=== Scenario LDR-05: M-extension smoke ===")
    prog_m = [
        instr_addi(5, 0, 6),       # x5 = 6
        instr_addi(6, 0, 7),       # x6 = 7
        instr_mul(7, 5, 6),        # x7 = 6 * 7 = 42
        instr_addi(8, 0, 20),      # x8 = 20
        instr_addi(9, 0, 4),       # x9 = 4
        instr_div(10, 8, 9),       # x10 = 20 / 4 = 5
        instr_rem(11, 8, 9),       # x11 = 20 % 4 = 0
        instr_add(12, 7, 10),      # x12 = 42 + 5 = 47
        instr_lui(13, 0x00008),    # x13 = 0x00008000
        instr_sw(13, 12, 0),       # mem[0x8000] = 47
        instr_jal(0, 0),           # infinite loop
    ]
    await load_program(prog_m)

    dut.run.value = 1
    await RisingEdge(dut.clk)

    golden = 47
    store_ok = False
    for _ in range(300):
        await RisingEdge(dut.clk)
        if (int(dbus_valid.value) == 1 and int(dbus_wr.value) == 1 and
                int(dbus_addr.value) == 0x00008000 and int(dbus_data.value) == golden):
            store_ok = True
            break
    assert store_ok, f"LDR-05: expected store of 0x{golden:08X} to 0x00008000 not observed"
    log.info("LDR-05: M-extension golden compare - PASS")

    log.info("=" * 80)
    log.info("hive_c_loader test PASSED")
    log.info("=" * 80)


# ---------------------------------------------------------------------------
# Pytest wrapper
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_hive_c_loader(request, test_level):
    """Pytest wrapper for hive_c_loader TDD test."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='vendor/filelists/vexriscv.f')
    # hive_c_loader.sv is not written yet (the module skip above). When it
    # lands, its hive_c_loader.f lands with it and replaces this line.
    verilog_sources.append(rtl_under_test)
    includes.append(os.path.join(repo_root, 'rtl/amba/includes'))

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
    ]
    compile_args.extend(get_coverage_compile_args())

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'test_hive_c_loader_{test_level}'
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="hive_c_loader",
        module=module,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
        extra_env={**level_env(test_level)},
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
