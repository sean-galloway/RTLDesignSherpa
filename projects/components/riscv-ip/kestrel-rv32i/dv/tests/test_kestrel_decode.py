# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_decode
# Purpose: Functional unit tests for kestrel-rv32i ALU, immediate generator,
#          and instruction decoder.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Created: 2026-10-06

"""ALU, immediate-generator, and decoder tests for kestrel-rv32i."""

import os
import random

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

# ---------------------------------------------------------------------------
# Constants that mirror kestrel_pkg enum ordering (must stay in lock-step).
# ---------------------------------------------------------------------------
ALU_ADD = 0
ALU_SUB = 1
ALU_AND = 2
ALU_OR = 3
ALU_XOR = 4
ALU_SLL = 5
ALU_SRL = 6
ALU_SRA = 7
ALU_SLT = 8
ALU_SLTU = 9

IMM_I = 0
IMM_S = 1
IMM_B = 2
IMM_U = 3
IMM_J = 4

ALU_OP_NAMES = {
    ALU_ADD: "ADD",
    ALU_SUB: "SUB",
    ALU_AND: "AND",
    ALU_OR: "OR",
    ALU_XOR: "XOR",
    ALU_SLL: "SLL",
    ALU_SRL: "SRL",
    ALU_SRA: "SRA",
    ALU_SLT: "SLT",
    ALU_SLTU: "SLTU",
}

# ---------------------------------------------------------------------------
# ALU golden model
# ---------------------------------------------------------------------------

def _signed32(x: int) -> int:
    """Convert an unsigned 32-bit value to signed two's-complement."""
    return x - (1 << 32) if x & (1 << 31) else x


def _mask32(x: int) -> int:
    """Truncate to 32 bits."""
    return x & ((1 << 32) - 1)


def alu_golden(op: int, a: int, b: int):
    """Return (y, eq, lt, ltu) for kestrel_alu."""
    sa = _signed32(a)
    sb = _signed32(b)
    shamt = b & 0x1F

    eq = a == b
    lt = sa < sb
    ltu = a < b

    if op == ALU_ADD:
        y = _mask32(a + b)
    elif op == ALU_SUB:
        y = _mask32(a - b)
    elif op == ALU_AND:
        y = a & b
    elif op == ALU_OR:
        y = a | b
    elif op == ALU_XOR:
        y = a ^ b
    elif op == ALU_SLL:
        y = _mask32(a << shamt)
    elif op == ALU_SRL:
        y = _mask32(a >> shamt)
    elif op == ALU_SRA:
        y = _mask32(sa >> shamt)
    elif op == ALU_SLT:
        y = 1 if lt else 0
    elif op == ALU_SLTU:
        y = 1 if ltu else 0
    else:
        raise ValueError(f"unknown ALU op {op}")

    return y, eq, lt, ltu


# ---------------------------------------------------------------------------
# Immediate golden model
# ---------------------------------------------------------------------------

def _sign_extend(value: int, bits: int) -> int:
    if value & (1 << (bits - 1)):
        value -= 1 << bits
    return value


def imm_golden(insn: int, sel: int) -> int:
    """Sign-extend the immediate from `insn` according to `sel`."""
    if sel == IMM_I:
        return _sign_extend((insn >> 20) & 0xFFF, 12)
    if sel == IMM_S:
        imm12 = (((insn >> 25) & 0x7F) << 5) | ((insn >> 7) & 0x1F)
        return _sign_extend(imm12, 12)
    if sel == IMM_B:
        imm13 = (((insn >> 31) & 1) << 12) | (((insn >> 7) & 1) << 11) | \
                (((insn >> 25) & 0x3F) << 5) | (((insn >> 8) & 0xF) << 1)
        return _sign_extend(imm13, 13)
    if sel == IMM_U:
        return insn & 0xFFFFF000
    if sel == IMM_J:
        imm21 = (((insn >> 31) & 1) << 20) | (((insn >> 12) & 0xFF) << 12) | \
                (((insn >> 20) & 1) << 11) | (((insn >> 21) & 0x3FF) << 1)
        return _sign_extend(imm21, 21)
    raise ValueError(f"unknown imm_sel {sel}")


# ---------------------------------------------------------------------------
# Decode golden table
#
# Instruction words were produced by assembling each instruction with
# riscv-none-elf-as -march=rv32i -mabi=ilp32 and reading the first word from
# riscv-none-elf-objdump -d.  The control bundle follows the RV32I datapath
# plan: R-type uses rs1/rs2; I/S/B/U/J select the corresponding immediate;
# branches, jumps, and auipc drive the ALU with PC as src_a.
# ---------------------------------------------------------------------------

def _ctrl(
    alu_op=ALU_ADD,
    imm_sel=IMM_I,
    alu_src_a_pc=0,
    alu_src_b_imm=0,
    rd_wen=0,
    dmem_req=0,
    dmem_we=0,
    dmem_size=0,
    branch=0,
    jump=0,
    jalr=0,
    halt_cause=0,
    csr_stub=0,
):
    return {
        "alu_op": alu_op,
        "imm_sel": imm_sel,
        "alu_src_a_pc": alu_src_a_pc,
        "alu_src_b_imm": alu_src_b_imm,
        "rd_wen": rd_wen,
        "dmem_req": dmem_req,
        "dmem_we": dmem_we,
        "dmem_size": dmem_size,
        "branch": branch,
        "jump": jump,
        "jalr": jalr,
        "halt_cause": halt_cause,
        "csr_stub": csr_stub,
    }


# fmt: off
DECODE_GOLDEN = {
    # R-type arithmetic
    0x003100b3: _ctrl(alu_op=ALU_ADD, rd_wen=1),                       # add x1, x2, x3
    0x403100b3: _ctrl(alu_op=ALU_SUB, rd_wen=1),                       # sub x1, x2, x3
    0x003110b3: _ctrl(alu_op=ALU_SLL, rd_wen=1),                       # sll x1, x2, x3
    0x003120b3: _ctrl(alu_op=ALU_SLT, rd_wen=1),                       # slt x1, x2, x3
    0x003130b3: _ctrl(alu_op=ALU_SLTU, rd_wen=1),                      # sltu x1, x2, x3
    0x003140b3: _ctrl(alu_op=ALU_XOR, rd_wen=1),                       # xor x1, x2, x3
    0x003150b3: _ctrl(alu_op=ALU_SRL, rd_wen=1),                       # srl x1, x2, x3
    0x403150b3: _ctrl(alu_op=ALU_SRA, rd_wen=1),                       # sra x1, x2, x3
    0x003160b3: _ctrl(alu_op=ALU_OR, rd_wen=1),                        # or x1, x2, x3
    0x003170b3: _ctrl(alu_op=ALU_AND, rd_wen=1),                       # and x1, x2, x3

    # I-type arithmetic / logic
    0xffb10093: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # addi x1, x2, -5
    0xffb12093: _ctrl(alu_op=ALU_SLT, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # slti x1, x2, -5
    0x00513093: _ctrl(alu_op=ALU_SLTU, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),  # sltiu x1, x2, 5
    0x0ff14093: _ctrl(alu_op=ALU_XOR, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # xori x1, x2, 0xFF
    0x0ff16093: _ctrl(alu_op=ALU_OR, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),    # ori x1, x2, 0xFF
    0x0ff17093: _ctrl(alu_op=ALU_AND, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # andi x1, x2, 0xFF
    0x00311093: _ctrl(alu_op=ALU_SLL, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # slli x1, x2, 3
    0x00715093: _ctrl(alu_op=ALU_SRL, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # srli x1, x2, 7
    0x40715093: _ctrl(alu_op=ALU_SRA, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1),   # srai x1, x2, 7

    # Loads
    0x00010083: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, dmem_req=1, dmem_size=0),  # lb
    0x00011083: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, dmem_req=1, dmem_size=1),  # lh
    0x00012083: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, dmem_req=1, dmem_size=2),  # lw
    0x00014083: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, dmem_req=1, dmem_size=0),  # lbu
    0x00015083: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, dmem_req=1, dmem_size=1),  # lhu

    # Stores
    0x00310023: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_S, alu_src_b_imm=1, dmem_req=1, dmem_we=1, dmem_size=0),  # sb
    0x00311023: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_S, alu_src_b_imm=1, dmem_req=1, dmem_we=1, dmem_size=1),  # sh
    0x00312023: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_S, alu_src_b_imm=1, dmem_req=1, dmem_we=1, dmem_size=2),  # sw

    # Branches
    0x00208263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # beq
    0x00209263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # bne
    0x0020c263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # blt
    0x0020d263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # bge
    0x0020e263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # bltu
    0x0020f263: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_B, alu_src_a_pc=1, alu_src_b_imm=1, branch=1),  # bgeu

    # Jumps / U-type
    0x004000ef: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_J, alu_src_a_pc=1, alu_src_b_imm=1, rd_wen=1, jump=1),   # jal
    0x000100e7: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_I, alu_src_b_imm=1, rd_wen=1, jalr=1),                   # jalr
    0x123450b7: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_U, alu_src_b_imm=1, rd_wen=1),                            # lui
    0x12345097: _ctrl(alu_op=ALU_ADD, imm_sel=IMM_U, alu_src_a_pc=1, alu_src_b_imm=1, rd_wen=1),            # auipc

    # System (halt paths)
    0x00000073: _ctrl(halt_cause=1),   # ecall
    0x00100073: _ctrl(halt_cause=2),   # ebreak

    # MISC-MEM: FENCE / FENCE.I retire as NOPs (funct3 000/001)
    0x0ff0000f: _ctrl(),               # fence iorw, iorw
    0x0000100f: _ctrl(),               # fence.i

    # System stubs: MRET falls through to pc+4; the CSR class retires with a
    # zero writeback (no CSR state exists — reads return zero, writes drop).
    0x30200073: _ctrl(),                          # mret
    0x30029573: _ctrl(rd_wen=1, csr_stub=1),      # csrrw a0, mstatus, t0
    0x30005573: _ctrl(rd_wen=1, csr_stub=1),      # csrrwi a0, mstatus, 0
    0xf1402573: _ctrl(rd_wen=1, csr_stub=1),      # csrr  a0, mhartid
}
# fmt: on

ILLEGAL_WORDS = [0x00000000, 0xFFFFFFFF]

# RESERVED encodings of implemented opcodes must land on the illegal halt.
RESERVED_WORDS = [
    0x30004073,      # SYSTEM funct3=100 (reserved)
    0x10500073,      # SYSTEM funct3=0, imm12=0x105 (wfi: not implemented)
    0x0000200f,      # MISC-MEM funct3=2 (reserved)
    0x02109133,      # sll with funct7=0x01 (reserved)
]

# Words chosen so that imm_golden can exercise every format including sign
# extension and the large U/J encodings.
IMM_VECTORS = [
    (0x00510093, IMM_I, 5),          # addi x1, x2, 5
    (0xFFB10093, IMM_I, -5),         # addi x1, x2, -5
    (0x00312223, IMM_S, 4),          # sw x3, 4(x2)
    (0xFE312E23, IMM_S, -4),         # sw x3, -4(x2)
    (0x00208263, IMM_B, 4),          # beq forward
    (0xFE208EE3, IMM_B, -4),         # beq backward
    (0x123450B7, IMM_U, 0x12345000), # lui x1, 0x12345
    (0x004000EF, IMM_J, 4),          # jal forward
    (0xFFDFF0EF, IMM_J, -4),         # jal backward
]

ALU_OP_LIST = list(range(10))
ALU_VALUES = [
    0x00000000,
    0x00000001,
    0xFFFFFFFF,
    0x7FFFFFFF,
    0x80000000,
    0x55555555,
    0xAAAAAAAA,
    0x12345678,
    0xFEDCBA98,
]


def _check_decode(dut, exp):
    """Assert the decoder outputs match the expected control bundle."""
    assert int(dut.alu_op.value) == exp["alu_op"], f"alu_op mismatch"
    assert int(dut.imm_sel.value) == exp["imm_sel"], f"imm_sel mismatch"
    assert int(dut.alu_src_a_pc.value) == exp["alu_src_a_pc"], f"alu_src_a_pc mismatch"
    assert int(dut.alu_src_b_imm.value) == exp["alu_src_b_imm"], f"alu_src_b_imm mismatch"
    assert int(dut.rd_wen.value) == exp["rd_wen"], f"rd_wen mismatch"
    assert int(dut.dmem_req.value) == exp["dmem_req"], f"dmem_req mismatch"
    assert int(dut.dmem_we.value) == exp["dmem_we"], f"dmem_we mismatch"
    assert int(dut.dmem_size.value) == exp["dmem_size"], f"dmem_size mismatch"
    assert int(dut.branch.value) == exp["branch"], f"branch mismatch"
    assert int(dut.jump.value) == exp["jump"], f"jump mismatch"
    assert int(dut.jalr.value) == exp["jalr"], f"jalr mismatch"
    assert int(dut.halt_cause.value) == exp["halt_cause"], f"halt_cause mismatch"
    assert int(dut.csr_stub.value) == exp["csr_stub"], f"csr_stub mismatch"


# ---------------------------------------------------------------------------
# cocotb tests
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_kestrel_alu(dut):
    """Exhaustive ALU check against Python golden model."""
    seed = int(os.environ.get("SEED", "0"))
    random.seed(seed)
    dut._log.info(f"kestrel_alu test with seed {seed}")

    values = ALU_VALUES + [random.randint(0, 0xFFFFFFFF) for _ in range(8)]

    for op in ALU_OP_LIST:
        for a in values:
            for b in values:
                dut.op.value = op
                dut.a.value = a
                dut.b.value = b
                await Timer(1, units="ns")

                exp_y, exp_eq, exp_lt, exp_ltu = alu_golden(op, a, b)
                got_y = int(dut.y.value)
                got_eq = int(dut.eq.value)
                got_lt = int(dut.lt.value)
                got_ltu = int(dut.ltu.value)

                assert got_y == exp_y, (
                    f"{ALU_OP_NAMES[op]} a=0x{a:08x} b=0x{b:08x}: "
                    f"y=0x{got_y:08x}, expected 0x{exp_y:08x}"
                )
                assert got_eq == exp_eq, f"eq mismatch for {ALU_OP_NAMES[op]}"
                assert got_lt == exp_lt, f"lt mismatch for {ALU_OP_NAMES[op]}"
                assert got_ltu == exp_ltu, f"ltu mismatch for {ALU_OP_NAMES[op]}"

    dut._log.info("kestrel_alu test PASSED")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_kestrel_imm_gen(dut):
    """Golden vectors for all five immediate formats."""
    for insn, sel, expected in IMM_VECTORS:
        dut.insn.value = insn
        dut.sel.value = sel
        await Timer(1, units="ns")
        got = int(dut.imm.value)
        assert got == _mask32(expected), (
            f"imm sel={sel} insn=0x{insn:08x}: got 0x{got:08x}, "
            f"expected 0x{_mask32(expected):08x}"
        )

    dut._log.info("kestrel_imm_gen test PASSED")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_kestrel_decode(dut):
    """Decode truth table: every RV32I instruction plus illegal opcodes."""
    for insn, expected in DECODE_GOLDEN.items():
        dut.insn.value = insn
        await Timer(1, units="ns")
        _check_decode(dut, expected)

    illegal = _ctrl(halt_cause=0xF)
    for insn in ILLEGAL_WORDS + RESERVED_WORDS:
        dut.insn.value = insn
        await Timer(1, units="ns")
        _check_decode(dut, illegal)

    dut._log.info("kestrel_decode test PASSED")


# ---------------------------------------------------------------------------
# pytest wrappers
# ---------------------------------------------------------------------------

DUT_CASES = [
    ("kestrel_alu", "cocotb_test_kestrel_alu"),
    ("kestrel_imm_gen", "cocotb_test_kestrel_imm_gen"),
    ("kestrel_decode", "cocotb_test_kestrel_decode"),
]


@pytest.mark.parametrize("dut_name, testcase", DUT_CASES)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_kestrel_decode(request, dut_name, testcase, test_level, description=None):
    """Pytest wrapper for the kestrel ALU/imm-gen/decode cocotb tests."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    test_name_plus_params = f"{testcase}_{test_level}"

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
        "--timescale", "1ns/1ps",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
