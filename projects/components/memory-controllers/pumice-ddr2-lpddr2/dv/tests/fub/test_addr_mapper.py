# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `addr_mapper`.

The mapping is driven by the single ADDR_MAP.bank_lsb knob (+ optional bank
XOR-hash). The classic "schemes" are just settings: bank_lsb == COL_WIDTH is
ROW_MAJOR, smaller bank_lsb inserts the bank into the column (BANK_INTERLEAVE),
and hash_en folds row bits into the bank (XOR_HASH). Every scenario decodes the
RTL and compares it to the Python reference (addr_mapper_tb.decode_ref), sweeping
bank_lsb across its legal range + hash on/off.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.addr_mapper_tb import AddrMapperTB  # noqa: E402


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_addr_mapper(dut):
    test_type = os.environ.get("TEST_TYPE", "row_major")
    tb = AddrMapperTB(dut)
    await tb.setup()
    scenarios = {
        "row_major":        _row_major,
        "bank_interleave":  _bank_interleave,
        "xor_hash":         _xor_hash,
        "bank_lsb_sweep":   _bank_lsb_sweep,
        "random_soak":      _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


def _assert_match(got, exp, *, tag: str, addr: int) -> None:
    assert (got.rank, got.bank, got.row, got.col) \
        == (exp.rank, exp.bank, exp.row, exp.col), (
        f"{tag} addr=0x{addr:08X}: got "
        f"(r={got.rank}, b={got.bank}, row=0x{got.row:X}, col=0x{got.col:X}) "
        f"want (r={exp.rank}, b={exp.bank}, row=0x{exp.row:X}, "
        f"col=0x{exp.col:X})"
    )


async def _row_major(tb: AddrMapperTB):
    """ROW_MAJOR = bank_lsb == COL_WIDTH (bank above the whole column). Sweep
    column, bank, then row fields; every decode must match the reference."""
    blsb = tb.COL_WIDTH
    addrs = [c * (1 << tb.BYTE_OFFSET_WIDTH) for c in range(16)]
    addrs += [b << (tb.COL_WIDTH + tb.BYTE_OFFSET_WIDTH) for b in range(tb.NUM_BANKS)]
    addrs += [r << (tb.COL_WIDTH + tb.BW + tb.BYTE_OFFSET_WIDTH) for r in range(8)]
    for addr in addrs:
        got = await tb.decode_rtl(addr, blsb)
        _assert_match(got, tb.decode_ref(addr, blsb), tag="ROW_MAJOR", addr=addr)


async def _bank_interleave(tb: AddrMapperTB):
    """BANK_INTERLEAVE = bank_lsb < COL_WIDTH (bank inserted into the column).
    At bank_lsb=4, cache-line stride (2^4 beats) must round-robin across banks."""
    blsb = min(4, tb.COL_WIDTH)
    stride = (1 << blsb) * (1 << tb.BYTE_OFFSET_WIDTH)
    seen = set()
    for k in range(tb.NUM_BANKS):
        addr = k * stride
        got = await tb.decode_rtl(addr, blsb)
        _assert_match(got, tb.decode_ref(addr, blsb), tag="BANK_INTERLEAVE", addr=addr)
        seen.add(got.bank)
    assert seen == set(range(tb.NUM_BANKS)), (
        f"BANK_INTERLEAVE(bank_lsb={blsb}): stride walk visited banks {seen}, "
        f"expected {set(range(tb.NUM_BANKS))}")


async def _xor_hash(tb: AddrMapperTB):
    """XOR_HASH = interleave placement + hash_en. bank ^= row-fold ^ seed.
    Sweep several seeds against the reference."""
    blsb = min(4, tb.COL_WIDTH)
    rng = random.Random(tb.SEED ^ 0xBAD5)
    addrs = [rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1) for _ in range(24)]
    for seed in (0x00, 0x5A, 0xA5, 0xFF):
        for addr in addrs:
            got = await tb.decode_rtl(addr, blsb, hash_en=1, hash_seed=seed)
            exp = tb.decode_ref(addr, blsb, hash_en=1, hash_seed=seed)
            _assert_match(got, exp, tag=f"XOR_HASH(seed={seed:#x})", addr=addr)


async def _bank_lsb_sweep(tb: AddrMapperTB):
    """Sweep bank_lsb across its full legal range [0, COL_WIDTH] (+ over-range,
    which the RTL clamps to COL_WIDTH), hash off and on. Any per-bank_lsb
    slicing drift between RTL and the reference fires here."""
    rng = random.Random(tb.SEED ^ 0x105B)
    addrs = [rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1) for _ in range(12)]
    for blsb in range(0, tb.COL_WIDTH + 3):     # includes over-range (clamped)
        for he in (0, 1):
            seed = rng.randint(0, 0xFF)
            for addr in addrs:
                got = await tb.decode_rtl(addr, blsb, hash_en=he, hash_seed=seed)
                exp = tb.decode_ref(addr, blsb, hash_en=he, hash_seed=seed)
                _assert_match(got, exp, tag=f"sweep(blsb={blsb},he={he})", addr=addr)


async def _random_soak(tb: AddrMapperTB):
    rng = random.Random(tb.SEED ^ 0xC0DE)
    n = {'gate': 32, 'func': 128, 'full': 512}.get(
        os.environ.get("TEST_LEVEL", "FUNC").lower(), 128)
    for _ in range(n):
        addr = rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1)
        blsb = rng.randint(0, tb.COL_WIDTH)
        he   = rng.randint(0, 1)
        seed = rng.randint(0, 0xFF)
        got = await tb.decode_rtl(addr, blsb, hash_en=he, hash_seed=seed)
        exp = tb.decode_ref(addr, blsb, hash_en=he, hash_seed=seed)
        _assert_match(got, exp, tag=f"soak(blsb={blsb},he={he})", addr=addr)


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["row_major", "bank_interleave", "xor_hash",
              "bank_lsb_sweep", "random_soak"]
_GATE = [(t,) for t in ["row_major", "bank_interleave", "xor_hash"]]
_FUNC = [(t,) for t in _ALL_TYPES]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_addr_mapper(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "addr_mapper"
    test_name = f"test_addr_mapper_{test_type}"

    filelist_path = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
                     "rtl/filelists/fub/addr_mapper.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "AXI_ADDR_WIDTH":    "32",
        "NUM_RANKS":         "1",
        "NUM_BANKS":         "8",
        "ROW_WIDTH":         "14",
        "COL_WIDTH":         "10",
        "BYTE_OFFSET_WIDTH": "3",
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "FUNC"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_ADDR_WIDTH":    "32",
        "NUM_RANKS":         "1",
        "NUM_BANKS":         "8",
        "ROW_WIDTH":         "14",
        "COL_WIDTH":         "10",
        "BYTE_OFFSET_WIDTH": "3",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET",
                    "-Wno-WIDTHTRUNC"]
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
        testcase="cocotb_test_addr_mapper",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
