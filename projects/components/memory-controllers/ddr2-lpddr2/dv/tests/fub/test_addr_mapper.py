# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `addr_mapper`.

Three runtime-selectable address schemes — ROW_MAJOR, BANK_INTERLEAVE,
XOR_HASH. Only ROW_MAJOR is exercised by any top-level test today
(the parameter default), so the other two are uncovered. These
scenarios exercise each scheme directly against a Python reference.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.addr_mapper_tb import (  # noqa: E402
    AddrMapperTB,
    SCHEME_ROW_MAJOR, SCHEME_BANK_INTERLEAVE, SCHEME_XOR_HASH,
)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_addr_mapper(dut):
    test_type = os.environ.get("TEST_TYPE", "row_major")
    tb = AddrMapperTB(dut)
    await tb.setup()
    scenarios = {
        "row_major":        _row_major,
        "bank_interleave":  _bank_interleave,
        "xor_hash":         _xor_hash,
        "all_schemes":      _all_schemes,
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
    """ROW_MAJOR — addresses sweep one column field, then bank field,
    then row field. Every decode must match the Python reference."""
    test_addrs = []
    # Sweep column inside row 0 bank 0
    for c in range(0, 16):
        test_addrs.append(c * (1 << tb.BYTE_OFFSET_WIDTH))
    # Sweep bank inside row 0
    for b in range(tb.NUM_BANKS):
        test_addrs.append((b << (tb.COL_WIDTH + tb.BYTE_OFFSET_WIDTH)))
    # Sweep row inside bank 0
    for r in range(8):
        test_addrs.append(r << (tb.COL_WIDTH + tb.BW + tb.BYTE_OFFSET_WIDTH))
    for addr in test_addrs:
        got = await tb.decode_rtl(addr, SCHEME_ROW_MAJOR)
        exp = tb.decode_row_major(addr)
        _assert_match(got, exp, tag="ROW_MAJOR", addr=addr)


async def _bank_interleave(tb: AddrMapperTB):
    """BANK_INTERLEAVE — cache-line stride must round-robin across
    banks. This scheme is *never* selected at the top, so a synthesis
    bug here would survive every other test in the suite."""
    # Cache-line addresses (stride = 2^CL beats) hit a different bank
    # each iteration.
    stride = (1 << tb.CL) * (1 << tb.BYTE_OFFSET_WIDTH)
    seen_banks = set()
    for k in range(tb.NUM_BANKS):
        addr = k * stride
        got = await tb.decode_rtl(addr, SCHEME_BANK_INTERLEAVE)
        exp = tb.decode_bank_interleave(addr)
        _assert_match(got, exp, tag="BANK_INTERLEAVE", addr=addr)
        seen_banks.add(got.bank)
    # Stride-walking the cache line must visit every bank exactly once.
    assert seen_banks == set(range(tb.NUM_BANKS)), (
        f"BANK_INTERLEAVE: walking N cache-lines visited banks "
        f"{seen_banks}, expected {set(range(tb.NUM_BANKS))}"
    )


async def _xor_hash(tb: AddrMapperTB):
    """XOR_HASH — bank index is `bank_raw XOR row[low] XOR row[mid]
    XOR seed[low]`. Test several seeds against the Python reference,
    and verify two row addresses that would collide under
    BANK_INTERLEAVE land on different banks under XOR_HASH (the
    point of the hash)."""
    rng = random.Random(tb.SEED ^ 0xBAD5)
    test_addrs = [rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1)
                  for _ in range(24)]
    for seed in (0x00, 0x5A, 0xA5, 0xFF):
        for addr in test_addrs:
            got = await tb.decode_rtl(addr, SCHEME_XOR_HASH, xor_seed=seed)
            exp = tb.decode_xor_hash(addr, xor_seed=seed)
            _assert_match(got, exp,
                          tag=f"XOR_HASH(seed={seed:#x})", addr=addr)


async def _all_schemes(tb: AddrMapperTB):
    """Same input address into all three schemes — verifies the
    runtime mux at the bottom of addr_mapper picks the right per-
    scheme computation (a "mux all to ROW_MAJOR" regression would
    fire here)."""
    rng = random.Random(tb.SEED ^ 0xC0DA)
    for _ in range(16):
        addr = rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1)
        seed = rng.randint(0, 0xFF)
        got_rm = await tb.decode_rtl(addr, SCHEME_ROW_MAJOR)
        got_bi = await tb.decode_rtl(addr, SCHEME_BANK_INTERLEAVE)
        got_xh = await tb.decode_rtl(addr, SCHEME_XOR_HASH,
                                     xor_seed=seed)
        _assert_match(got_rm, tb.decode_row_major(addr),
                      tag="all/ROW_MAJOR", addr=addr)
        _assert_match(got_bi, tb.decode_bank_interleave(addr),
                      tag="all/BANK_INTERLEAVE", addr=addr)
        _assert_match(got_xh, tb.decode_xor_hash(addr, seed),
                      tag="all/XOR_HASH", addr=addr)


async def _random_soak(tb: AddrMapperTB):
    rng = random.Random(tb.SEED ^ 0xC0DE)
    n = {'gate': 32, 'func': 128, 'full': 512}.get(
        os.environ.get("TEST_LEVEL", "FUNC").lower(), 128)
    for _ in range(n):
        addr   = rng.randint(0, (1 << tb.AXI_ADDR_WIDTH) - 1)
        scheme = rng.choice([SCHEME_ROW_MAJOR, SCHEME_BANK_INTERLEAVE,
                             SCHEME_XOR_HASH])
        seed   = rng.randint(0, 0xFF)
        got = await tb.decode_rtl(addr, scheme, xor_seed=seed)
        if scheme == SCHEME_ROW_MAJOR:
            exp = tb.decode_row_major(addr)
            tag = "soak/ROW_MAJOR"
        elif scheme == SCHEME_BANK_INTERLEAVE:
            exp = tb.decode_bank_interleave(addr)
            tag = "soak/BANK_INTERLEAVE"
        else:
            exp = tb.decode_xor_hash(addr, seed)
            tag = "soak/XOR_HASH"
        _assert_match(got, exp, tag=tag, addr=addr)


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["row_major", "bank_interleave", "xor_hash",
              "all_schemes", "random_soak"]
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

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/addr_mapper.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
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
        "SEED": str(random.randint(0, 100000)),
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
        # All three synth flags ON — otherwise the BANK_INTERLEAVE /
        # XOR_HASH branches collapse to '0 and the test can't decide
        # whether the mux logic is correct.
        "SYNTH_ROW_MAJOR":       "1",
        "SYNTH_BANK_INTERLEAVE": "1",
        "SYNTH_XOR_HASH":        "1",
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
