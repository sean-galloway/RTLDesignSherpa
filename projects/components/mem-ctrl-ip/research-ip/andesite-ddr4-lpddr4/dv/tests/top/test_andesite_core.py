# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""andesite_core: AXI in, DFI 4.0 out, data through the whole datapath.

The four-test suite carried from `test_scoria_core.py`:
  init_then_write_read_roundtrip
  write_lands_where_the_dram_thinks_it_lives
  read_returns_preloaded_data
  several_banks_round_trip

Run at the andesite DDR4 design point -- row 14 / col 10 / 8 banks / BL8 /
DFI_RATE 2 -- because the framework's MemoryModel is sparse enough to take it.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_core_tb import AndesiteCoreTB  # noqa: E402
from tbclasses.andesite_dram_configs import dram_config  # noqa: E402

ROW_WIDTH, COL_WIDTH, NUM_BANKS, NUM_BG = 14, 10, 8, 4
DRAM_BEAT_WIDTH = int(os.environ.get("ANDESITE_DRAM_BEAT_WIDTH", "64"))
DRAM_DEVICE_WIDTH = int(os.environ.get("ANDESITE_DRAM_DEVICE_WIDTH", "64"))
DFI_RATE, DRAM_BL = 2, 8
_SPACING, _PROG, _META = dram_config()

BEAT_BYTES = (DRAM_BEAT_WIDTH * DFI_RATE) // 8


def _pattern(seed, nbytes=BEAT_BYTES):
    rng = random.Random(seed)
    return int.from_bytes(bytes(rng.randrange(256) for _ in range(nbytes)),
                          "little")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_andesite_core(dut):
    tt = os.environ.get("TEST_TYPE", "init_then_write_read_roundtrip")
    tb = AndesiteCoreTB(dut, row_width=ROW_WIDTH, col_width=COL_WIDTH,
                        num_banks=NUM_BANKS, num_bg=NUM_BG,
                        dram_beat_width=DRAM_BEAT_WIDTH,
                        dram_device_width=DRAM_DEVICE_WIDTH)
    await tb.start()
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    ok = await tb.complete_init()
    chk(ok, "init never completed, so nothing below it can be measured")
    if not ok:
        assert not fails, "\n  ".join(fails)

    if tt == "init_then_write_read_roundtrip":
        addr = 0x0001_0000
        data = _pattern(1)
        await tb.axi_wr.single_write(addr, data)
        got = await tb.axi_rd.single_read(addr)
        chk(got == data,
            f"round trip at 0x{addr:X}: wrote 0x{data:032X}, read "
            f"0x{got:032X}.")
        acts, cols = tb.stat('stat_act_o'), tb.stat('stat_page_hit_o')
        tb.log.info(f"counters after one round trip: ACT={acts} "
                    f"columns={cols} PRE={tb.stat('stat_pre_o')} "
                    f"REF={tb.stat('stat_ref_o')}")
        chk(acts >= 1,
            f"stat_act is {acts}: the DRAM was never activated")
        chk(cols >= 2,
            f"stat_page_hit is {cols}, expected at least 2 column commands")

    elif tt == "write_lands_where_the_dram_thinks_it_lives":
        for i, addr in enumerate((0x0000_0000, 0x0000_1000, 0x0000_8000,
                                  0x0002_4000, 0x0010_0010)):
            addr &= ~(BEAT_BYTES - 1)
            data = _pattern(100 + i)
            await tb.axi_wr.single_write(addr, data)
            for _ in range(40):
                await RisingEdge(dut.aclk)
            want = data.to_bytes(BEAT_BYTES, "little")
            got = tb.peek_memory(addr, BEAT_BYTES)
            rank, bank, row, col = tb.decode(addr)
            chk(got == want,
                f"0x{addr:08X} should decode to bank {bank} row 0x{row:X} col "
                f"0x{col:X} and hold {want.hex()}; the DRAM model holds "
                f"{got.hex()} there.")

    elif tt == "read_returns_preloaded_data":
        addr = 0x0004_0000
        want = _pattern(7).to_bytes(BEAT_BYTES, "little")
        tb.preload_memory(addr, want)
        got = await tb.axi_rd.single_read(addr)
        chk(got.to_bytes(BEAT_BYTES, "little") == want,
            f"preloaded {want.hex()} at 0x{addr:X} and AXI read back "
            f"{got.to_bytes(BEAT_BYTES, 'little').hex()}")

    elif tt == "several_banks_round_trip":
        page = (1 << COL_WIDTH) * BEAT_BYTES // DFI_RATE
        wrote = {}
        for b in range(NUM_BANKS):
            addr = (b << COL_WIDTH) * (DRAM_BEAT_WIDTH // 8)
            addr &= ~(BEAT_BYTES - 1)
            wrote[addr] = _pattern(200 + b)
            await tb.axi_wr.single_write(addr, wrote[addr])
        for addr, data in wrote.items():
            got = await tb.axi_rd.single_read(addr)
            _, bank, row, col = tb.decode(addr)
            chk(got == data,
                f"bank {bank} (0x{addr:08X}): wrote 0x{data:032X}, read "
                f"0x{got:032X}")
        tb.log.info(f"crossed {len(wrote)} banks, page {page} B")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["init_then_write_read_roundtrip",
         "write_lands_where_the_dram_thinks_it_lives"]
_FUNC = _GATE + ["read_returns_preloaded_data", "several_banks_round_trip"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_core(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_core_tb"
    test_name = f"test_andesite_core_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "dv/filelists/andesite_core_tb.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_core",
        sim_build=sim_build, simulator="verilator",
        parameters={"ROW_WIDTH": str(ROW_WIDTH), "COL_WIDTH": str(COL_WIDTH),
                    "NUM_BANKS": str(NUM_BANKS), "NUM_BG": "4",
                    "ADDR_WIDTH": "18",
                    "DRAM_BEAT_WIDTH": str(DRAM_BEAT_WIDTH),
                    "DRAM_DEVICE_WIDTH": str(DRAM_DEVICE_WIDTH),
                    "DFI_RATE": str(DFI_RATE), "DRAM_BL": str(DRAM_BL)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET", "--assert",
                      "--public-flat-rw"],
        keep_files=True, timescale="1ns/1ps")
