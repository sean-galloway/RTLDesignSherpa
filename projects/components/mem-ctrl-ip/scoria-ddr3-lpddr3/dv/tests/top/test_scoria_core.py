# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""scoria_core: AXI in, DFI out, data through the whole datapath.

The first test of scoria that touches the host interface and the DRAM side at
once. Below it, seventeen FUB suites prove the blocks and a macro suite proves
the scheduler composes; above it, nothing exists yet. This is the boundary the
HAS fixes verification at: "against the DV repository's DFI bus functional
model, in cocotb. No board is required to verify scoria."

The case that matters most is not the round trip -- it is
`write_lands_where_the_dram_thinks_it_lives`. A write-then-read through a
loopback proves the data came back, and proves nothing about WHERE it was
stored: an address-map error that is self-consistent returns the right bytes
from the wrong row. So the backing memory is read directly, at the (bank, row,
col) the address is supposed to decode to. The addr_mapper suite proves that
decode in isolation; this is the only place the whole path has to agree with
it.

Run at the real board geometry -- row 15 / col 10 / 8 banks / 1 GiB, BL8 over a
1:4 gear -- because the framework's MemoryModel is sparse enough to take it
(268M lines, built instantly). Shrinking the geometry to make a test cheap is
how this family lost a 2x read throttle to a suite that could not express the
shape that ships.
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

from tbclasses.scoria_core_tb import ScoriaCoreTB  # noqa: E402
from tbclasses.scoria_dram_configs import dram_config  # noqa: E402

ROW_WIDTH, COL_WIDTH, NUM_BANKS = 15, 10, 8
# DRAM_BEAT_WIDTH is the DFI data width PER PHASE, and for a DDR3 PHY that is
# TWICE the DQ width -- two transfers per CK. Measured from the Genesys 2
# LiteDRAM core that passes memtest on this board:
#
#     SDRAM_PHY_DATABITS      32     the DQ bus
#     SDRAM_PHY_DFI_DATABITS  64     DFI data per phase
#
# and from LiteDRAM's own s7ddrphy, which sets `dfi_databits = 2*databits` and
# packs transfer n into `phases[n//2]` half `n%2`.
#
# So 64 is the BOARD configuration and 32 is not drivable by this PHY. 32 is
# kept reachable because it is a legal shape for a 16-bit device at 1:4 and it
# is what every suite ran before 2026-10-01 -- but the default is the board.
DRAM_BEAT_WIDTH = int(os.environ.get("SCORIA_DRAM_BEAT_WIDTH", "64"))
# The DQ bus. Independent of the beat: DDR3 puts two device words in one
# DFI phase, so beat == 2 x device on this board.
DRAM_DEVICE_WIDTH = int(os.environ.get("SCORIA_DRAM_DEVICE_WIDTH", "32"))
DFI_RATE, DRAM_BL = 4, 8
_SPACING, _PROG, _META = dram_config()

# One AXI beat is the DFI word: per-phase beat x DFI_RATE phases.
# Board config: 64 x 4 = 256 bits = 32 bytes.
BEAT_BYTES = (DRAM_BEAT_WIDTH * DFI_RATE) // 8   # the AXI word = the DFI word


def _pattern(seed, nbytes=BEAT_BYTES):
    rng = random.Random(seed)
    return int.from_bytes(bytes(rng.randrange(256) for _ in range(nbytes)),
                          "little")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_scoria_core(dut):
    tt = os.environ.get("TEST_TYPE", "init_then_write_read_roundtrip")
    tb = ScoriaCoreTB(dut, row_width=ROW_WIDTH, col_width=COL_WIDTH,
                      num_banks=NUM_BANKS,
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
        # The loop closed: one AXI beat down to the DRAM and back.
        addr = 0x0001_0000
        data = _pattern(1)
        await tb.axi_wr.single_write(addr, data)
        got = await tb.axi_rd.single_read(addr)
        chk(got == data,
            f"round trip at 0x{addr:X}: wrote 0x{data:032X}, read "
            f"0x{got:032X}. The datapath is AXI -> intake -> CAM -> scheduler "
            f"-> DFI layer -> PHY model -> memory and back; a mismatch here "
            f"does not say which stage, which is what the FUB suites are for.")
        # A pass has to prove it did work. The controller's own counters are
        # brought out by the wrapper, so the test can require that DRAM
        # commands actually issued -- otherwise a datapath that returned the
        # right bytes without touching the DRAM (or a BFM that answered from
        # thin air) reads exactly like success, and this file's whole claim is
        # that the traffic went through the real DFI layer.
        acts, cols = tb.stat('stat_act_o'), tb.stat('stat_page_hit_o')
        tb.log.info(f"counters after one round trip: ACT={acts} "
                    f"columns={cols} PRE={tb.stat('stat_pre_o')} "
                    f"REF={tb.stat('stat_ref_o')}")
        chk(acts >= 1,
            f"stat_act is {acts}: the DRAM was never activated, so whatever "
            f"the round trip compared did not come from the memory model")
        chk(cols >= 2,
            f"stat_page_hit is {cols}, expected at least 2 column commands "
            f"(the write and the read)")

    elif tt == "write_lands_where_the_dram_thinks_it_lives":
        # THE case. A self-consistent address-map error returns the right
        # bytes from the wrong row, so the round trip cannot see it. Read the
        # backing model at the coordinates the address should decode to.
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
                f"{got.hex()} there. A round trip would have passed -- this is "
                f"the address map, not the data path.")

    elif tt == "read_returns_preloaded_data":
        # Proves the READ path independently of the write path: if both were
        # broken the same way, a round trip would still pass.
        addr = 0x0004_0000
        want = _pattern(7).to_bytes(BEAT_BYTES, "little")
        tb.preload_memory(addr, want)
        got = await tb.axi_rd.single_read(addr)
        chk(got.to_bytes(BEAT_BYTES, "little") == want,
            f"preloaded {want.hex()} at 0x{addr:X} and AXI read back "
            f"{got.to_bytes(BEAT_BYTES, 'little').hex()}; the write path was "
            f"not involved, so this is the read return path or the decode")

    elif tt == "several_banks_round_trip":
        # One beat per bank, so the test crosses every bank machine rather
        # than exercising bank 0 eight times.
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
def test_scoria_core(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_core_tb"          # the DV wrapper, not scoria_core
    test_name = f"test_scoria_core_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "dv/filelists/scoria_core_tb.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_core",
        sim_build=sim_build, simulator="verilator",
        parameters={"ROW_WIDTH": str(ROW_WIDTH), "COL_WIDTH": str(COL_WIDTH),
                    "NUM_BANKS": str(NUM_BANKS),
                    "DRAM_BEAT_WIDTH": str(DRAM_BEAT_WIDTH),
                    "DRAM_DEVICE_WIDTH": str(DRAM_DEVICE_WIDTH),
                    "DFI_RATE": str(DFI_RATE), "DRAM_BL": str(DRAM_BL)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET", "--assert",
                      # The BFMs reach into the wrapper's internal phy_dfi_*
                      # nets, which are not ports of the toplevel.
                      "--public-flat-rw"],
        keep_files=True, timescale="1ns/1ps")
