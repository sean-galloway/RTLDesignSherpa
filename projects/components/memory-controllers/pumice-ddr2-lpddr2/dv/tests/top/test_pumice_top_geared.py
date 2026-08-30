# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Runner for pumice_top_geared: the controller core (fixed DW = DRAM_BEAT*DFI_RATE)
# behind the repo's FORMALLY-VERIFIED AXI dwidth converters, so the HOST AXI width
# is a free parameter. Proves the WRAPPER WIRING (the converters are already
# formally proven): a write burst driven at the host width must round-trip back
# through host-width reads. Covers down-gear (host < DW), up-gear (host > DW), and
# GEAR-1 (host == DW, converters bypassed).

import os
import sys
import random

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_top_csr_tb import PumiceTopCsrTB  # noqa: E402
from tbclasses.pumice_sequences import build_b2b_wr_rd_sequences  # noqa: E402

# core geometry (fixed)
DFI_RATE  = 2
DRAM_BEAT = 64
BL        = 8
DW        = DRAM_BEAT * DFI_RATE          # core AXI width = 128
NUM_BANKS, ROW_WIDTH, COL_WIDTH = 8, 14, 10
BASE      = 0x10000


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_pumice_top_geared(dut):
    host_w = int(os.environ.get("HOST_AXI_DATA_WIDTH", "64"))
    random.seed(int(os.environ.get("SEED", "1")))

    tb = PumiceTopCsrTB(dut, dram_beat_width=DRAM_BEAT, dfi_rate=DFI_RATE, dram_bl=BL,
                        num_ranks=1, num_banks=NUM_BANKS, row_width=ROW_WIDTH,
                        col_width=COL_WIDTH, mem_type="DDR2",
                        host_axi_data_width=host_w)
    await tb.reset()
    tb.init_dfi_slave()
    await tb.program_defaults(page_policy=2, mem_type="DDR2")   # CLOSE (software encoding)
    await tb.wait_for_init_done()
    # bready/rready are NOT tied high here: init_axi_masters() builds the
    # master BFMs, which own every signal on s_axi including the response
    # readies. Poking them first only creates a second driver (PUMICE-014).
    tb.init_axi_masters()
    tb.set_axi_timing_profile("backtoback")

    # One DRAM burst = BL*DRAM_BEAT bits; express it in HOST beats.
    host_beats = (BL * DRAM_BEAT) // host_w
    assert host_beats >= 1, f"host width {host_w} too wide for one DRAM burst"

    # GEARED_BURST_BEATS lets the test issue a burst SHORTER than a whole DRAM
    # burst -- which is what the ddr2-char harness does (host_w=64, AxLEN=0)
    # and what nothing here previously covered: host_beats is always a whole
    # burst, so the down-gear path had only ever seen aligned traffic.
    burst_beats = int(os.environ.get("GEARED_BURST_BEATS", "0")) or host_beats
    tb.log.info(f"GEARED: host={host_w}b DW={DW}b -> {host_beats} host "
                f"beats/burst, issuing {burst_beats}")

    wr, rd, _ = build_b2b_wr_rd_sequences(
        n_bursts=4, burst_len=burst_beats, base_addr=BASE, data_width=host_w)

    # Direct round-trip: what we wrote at each host byte-addr must read back.
    bpw = host_w // 8
    hmask = (1 << host_w) - 1
    exp = {}
    for b in wr.bursts:
        if not getattr(b, "is_write", True):
            continue
        for ki, val in enumerate(b.data):
            exp[b.addr + ki * bpw] = val & hmask

    await tb.run_writes(wr, drain_cycles=300)
    rd_dicts = await tb.run_sequence(rd)

    n_checked = 0
    for d in rd_dicts:
        assert d.get("data") is not None, f"read @ {d.get('addr'):#x} no data ({d})"
        for ki, val in enumerate(d["data"]):
            byte_addr = d["addr"] + ki * bpw
            assert byte_addr in exp, f"read addr {byte_addr:#x} not written ({sorted(exp)[:4]}...)"
            assert (val & hmask) == exp[byte_addr], (
                f"GEAR host={host_w}: R @ {byte_addr:#x} = {val & hmask:#x} "
                f"!= wrote {exp[byte_addr]:#x}")
            n_checked += 1
    assert n_checked == len(exp), f"read {n_checked} beats, wrote {len(exp)}"
    tb.log.info(f"PASS geared host={host_w}b: {n_checked} beats round-tripped "
                f"through the dwidth converters")


# ---------------------------------------------------------------------------
import pytest  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "dv/tb/pumice_top_geared_tb_top.f")


# host widths: 64 = down-gear (2:1), 128 = GEAR-1 (converters bypassed),
# 256 = up-gear (1:2). All map to one DW=128 DRAM burst.
def _run_geared(request, host_w, extra=None):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_top_geared_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    os.makedirs(log_dir, exist_ok=True)
    params = {"HOST_AXI_DATA_WIDTH": str(host_w), "AXI_ID_WIDTH": "8",
              "AXI_ADDR_WIDTH": "32", "NUM_RANKS": "1", "NUM_BANKS": str(NUM_BANKS),
              "ROW_WIDTH": str(ROW_WIDTH), "COL_WIDTH": str(COL_WIDTH),
              "DFI_RATE": str(DFI_RATE), "DRAM_BEAT_WIDTH": str(DRAM_BEAT),
              "BL": str(BL), "NUM_ENTRIES": "8", "N_SRAM_SLOTS": "8"}
    # Distinct sim_build per burst length: same RTL params, but PUMICE-010
    # says one sim_build per process only.
    _bb = (extra or {}).get("GEARED_BURST_BEATS", "full")
    sim_build = sim_build_path(tests_dir, f"geared_h{host_w}_b{_bb}")
    # PUMICE-010: echo the seed so a one-off red is reproducible.
    def _seed_echo(hw):
        sd = os.environ.get("PUMICE_SEED", str(random.randint(0, 100000)))
        print(f"[seed] geared_h{hw} PUMICE_SEED={sd}")
        return sd
    os.makedirs(sim_build, exist_ok=True)
    env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
           "COCOTB_LOG_LEVEL": "INFO",
           "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
           "SEED": _seed_echo(host_w),
           "HOST_AXI_DATA_WIDTH": str(host_w)}
    env.update(params)
    if extra:
        env.update(extra)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_top_geared",
        sim_build=sim_build, simulator="verilator", extra_env=env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--public-flat-rw", "-Wno-MULTIDRIVEN",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=False, keep_files=True, timescale="1ns/1ps")


# host widths: 64 = down-gear (2:1), 128 = GEAR-1 (converters bypassed),
# 256 = up-gear (1:2). All map to one DW=128 DRAM burst.
@pytest.mark.parametrize("host_w", [64, 128, 256])
def test_pumice_top_geared(request, host_w):
    _run_geared(request, host_w)

# The ddr2-char harness runs host_w=64 with AxLEN=0 -- ONE 64-bit host beat
# against a DRAM burst that is (BL*DRAM_BEAT)/64 = 8 host beats wide. Nothing
# above covers that: the sweep always issues a whole burst. These do, at the
# harness's exact geometry, so a hang here is a pumice bug and a hang only in
# the harness is a harness bug.
@pytest.mark.parametrize("beats", [1, 2, 4])
def test_pumice_top_geared_short_burst(request, beats):
    _run_geared(request, host_w=64, extra={"GEARED_BURST_BEATS": str(beats)})
