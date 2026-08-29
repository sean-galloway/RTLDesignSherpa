# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Pattern-B runner for `pumice_wr_splitter` (write-side burst splitter).

Directly exercises the AxLEN -> DRAM-burst mapping — the "one AXI burst maps to
an integer number of DRAM bursts" contract that was previously untested. The
splitter chops the host AW into CHUNK_BEATS-sized sub-commands (CHUNK_BEATS =
AXI beats per DRAM burst) and re-frames WLAST every CHUNK_BEATS beats.

  cocotb_test_wr_splitter_single  - AxLEN == CHUNK_BEATS-1  -> ONE sub-command,
                                    agg=0, last=1, one re-framed WLAST.
  cocotb_test_wr_splitter_split   - AxLEN == 2*CHUNK_BEATS-1 -> TWO sub-commands
                                    of CHUNK_BEATS, agg=1 on both, last only on
                                    the 2nd; WLAST re-framed every CHUNK_BEATS.
  cocotb_test_wr_splitter_ragged  - AxLEN not a multiple of CHUNK_BEATS -> a full
                                    sub-command + a RAGGED tail sub-command
                                    (< CHUNK_BEATS); the tail's WLAST is the
                                    host's own final beat. (The tail then SLVERRs
                                    at pumice_wr_intake — see that test.)
"""

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer   # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_wr_splitter.f")

CHUNK_BEATS = 4          # AXI beats per DRAM burst (must match the param below)


async def _reset(dut):
    """Reset, and build the BFMs that own both sides (PUMICE-014).

    `fub_aw`/`fub_w` are AXI-SHAPED but this fub carries NO B channel -- one
    B per ORIGINAL burst is emitted downstream by pumice_wr_data_cam
    (`commit_done_valid_o` gated on agg && last) and driven onto the bus by
    pumice_wr_intake. So the AXI4 write master, which needs a B channel to
    complete a transaction, cannot bind here; these are driven as plain
    valid/ready ports by GAXI producers.

    `m_aw`/`m_w` are the DUT's master outputs -> GAXI consumers own their
    readys at ready_policy='always', which is exactly what the old hardwired
    `m_awready=1` / `m_wready=1` modelled.
    """
    dut.aresetn.value = 0
    aw_src = fub_producer(
        dut, "fub_aw", dut.aclk, log=dut._log,
        valid="fub_awvalid", ready="fub_awready",
        fields={'id':    ("fub_awid", 8),
                'addr':  ("fub_awaddr", 32),
                'len':   ("fub_awlen", 8),
                'size':  ("fub_awsize", 3),
                'burst': ("fub_awburst", 2)})
    w_src = fub_producer(
        dut, "fub_w", dut.aclk, log=dut._log,
        valid="fub_wvalid", ready="fub_wready",
        fields={'data': ("fub_wdata", 64),
                'strb': ("fub_wstrb", 8),
                'last': ("fub_wlast", 1)})
    aw_sink = fub_consumer(
        dut, "m_aw", dut.aclk, log=dut._log,
        valid="m_awvalid", ready="m_awready",
        fields={'len':  ("m_awlen", 8),
                'agg':  ("m_aw_agg", 1),
                'last': ("m_aw_last", 1)})
    w_sink = fub_consumer(
        dut, "m_w", dut.aclk, log=dut._log,
        valid="m_wvalid", ready="m_wready",
        fields={'last': ("m_wlast", 1)})
    for _ in range(5):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)
    return aw_src, w_src, aw_sink, w_sink


async def _drive_burst(aw_src, w_src, awlen):
    """One AW plus its W beats, through the GAXI producers.

    QUEUE-AND-GO (`_driver_send`) rather than blocking `send()`: the old code
    ran _drive_aw concurrently with _drive_w because the splitter accepts the
    two independently, and awaiting each packet would serialise them and
    insert gaps between W beats.
    """
    await aw_src._driver_send(aw_src.create_packet(
        id=3, addr=0x1000, len=awlen, size=3, burst=1))
    n = awlen + 1
    for i in range(n):
        await w_src._driver_send(w_src.create_packet(
            data=0xA0 + i, strb=0xFF, last=1 if i == n - 1 else 0))


async def _collect(dut, aw_sink, w_sink, n_subs_expected, n_wbeats_expected):
    """Run one burst; collect sub-commands (awlen, agg, last) + W-beat WLASTs."""
    subs = []
    wlasts = []

    # Both sinks are GAXI consumers -- reshape what they captured rather
    # than re-sampling the bus.
    async def mon_aw():
        while len(subs) < n_subs_expected:
            await RisingEdge(dut.aclk)
            while aw_sink._recvQ:
                q = aw_sink._recvQ.popleft()
                subs.append((q.len, q.agg, q.last))

    async def mon_w():
        while len(wlasts) < n_wbeats_expected:
            await RisingEdge(dut.aclk)
            while w_sink._recvQ:
                wlasts.append(w_sink._recvQ.popleft().last)

    cocotb.start_soon(mon_aw())
    cocotb.start_soon(mon_w())
    return subs, wlasts


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_single(dut):
    """AxLEN = CHUNK_BEATS-1 -> exactly one DRAM burst, no split."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    aw_src, w_src, aw_sink, w_sink = await _reset(dut)
    nbeats = CHUNK_BEATS
    subs, wlasts = await _collect(dut, aw_sink, w_sink, 1, nbeats)
    await _drive_burst(aw_src, w_src, nbeats - 1)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 1, f"expected 1 sub-command, got {subs}"
    awlen, agg, last = subs[0]
    assert awlen == CHUNK_BEATS - 1, f"sub awlen {awlen} != {CHUNK_BEATS-1}"
    assert agg == 0, "single (unsplit) burst must NOT set agg"
    assert last == 1, "single burst must set last"
    assert wlasts.count(1) == 1 and wlasts[-1] == 1, \
        f"exactly one WLAST at the end, got {wlasts}"
    dut._log.info("PASS: AxLEN=%d -> 1 DRAM burst (no split)", nbeats - 1)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_split(dut):
    """AxLEN = 2*CHUNK_BEATS-1 -> two DRAM bursts (integer multiple split)."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    aw_src, w_src, aw_sink, w_sink = await _reset(dut)
    nbeats = 2 * CHUNK_BEATS
    subs, wlasts = await _collect(dut, aw_sink, w_sink, 2, nbeats)
    await _drive_burst(aw_src, w_src, nbeats - 1)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 2, f"expected 2 sub-commands, got {subs}"
    for i, (awlen, agg, last) in enumerate(subs):
        assert awlen == CHUNK_BEATS - 1, f"sub{i} awlen {awlen} != {CHUNK_BEATS-1}"
        assert agg == 1, f"sub{i} of a split must set agg"
        assert last == (1 if i == 1 else 0), f"sub{i} last wrong: {last}"
    # WLAST re-framed every CHUNK_BEATS: at beat CHUNK_BEATS-1 and 2*CHUNK_BEATS-1
    want = [1 if (j + 1) % CHUNK_BEATS == 0 else 0 for j in range(nbeats)]
    assert wlasts == want, f"WLAST re-framing {wlasts} != {want}"
    dut._log.info("PASS: AxLEN=%d -> 2 DRAM bursts (split)", nbeats - 1)


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_wr_splitter_ragged(dut):
    """AxLEN not a multiple of CHUNK_BEATS -> full sub + ragged tail sub."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    aw_src, w_src, aw_sink, w_sink = await _reset(dut)
    nbeats = CHUNK_BEATS + 2          # 6: one full (4) + ragged tail (2)
    subs, wlasts = await _collect(dut, aw_sink, w_sink, 2, nbeats)
    await _drive_burst(aw_src, w_src, nbeats - 1)
    for _ in range(20):
        await RisingEdge(dut.aclk)
    assert len(subs) == 2, f"expected 2 sub-commands (full+ragged), got {subs}"
    assert subs[0][0] == CHUNK_BEATS - 1, f"full sub awlen {subs[0][0]}"
    assert subs[1][0] == (nbeats - CHUNK_BEATS) - 1, \
        f"ragged tail awlen {subs[1][0]} != {(nbeats-CHUNK_BEATS)-1}"
    # tail is SHORTER than CHUNK_BEATS -> intake will SLVERR it (see wr_intake).
    want = [1 if (j + 1) % CHUNK_BEATS == 0 or j == nbeats - 1 else 0
            for j in range(nbeats)]
    assert wlasts == want, f"ragged WLAST {wlasts} != {want}"
    dut._log.info("PASS: AxLEN=%d -> full + ragged tail (intake SLVERRs tail)",
                  nbeats - 1)


# ---------------------------------------------------------------------------
# Pytest wrappers
# ---------------------------------------------------------------------------
def _run(request, testcase):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_wr_splitter"
    test_name = testcase

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "AXI_DATA_WIDTH": "64",
        "AXI_USER_WIDTH": "1", "CHUNK_BEATS": str(CHUNK_BEATS),
    }
    extra_env = {
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    extra_env.update(params)
    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True,
        timescale="1ns/1ps")


def test_pumice_wr_splitter_single(request):
    _run(request, "cocotb_test_wr_splitter_single")


def test_pumice_wr_splitter_split(request):
    _run(request, "cocotb_test_wr_splitter_split")


def test_pumice_wr_splitter_ragged(request):
    _run(request, "cocotb_test_wr_splitter_ragged")
