# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_cxs_top
# Purpose: rapids_cxs_top (byte-granular RAPIDS, CXS network planes) datapath tests (Pattern B)
#
# Documentation: projects/components/dma-ip/rapids/docs/rapids_planes.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2026-10-15

"""
rapids_cxs_top is rapids_top with the network planes swapped for CXS
(rtl/plane/rapids_plane_cxs_{tx,rx}). The core, the CSRs and every scoreboard
are the AXIS top's; RapidsCxsTopTB swaps only the network BFMs. So these
cells re-run the scenarios that cross the network ports -- the rest of the
AXIS suite (status, perf windows, control path, monitors-off build) exercises
logic the plane swap does not touch.

Every cell also requires the link to be clean: no violation in the CXS
transmitter, receiver or either wire monitor, and the DUT's
*_cxs_protocol_error / snk_cxs_unsupported flags low.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_levels import depth as _profile_depth

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_top_tb import RapidsCxsTopTB
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_tb import RapidsCxsTileTB
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_credits_tb import RapidsCxsTileCreditsTB


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

def _beats():
    return _profile_depth('top_beats')


async def _bring_up(dut):
    tb = RapidsCxsTopTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    return tb


def _finish(tb, ok, stats, what):
    tb.finalize_test()
    assert ok, f"{what} failed: {stats.get('errors')}"
    link = tb.cxs_link_errors()
    assert not link, f"{what}: CXS link not clean: {link}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_source_path(dut):
    """SOURCE: memory -> CXS egress (one CXS packet per AXIS TLAST run)."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_source_path(channel=0, beats=_beats())
    _finish(tb, ok, stats, "source path")
    tb.assert_descriptors_fetched()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_sink_path(dut):
    """SINK: CXS ingress -> memory. The sink withholds credits (its FIFO
    fills) until the channel's descriptor is fetched, as the AXIS plane
    withholds tready."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_sink_path(channel=0, beats=_beats())
    _finish(tb, ok, stats, "sink path")
    tb.assert_descriptors_fetched()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_source_bytes(dut):
    """SOURCE, byte-granular: unaligned address, odd length -- the partial
    last beat's TSTRB must survive the trip through CXSUSER."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_source_bytes(channel=1, offset=5, nbytes=77)
    _finish(tb, ok, stats, "source bytes")
    tb.assert_descriptors_fetched()


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_sink_bytes(dut):
    """SINK, byte-granular: a packed packet with a partial last beat to an
    unaligned address; END0PTR / CXSUSER carry the strobes in."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_sink_bytes(channel=2, offset=9, nbytes=77)
    _finish(tb, ok, stats, "sink bytes")
    tb.assert_descriptors_fetched()


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_source_concurrent(dut):
    """Four source channels at once: their packets interleave mid-packet on
    the single CXS link (per-stream framing, IHI 0079D 2.5.2)."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_source_concurrent(beats=4 * _beats())
    _finish(tb, ok, stats, "concurrent source")


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_sink_concurrent(dut):
    """Four sink channels at once, their flits interleaved beat by beat."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_sink_concurrent(beats=4 * _beats())
    _finish(tb, ok, stats, "concurrent sink")


@cocotb.test(timeout_time=90, timeout_unit="ms")
async def cocotb_test_cxs_monitors(dut):
    """Both CXS monitor-lites (sink 0x09, source 0x0A) report a PROTOCOL_CXS
    Completion/PACKET_END per CXS packet through the monbus group."""
    tb = await _bring_up(dut)
    ok, stats = await tb.test_cxs_monitors(beats=_beats())
    _finish(tb, ok, stats, "CXS monitor-lites")


@cocotb.test(timeout_time=90, timeout_unit="ms")
async def cocotb_test_ext_addressing(dut):
    """EXT (strided) source descriptor over the CXS egress: the payload of
    every beat is the address it was read from, so the egress proves the walk."""
    tb = await _bring_up(dut)
    channel, inner, rows = 0, 4, 2
    beats = inner * rows
    bpl = tb.DATA_WIDTH // 8
    src_addr = tb.SRC_BASE + channel * tb.CHANNEL_OFFSET
    desc_addr = tb.DESC_BASE + channel * 0x1000
    seq = tb.expected_seq(base=src_addr, s0=bpl, s1=0x1000, inner=inner,
                          length=beats, per_beat=False)
    mask = (1 << (bpl * 8)) - 1
    expected = []
    for run_base, run_beats in seq:
        for i in range(run_beats):
            a = run_base + i * bpl
            tb.preload_source(a, [a & mask])
            expected.append(a & mask)
    chunk0 = tb.create_descriptor(src_addr, 0, beats, channel_id=channel,
                                  desc_type=tb.DESC_TYPE_EXT)
    chunk1 = tb.build_ext_chunk1(rd=dict(s0=bpl, s1=0x1000, inner=inner, w0=0, w1=0),
                                 wr=dict(s0=bpl, s1=0, inner=inner, w0=0, w1=0))
    tb.register_ext_descriptor(tb.desc_src_mem, desc_addr, chunk0, chunk1)
    await tb.kick_off_channel('src', channel, desc_addr)
    idle = await tb.wait_half_idle('src', timeout_cycles=20000)
    for _ in range(8000):
        await tb.wait_clocks(tb.clk_name, 1)
        if len(tb.captured_axis.get(channel, [])) >= beats:
            break
    await tb.wait_clocks(tb.clk_name, 200)
    got = tb.captured_axis.get(channel, [])
    errors = list(tb.test_errors)
    if not idle:
        errors.append("src half did not return to idle")
    if got != expected:
        errors.append(f"egress {[hex(v) for v in got[:12]]} != expected {[hex(v) for v in expected[:12]]}")
    _finish(tb, not errors, {'errors': errors}, "extended addressing")
    tb.assert_descriptors_fetched()


# ===========================================================================
# TILE HEADER (TILE_HDR = 1): TILE_SPEC 11.5 header on both ports, 11.11
# cell-issued descriptors. The cells build the top with TILE_HDR = 1.
# ===========================================================================

async def _bring_up_tile(dut):
    tb = RapidsCxsTileTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    return tb


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_source_write(dut):
    """A source descriptor's ptype / op / coordinate / target become its
    packet's header beat, ahead of the payload."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_source_write(channel=0, beats=_beats())
    _finish(tb, ok, stats, "tile source write")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_source_read(dut):
    """op = 1: a header-only read request, and no source-memory read."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_source_read(channel=3, nbytes=200)
    _finish(tb, ok, stats, "tile read request")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_sink_write(dut):
    """A cell's mem write: header stripped, payload to memory."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_sink_write(channel=2, beats=_beats())
    _finish(tb, ok, stats, "tile sink write")


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_tile_cell_descriptors(dut):
    """Cell-issued descriptors on four source channels: idle, busy, and one
    chaining into memory; each packet reaches the coordinate it names."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_cell_descriptors(beats=_beats())
    _finish(tb, ok, stats, "cell-issued descriptors")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_desc_overflow(dut):
    """A desc packet with no free slot is dropped and flagged; the running
    transfer and the queued descriptors complete, and nothing stalls."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_cell_descriptor_overflow(channel=5)
    _finish(tb, ok, stats, "descriptor overflow")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_source_bad_ptype(dut):
    """A source descriptor with ptype credit is refused, not sent."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_source_bad_ptype(channel=6)
    _finish(tb, ok, stats, "source ptype refusal")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_unsupported(dut):
    """Credit packets are consumed and counted, a read request to RAPIDS is
    consumed and flagged, and the stream still carries data afterwards."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_unsupported(channel=4)
    _finish(tb, ok, stats, "credit / unsupported")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_all_channels_concurrent(dut):
    """Every channel of the build at once, both halves: one KICK_ENABLE write
    launches all of them (16 on rapids_16ch_cxs_top)."""
    tb = await _bring_up(dut)
    chans = tuple(range(tb.NUM_CHANNELS))
    ok_s, st_s = await tb.test_source_concurrent(channels=chans, beats=4 * _beats())
    ok_k, st_k = await tb.test_sink_concurrent(channels=chans, beats=4 * _beats())
    _finish(tb, ok_s and ok_k, {'errors': st_s['errors'] + st_k['errors']}, "all channels concurrent")


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_tile_high_channel_descriptors(dut):
    """Cell-issued descriptors on the build's top channels (tag 15 on 16)."""
    tb = await _bring_up_tile(dut)
    ok, stats = await tb.test_cell_descriptors(beats=_beats(), base_channel=tb.NUM_CHANNELS - 4)
    _finish(tb, ok, stats, "high-channel cell descriptors")


# ===========================================================================
# END-TO-END TILE CREDITS (TILE_HDR = 1, TILE_CREDITS = 1): TILE_SPEC 11.9 /
# 11.10. Every scenario boots its own build: the window counts from reset.
# ===========================================================================

async def _bring_up_credits(dut):
    tb = RapidsCxsTileCreditsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    return tb


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_credit_window(dut):
    """The advertisement window: legal mask, late and zero advertisements,
    and a descriptor held until the window closes."""
    tb = await _bring_up_credits(dut)
    ok, stats = await tb.test_window()
    _finish(tb, ok, stats, "advertisement window")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_credit_no_oversend(dut):
    """A destination is never sent more flits than it advertised and returned."""
    tb = await _bring_up_credits(dut)
    ok, stats = await tb.test_no_oversend(beats=_beats())
    _finish(tb, ok, stats, "no oversend")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_credit_shared_counter(dut):
    """Two channels writing one cell share its counter."""
    tb = await _bring_up_credits(dut)
    ok, stats = await tb.test_shared_counter()
    _finish(tb, ok, stats, "shared counter")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_credit_node(dut):
    """A node's counter covers what is addressed to it; a read is one flit."""
    tb = await _bring_up_credits(dut)
    ok, stats = await tb.test_node_destination()
    _finish(tb, ok, stats, "node destination")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_tile_credit_illegal(dut):
    """A descriptor to an illegal destination is refused."""
    tb = await _bring_up_credits(dut)
    ok, stats = await tb.test_illegal_refused()
    _finish(tb, ok, stats, "illegal destinations")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_top(testcase, test_name, extra_params=None, test_level='gate', dut='rapids_cxs_top', nch=8):
    """Compile rapids_cxs_top and run one testcase (13-bit APB, as the AXIS top)."""
    test_name = f"{test_name}_{test_level}"
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top': '../../rtl/top',
    })
    dut_name = dut   # rapids_{8,16}ch_*top builds pick their register map by filelist

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/dma-ip/rapids/rtl/filelists/top/{dut_name}.f'
    )

    # RTL overrides go into test_name before any path: sim_build is keyed on it.
    if extra_params:
        test_name = f"{test_name}_" + "_".join(
            f"{k.lower()}{v}" for k, v in sorted(extra_params.items()))
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': nch,
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
        'APB_ADDR_WIDTH': 13,
        'APB_DATA_WIDTH': 32,
    }
    if extra_params:
        rtl_parameters.update(extra_params)

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        'TEST_NUM_CHANNELS': str(nch),
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': '512',
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': '13',
        'TEST_APB_DATA_WIDTH': '32',
        # The BFMs must build the same link as the top: CXS_MAX_CREDIT
        # (top default 32) unless the cell overrides it
        'TEST_CXS_MAX_CREDIT': str(rtl_parameters.get('CXS_MAX_CREDIT', 32)),
    }

    compile_args = [
        "-Wno-fatal",  # generated rapids_regs.sv trips MULTIDRIVEN/UNOPT; keep warnings non-fatal
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/dma-ip/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_source(request, test_level):
    """SOURCE datapath over the CXS egress plane."""
    _run_top("cocotb_test_source_path", "test_rapids_cxs_top_source", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_sink(request, test_level):
    """SINK datapath over the CXS ingress plane."""
    _run_top("cocotb_test_sink_path", "test_rapids_cxs_top_sink", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_source_bytes(request, test_level):
    """SOURCE byte-granular: TSTRB through CXSUSER."""
    _run_top("cocotb_test_source_bytes", "test_rapids_cxs_top_source_bytes", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_sink_bytes(request, test_level):
    """SINK byte-granular: partial last beat over CXS."""
    _run_top("cocotb_test_sink_bytes", "test_rapids_cxs_top_sink_bytes", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_cxs_mon(request, test_level):
    """CXS monitor-lites report through the monbus group."""
    _run_top("cocotb_test_cxs_monitors", "test_rapids_cxs_top_cxs_mon", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_ext_addressing(request, test_level):
    """EXT addressing over the CXS egress (USE_ROW_COL_MAJOR_ADDRESSING=1)."""
    _run_top("cocotb_test_ext_addressing", "test_rapids_cxs_top_ext_addressing", extra_params={'USE_ROW_COL_MAJOR_ADDRESSING': 1}, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_source_concurrent(request, test_level):
    """Concurrent source channels interleaved on the one CXS link."""
    _run_top("cocotb_test_source_concurrent", "test_rapids_cxs_top_source_concurrent", test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_sink_concurrent(request, test_level):
    """Concurrent sink channels interleaved on the one CXS link."""
    _run_top("cocotb_test_sink_concurrent", "test_rapids_cxs_top_sink_concurrent", test_level=test_level)


# ---- TILE_HDR = 1 cells ---------------------------------------------------
_TILE = {'TILE_HDR': 1}


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_source_write(request, test_level):
    """Tile header on the source port, built from the descriptor."""
    _run_top("cocotb_test_tile_source_write", "test_rapids_cxs_top_tile_source_write",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_source_read(request, test_level):
    """Header-only read request (op = 1)."""
    _run_top("cocotb_test_tile_source_read", "test_rapids_cxs_top_tile_source_read",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_sink_write(request, test_level):
    """Tile header stripped on the sink port."""
    _run_top("cocotb_test_tile_sink_write", "test_rapids_cxs_top_tile_sink_write",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_cell_descriptors(request, test_level):
    """Cell-issued descriptors into the source channels' queues."""
    _run_top("cocotb_test_tile_cell_descriptors", "test_rapids_cxs_top_tile_cell_descriptors",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_desc_overflow(request, test_level):
    """Dropped cell-issued descriptor with no free slot."""
    _run_top("cocotb_test_tile_desc_overflow", "test_rapids_cxs_top_tile_desc_overflow",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_unsupported(request, test_level):
    """Credit and unsupported packets never stall the sink port."""
    _run_top("cocotb_test_tile_unsupported", "test_rapids_cxs_top_tile_unsupported",
             extra_params=_TILE, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_source_bad_ptype(request, test_level):
    """A source descriptor with ptype credit is refused."""
    _run_top("cocotb_test_tile_source_bad_ptype", "test_rapids_cxs_top_tile_source_bad_ptype",
             extra_params=_TILE, test_level=test_level)


# ---- TILE_CREDITS = 1 cells --------------------------------------------------
_CREDITS = {'TILE_HDR': 1, 'TILE_CREDITS': 1}


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("scenario", ["window", "no_oversend", "shared_counter", "node", "illegal"])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_cxs_top_tile_credits(request, scenario, test_level):
    """End-to-end tile credits and the legal-destination mask (TILE_SPEC 11.9 / 11.10)."""
    _run_top(f"cocotb_test_tile_credit_{scenario}", f"test_rapids_cxs_top_tile_credit_{scenario}",
             extra_params=_CREDITS, test_level=test_level)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_16ch_cxs_top_tile_credits(request, test_level):
    """The 16-channel map carries the same credit registers and counters."""
    _run_top("cocotb_test_tile_credit_shared_counter", "test_rapids_16ch_cxs_top_tile_credit_shared",
             extra_params=_CREDITS, test_level=test_level, dut="rapids_16ch_cxs_top", nch=16)


# ---- 16-channel CXS top ----------------------------------------------------
@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("nch", [8, 16])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_nch_cxs_top_all_channels(request, nch, test_level):
    """Every channel at once (8 or 16), both halves, one link each way."""
    _run_top("cocotb_test_all_channels_concurrent", f"test_rapids_{nch}ch_cxs_top_all_channels",
             test_level=test_level, dut=f"rapids_{nch}ch_cxs_top", nch=nch)


@pytest.mark.top
@pytest.mark.rapids_cxs_top
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_16ch_cxs_top_tile_high_channels(request, test_level):
    """Tile header + cell-issued descriptors on channels 12..15."""
    _run_top("cocotb_test_tile_high_channel_descriptors", "test_rapids_16ch_cxs_top_tile_high_channels",
             extra_params=_TILE, test_level=test_level, dut="rapids_16ch_cxs_top", nch=16)
