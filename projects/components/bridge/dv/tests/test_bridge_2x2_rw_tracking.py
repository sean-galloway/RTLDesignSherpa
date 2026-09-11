#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): response-tracking tests on bridge_2x2_rw.
#
# These two tests were first added INSIDE the generated test_bridge_2x2_rw.py
# (c64660f47 for BRIDGE-011, b0cce57ca / 56a916a79 for latency). A generated
# file cannot carry hand-written tests: the next regenerate drops them
# silently, and the file was never regenerated after that for exactly this
# reason. They live here now, beside the generated file for the same DUT,
# and use the same generated TB class.
#
#   outstanding_overflow -- BRIDGE-011: more concurrent writes than the
#       slave's response-tracking FIFO is deep; occupancy must never exceed
#       DEPTH (awready gated on not-full), no B misroutes, every write lands.
#   latency -- the bridge's structural request/response propagation, in
#       cycles, asserted exactly so a moved pipeline stage is caught.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ReadOnly, RisingEdge, ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from projects.components.bridge.dv.tbclasses.bridge2x2_rw_tb import Bridge2x2RwTB


def _hi(sig):
    """True when `sig` reads as 1, False when it is 0 OR UNRESOLVABLE.

    int(sig.value) raises ValueError on an X, and an exception inside a
    cocotb.start_soon watcher kills that watcher SILENTLY -- the test then
    reports "no violations found" when what actually happened is "nothing was
    ever sampled". Outputs read X before the first transaction, so every
    watcher started right after reset hits this.
    """
    try:
        return int(sig.value) == 1
    except ValueError:
        return False




@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_outstanding_overflow(dut):
    """
    BRIDGE-011: offer more concurrent writes to one slave than its
    response-tracking FIFO is deep, and require the bridge to hold the line.

    Each slave adapter records the ORIGINATING MASTER for every accepted AW in
    a fixed-depth FIFO and pops it on the response, routing B by FIFO POSITION.
    Push is unconditional on the AW handshake with no full check, so nothing
    stops the pointer running past the reader:

      * past DEPTH, live entries are overwritten -- a response is routed by a
        stale entry, to the WRONG MASTER;
      * at exactly 2*DEPTH the write pointer LAPS the read pointer, the
        `wr_ptr != rd_ptr` occupancy test reads EMPTY, `bid_valid` drops and
        the response is never routed at all -- the master waits forever.

    The invariant asserted here is the one the fix establishes: occupancy NEVER
    exceeds DEPTH, because awready is gated on the FIFO being not-full. That
    holds on fixed RTL and is violated on broken RTL, so it works in both
    directions -- unlike "occupancy exceeded DEPTH", which only a broken
    bridge can satisfy.

    Two conditions are needed and no other test in this suite has either: TWO
    masters outstanding on ONE slave (a single master's entries are all
    identical, so overwriting them is invisible), and a SLOW slave, since the
    default BFM answers in about a cycle and never builds depth.
    """
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()

    FIFO_DEPTH = 16    # WR_FIFO_DEPTH in ddr_adapter.sv
    # Depth (TEST_LEVEL): concurrent writes per master -- gate 20 (40 total,
    # past both DEPTH and 2*DEPTH), func 40, full 64. The invariant needs
    # more than 2*DEPTH offered in total; every level clears that.
    PER_MASTER = tb.level_cfg['overflow_per_master']
    assert 2 * PER_MASTER > 2 * FIFO_DEPTH, "stimulus cannot reach the lap point"
    B_DELAY    = 2 * PER_MASTER    # cycles; must outlast the issue phase

    tb.log.info("=" * 80)
    tb.log.info(f"BRIDGE-011 (level={tb.level}): {2 * PER_MASTER} concurrent writes to slave 0 "
                f"(tracking FIFO is {FIFO_DEPTH} deep)")
    tb.log.info("=" * 80)

    tb.set_slave_response_delay(0, B_DELAY)

    # Ground truth, straight off the adapter's own pointers. Port-level
    # arithmetic was tried first and disagreed with itself: the FIFO pops on
    # the CROSSBAR-side B, not the slave-port B, so counting handshakes at the
    # slave port measures something else entirely.
    fifo = {'peak': 0, 'probed': False}
    bad_route = []
    b_seen = []

    # ONE probe coroutine for everything sampled per cycle.
    #
    # This started as four concurrent coroutines each awaiting ReadOnly(). That
    # DROPS SAMPLES: the B-channel watchers between them saw 16 of 80
    # responses, and a watcher that misses traffic reports "no misroutes"
    # identically to a clean run. One sampler sees every cycle.
    async def _probe():
        # BRIDGE-015/016: a multi-master bridge's AXI slaves track by ID in
        # bridge_cam, so occupancy is the CAM's count rather than a pointer
        # difference. The invariant is the same either way: it never exceeds
        # DEPTH, because the AW handshake is gated on not-full.
        adapter = tb.dut.u_ddr_adapter
        cam = getattr(adapter, 'u_wr_cam', None)
        if cam is not None:
            def occupancy():
                return int(cam.tags_count.value)
        else:
            wr, rd = adapter.wr_ptr, adapter.rd_ptr
            def occupancy():
                return (int(wr.value) - int(rd.value)) & 0x1F
        fifo['probed'] = True
        ports = ((0, tb.dut.cpu_m_axi_bid, tb.dut.cpu_m_axi_bvalid, tb.dut.cpu_m_axi_bready),
                 (1, tb.dut.dma_m_axi_bid, tb.dut.dma_m_axi_bvalid, tb.dut.dma_m_axi_bready))
        while True:
            await RisingEdge(tb.clock)
            await ReadOnly()
            occ = occupancy()
            if occ > fifo['peak']:
                fifo['peak'] = occ
            for idx, bid, bv, br in ports:
                if _hi(bv) and _hi(br):
                    b_seen.append(idx)
                    got = int(bid.value)
                    if ((got >> 3) & 1) != idx:
                        bad_route.append((idx, got))

    cocotb.start_soon(_probe())

    plan = []
    for m in (0, 1):
        for i in range(PER_MASTER):
            plan.append((m,
                         0x00001000 + (m * 0x400) + (i * 4),
                         0xB0110000 | (m << 12) | i,
                         (m << 3) | (i % 8)))

    done = []

    async def _issue(m, addr, data, txn_id):
        await tb.master_write(m, addr, data, txn_id=txn_id)
        done.append((m, addr, data))

    # Launched before any of them awaits, so the offered load is 80
    # concurrent writes by construction -- no runtime check needed to know
    # the stimulus was strong enough.
    for (m, addr, data, txn_id) in plan:
        cocotb.start_soon(_issue(m, addr, data, txn_id))

    for _ in range(6000):
        if len(done) == len(plan):
            break
        await ClockCycles(tb.clock, 10)

    assert fifo['probed'], "FIFO pointer probe never ran -- test proves nothing"

    tb.log.info(f"peak tracking-FIFO occupancy: {fifo['peak']} "
                f"(depth {FIFO_DEPTH}), completed {len(done)}/{len(plan)}")

    # THE invariant. Gating awready on not-full makes this unconditional.
    assert fifo['peak'] <= FIFO_DEPTH, (
        f"BRIDGE-011: slave 0's tracking FIFO reached {fifo['peak']} entries "
        f"with only {FIFO_DEPTH} slots. Past {FIFO_DEPTH} a live entry is "
        f"overwritten and its response is routed to the wrong master; at "
        f"{2 * FIFO_DEPTH} the pointers lap, occupancy reads EMPTY and the "
        f"response is never routed at all. awready must be gated on not-full.")

    # The BID check is SUPPLEMENTARY and best-effort: a cycle sampler running
    # beside the BFMs does not catch every handshake (measured: roughly a third
    # of them), so "bad_route is empty" is not proof of clean routing. It only
    # ever reports misroutes it actually saw. The occupancy invariant below is
    # the primary detector and does not depend on sampling at all.
    #
    # What IS asserted here: the watcher was alive and sampling. A dead watcher
    # and a clean run are otherwise indistinguishable.
    assert b_seen, (
        "the B-channel watcher never observed a single response, so its "
        "'no misroutes' result carries no information at all")
    tb.log.info(f"BID check sampled {len(b_seen)}/{len(plan)} responses "
                f"(best-effort; the occupancy invariant is the real detector)")

    assert not bad_route, (
        f"BRIDGE-011: {len(bad_route)} response(s) delivered to the wrong "
        f"master -- first, master port {bad_route[0][0]} received BID "
        f"0x{bad_route[0][1]:x}.")

    if len(done) != len(plan):
        per_master = {0: 0, 1: 0}
        for (m, _a, _d) in done:
            per_master[m] += 1
        raise AssertionError(
            f"BRIDGE-011: only {len(done)}/{len(plan)} writes completed "
            f"(master 0: {per_master[0]}/{PER_MASTER}, master 1: "
            f"{per_master[1]}/{PER_MASTER}). A response was dropped or "
            f"consumed by the wrong master.")

    for (m, addr, data, _id) in plan:
        actual = tb.slave_mem_read(0, addr, master_idx=m)
        assert actual == data, (
            f"slave 0 memory mismatch at 0x{addr:08x} (master {m}): "
            f"got 0x{actual:08x}, expected 0x{data:08x}")

    tb.log.info(f"All {len(plan)} writes completed; peak occupancy "
                f"{fifo['peak']} stayed within the {FIFO_DEPTH}-entry FIFO")





@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_latency(dut):
    """Measure request and response latency through the bridge, in cycles.

    The performance chapters quote figures like "2-3 cycles" and describe a
    master-delivery stage as "0 (Direct connection)". Nothing measured them, so
    they drifted from the RTL -- the response path is registered where the
    docs said it was not.

    Measured here at the PORTS, on an idle bridge with a prompt slave, so the
    numbers are the structural pipeline depth and not a queuing artifact:
      request  = master AW accepted -> AW presented at the slave port
      response = slave B accepted   -> B presented at the master port
    """
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_response_delay(0, 1)

    # Depth (TEST_LEVEL): the measurement is repeated `latency_samples` times
    # (gate 1, func 3, full 8) at RNG-chosen addresses in slave 0; every
    # sample must give the same structural figure, which is the point -- a
    # number that moves with the address is a queueing artifact, not depth.
    samples = tb.level_cfg['latency_samples']
    for sample in range(samples):
        await _measure_once(tb, dut, sample, samples)


async def _measure_once(tb, d, sample, samples):
    marks = {}

    # ONE sampler for all four ports. Four concurrent coroutines each awaiting
    # ReadOnly() recorded nothing at all -- a single sampler is both simpler
    # and immune to whatever phase contention that caused.
    async def _sampler():
        n = 0
        ports = (('m_aw', d.cpu_m_axi_awvalid, d.cpu_m_axi_awready),
                 ('s_aw', d.ddr_s_axi_awvalid, d.ddr_s_axi_awready),
                 ('s_b',  d.ddr_s_axi_bvalid,  d.ddr_s_axi_bready),
                 ('m_b',  d.cpu_m_axi_bvalid,  d.cpu_m_axi_bready))
        while True:
            await RisingEdge(tb.clock)
            n += 1
            for name, v, r in ports:
                if _hi(v) and _hi(r):
                    marks.setdefault(name, n)
            # VALID arrival is the bridge's own propagation. ACCEPTANCE also
            # counts however long the far side held READY low, which is the
            # attached slave's behaviour, not the bridge's depth.
            if _hi(d.ddr_s_axi_awvalid):
                marks.setdefault('s_aw_valid', n)
            if _hi(d.cpu_m_axi_bvalid):
                marks.setdefault('m_b_valid', n)

    cocotb.start_soon(_sampler())

    addr = 0x00002000 if sample == 0 else 0x00001000 + tb.rng.randrange(0, 0x2000, 4)
    await tb.master_write(0, addr, 0x1A7E0000 | sample)

    for _ in range(50):
        if {'m_aw', 's_aw', 's_b', 'm_b'} <= marks.keys():
            break
        await ClockCycles(tb.clock, 1)

    missing = {'m_aw', 's_aw', 's_b', 'm_b'} - marks.keys()
    assert not missing, f"never observed handshakes: {sorted(missing)}"

    # PROPAGATION is the bridge's own depth: how long a beat takes to appear
    # on the far side. Accept-to-accept was measured first and was wrong for
    # this purpose -- it also counts however long the far side held READY low,
    # so it moved between runs (4/2 one run, 2/6 the next) and described the
    # BFM's timing as much as the bridge's.
    req = marks['s_aw_valid'] - marks['m_aw']
    rsp = marks['m_b_valid'] - marks['s_b']
    tb.log.info(f"LATENCY sample {sample + 1}/{samples} @0x{addr:08x}: propagation request = {req} cycles")
    if 's_aw_valid' in marks:
        tb.log.info(f"LATENCY propagation request (AW accepted -> AWVALID at slave) = "
                    f"{marks['s_aw_valid'] - marks['m_aw']} cycles")
    if 'm_b_valid' in marks:
        tb.log.info(f"LATENCY propagation response (B accepted -> BVALID at master) = "
                    f"{marks['m_b_valid'] - marks['s_b']} cycles")
    tb.log.info(f"LATENCY propagation response = {rsp} cycles")

    # Both paths are two skid stages, so both are 2. Asserting the exact value
    # (not just >= 1) is what makes this test able to catch a pipeline stage
    # being added or removed, which is the drift the docs suffered from.
    assert req == 2, (
        f"request propagation measured {req} cycles, expected 2 "
        f"(cpu_adapter AW skid -> ddr_adapter AW skid). A change here means a "
        f"pipeline stage moved; update Table 5.7 in the same commit.")
    assert rsp == 2, (
        f"response propagation measured {rsp} cycles, expected 2. The docs "
        f"once described master delivery as '0 (Direct connection)'; it is "
        f"registered.")



# ============================================================================
# Pytest wrappers
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_outstanding_overflow(request, test_level):
    """Pytest wrapper for the BRIDGE-011 outstanding-depth test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_2x2_rw"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_2x2_rw.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_outstanding_overflow_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    # sim_build_path(), not a hand-built join: it honours SIM_BUILD_ROOT so
    # concurrent sessions do not share one build tree, and drops an advisory
    # busy marker so a cleaner can tell "being built in right now" from
    # "leftover". Hand-joining tests_dir/local_sim_build puts every session
    # back in the same directory, which is what f01853fe was written to stop.
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_2x2_rw_outstanding_overflow",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )




@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_latency(request, test_level):
    """Pytest wrapper for the measured-latency test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_2x2_rw"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_2x2_rw.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_latency_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    # sim_build_path(), not a hand-built join: it honours SIM_BUILD_ROOT so
    # concurrent sessions do not share one build tree, and drops an advisory
    # busy marker so a cleaner can tell "being built in right now" from
    # "leftover". Hand-joining tests_dir/local_sim_build puts every session
    # back in the same directory, which is what f01853fe was written to stop.
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_2x2_rw_latency",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
