# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The cocotb dispatcher for stream_harness -- SHARED BY BOTH BUILDS.

There is ONE harness. build-mon and build-perf are that harness at different
parameters, and the cocotb-side behaviour they exercise (ping, descriptor load,
CSR reads, APB config, DMA runs, perf windows) is the SAME code either way --
so it lives at component level next to StreamHarnessTB, not in a build.

Which cases a build actually runs is the build's business, and follows from
USE_AXI_MONITORS:

  build-perf (monitors OFF): ping, desc_load, csr_read, apb_config, dma_*,
      ext_* -- plus the always-on observer bus meters.
  build-mon  (monitors ON):  the above, plus desc_perf / rw_perf / obs_equiv,
      which read IN-CORE monitor windows that only exist when monitors are
      compiled in.

A build's pytest wrapper selects with the TEST_TYPE env var and points cocotb
at this module. It must NOT override USE_AXI_MONITORS: that parameter is the
build's identity, and a test that flips it builds a design no bitstream has.
"""
import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run
# Window-edge tolerance for latency-histogram totals.
#
# The two numbers being compared come from DIFFERENT modules, each with its own
# i_clear/i_freeze window: the burst count from axi_bus_meter (which counts AR/AW
# HANDSHAKES) and the total from axi_perf_latency_hist (which counts COMPLETIONS).
# A transaction straddling either window boundary is therefore counted by one and
# not the other, so exact equality is stricter than the hardware can guarantee.
#
# The skew is ONE EVENT PER BOUNDARY and does not scale with traffic: measured
# 255 vs 256 on a 256-burst run and 4092 vs 4093 on a 4096-burst run. That is why
# this is a small CONSTANT and deliberately NOT a percentage. axi_perf_latency_hist
# has a second, far more serious failure mode -- when its per-channel timestamp
# FIFO is full the push is silently dropped, the completion pops some OTHER
# command's timestamp, and totals undercount while surviving latencies are
# misattributed, with no flag anywhere. That loss DOES scale with traffic, so a
# proportional tolerance would grow to hide exactly the bug this check exists to
# catch. Keep it constant.
HIST_EDGE_TOL = 2


from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# The build directory uses hyphens (`build-perf/`) for consistency with
# shell paths and FPGA tooling conventions, so it is not a valid Python package.
# Inject the AREA's `dv/` into sys.path and import the tbclasses module
# unqualified.
_flow_dv = os.path.join(repo_root, "projects/fpga-systems/Genesys2/stream/dv")
if _flow_dv not in sys.path:
    sys.path.insert(0, _flow_dv)

from tbclasses.stream_harness_tb import StreamHarnessTB


def _built_channels() -> int:
    """How many channels this build actually elaborated.

    Read from the environment (the pytest wrapper passes its NUM_CHANNELS
    generic through extra_env), NOT from a Python constant in some build's test
    file. This dispatcher is shared: build-mon elaborates 4 channels and
    build-perf 8, so a module-level default here would be wrong for one of them
    -- which is exactly what happened when this was `BASE_RTL_PARAMS[...]` and
    the constant lived in the perf wrappers.
    """
    return int(os.environ.get('NUM_CHANNELS', '4'))

# ==========================================================================
# CocoTB test function
# ==========================================================================

# Default 50 ms caps the entire test. Realistic breakdown: UART setup
# ~2.5 ms of sim time, poll window ~500 us, plus margin. Was 2000 ms;
# lowered so a broken DMA surfaces as a cocotb timeout in seconds, not
# minutes. Override via SIM_TIMEOUT_MS env var for deep-chain repro runs
# (16 desc x 2 ch needs ~200 ms sim time at 8 KB / desc).
@cocotb.test(timeout_time=int(os.environ.get('SIM_TIMEOUT_MS', '50')), timeout_unit="ms")
async def cocotb_test_stream_perf(dut):
    """Unified stream characterization test — dispatches on TEST_TYPE."""
    test_type = os.environ.get('TEST_TYPE', 'ping')

    tb = StreamHarnessTB(dut)
    await tb.setup_clocks_and_reset()

    if test_type == 'ping':
        tb.log.info("=== Ping test (UART -> decode -> CSR) ===")
        ok = await tb.run_ping_test()

    elif test_type == 'desc_load':
        tb.log.info("=== Descriptor load test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_descriptor_load_test()

    elif test_type == 'csr_read':
        tb.log.info("=== CSR readback test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_csr_readback_test()

    elif test_type == 'apb_config':
        tb.log.info("=== APB config path test ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_apb_config_test()

    elif test_type.startswith('dma_'):
        # dma_1ch, dma_2ch, ..., dma_8ch -> ACTIVE channel count. The BUILD
        # count is the build's NUM_CHANNELS generic (see _built_channels), so
        # e.g. SIM_NUM_CHANNELS=8 + dma_4ch = 4 active of 8 built (the
        # PARTIAL-population case the FPGA hang needs). DMA_COMPRESS_EN /
        # DMA_MON_ERR_CFG let this path match the FPGA debug-compl +
        # compression run exactly (mon_err_cfg=0 -> bulk-trace via compressor).
        num_ch = int(test_type.split('_')[1].replace('ch', ''))
        desc_per_ch = int(os.environ.get('DMA_DESC_PER_CH', '2'))
        xfer_bytes = int(os.environ.get('DMA_XFER_BYTES', '8192'))
        compress_en = bool(int(os.environ.get('DMA_COMPRESS_EN', '0')))
        # default routing = run_dma_test's default; override to 0 (bulk-trace)
        _merr = os.environ.get('DMA_MON_ERR_CFG')
        mon_err_cfg = int(_merr, 0) if _merr is not None else None
        tb.log.info(f"=== DMA test: {num_ch}ch active x {desc_per_ch}desc x "
                    f"{xfer_bytes}B  (build={_built_channels()}, "
                    f"compress_en={compress_en}, mon_err_cfg={mon_err_cfg}) ===")
        ok = await tb.run_ping_test()
        timeout_clocks = int(os.environ.get('DMA_TIMEOUT_CLOCKS', '50000'))

        # A plain DMA config -- no monitor instrumentation requested -- is
        # EXACTLY what the board runs, so run the board's program: the shared
        # CharacterizationRunner over the shared bridge. Reserve the tb's own
        # orchestration (run_dma_test) for the monitor-validation knobs the
        # runner has no notion of. Reimplementing the plain case is what let
        # sim and silicon diverge without either side reporting it.
        wants_mon_instrumentation = compress_en or (mon_err_cfg is not None)

        if not wants_mon_instrumentation:
            res = await tb.run_dma_via_runner(
                num_channels=num_ch,
                descriptors_per_channel=desc_per_ch,
                transfer_bytes=xfer_bytes,
            )
            ok &= bool(res.get('pass'))   # key is 'pass' (characterization.py)
        else:
            kw = dict(
                num_channels=num_ch,
                descriptors_per_channel=desc_per_ch,
                transfer_bytes=xfer_bytes,
                timeout_clocks=timeout_clocks,
                compress_en=compress_en,
            )
            if mon_err_cfg is not None:
                kw['mon_err_cfg'] = mon_err_cfg
            ok &= await tb.run_dma_test(**kw)

    elif test_type == 'desc_perf':
        # RFC Stage E: open the descriptor-monitor perf window, run a DMA
        # workload (which fetches descriptors over the monitored bus), close
        # the window, and verify the perf CSRs counted real traffic and the
        # four buckets sum to window_cycles.
        tb.log.info("=== Descriptor-monitor perf-window test (RFC Stage E) ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_dma_test(
            num_channels=1,
            descriptors_per_channel=4,
            transfer_bytes=4096,
            measure_desc_perf=True,
        )
        perf = getattr(tb, '_desc_perf', None)
        assert perf is not None, "desc_perf snapshot missing"
        # WINDOW_CYCLES is a LIVE counter that the monitor zeroes when the
        # window closes (it is sampled at close for the legacy WIN_END packet,
        # not meant for post-close polling). The four buckets, by contrast,
        # HOLD their values after close -- so bucket_total is the authoritative
        # closed-window length for the CSR route. Verify the window actually
        # opened and counted real descriptor-fetch traffic.
        assert perf['win_active'] == 0, f"window did not close: {perf}"
        assert perf['bucket_total'] > 0, f"perf window never opened/counted: {perf}"
        assert perf['bursts'] > 0, f"no descriptor AR bursts counted: {perf}"
        assert perf['beats'] > 0, f"no descriptor R beats counted: {perf}"
        assert perf['productive'] > 0, f"no productive cycles counted: {perf}"
        assert perf['beats'] == perf['productive'], \
            f"beats != productive (beat_count = prod_cycles): {perf}"
        assert perf['bytes'] > 0, f"no bytes counted: {perf}"
        tb.log.info(f"Desc-monitor perf window verified: {perf}")

    elif test_type == 'rw_perf':
        # RFC Stage E option 2: open the data-read and data-write datapath perf
        # windows, run a DMA workload (which moves data over the monitored R/W
        # buses), close the windows, and verify the in-core monitor CSRs counted
        # real traffic -- aggregate buckets/counts (E.1), per-channel buckets
        # (E.2), and latency histograms (E.3). The legacy harness axi_bus_meter
        # this route replaces was retired in E.4.
        tb.log.info("=== RD/WR datapath perf-window test (RFC Stage E option 2) ===")
        ok = await tb.run_ping_test()
        # Match the FPGA characterization's first config exactly: 1 channel,
        # 1 descriptor of 64 KB (the pattern where scheduler_idle lingered
        # ~1000x past the data transfer on the board).
        ok &= await tb.run_dma_test(
            num_channels=1,
            descriptors_per_channel=1,
            transfer_bytes=65536,
            timeout_clocks=200_000,
            measure_rw_perf=True,
        )
        rd = getattr(tb, '_rd_perf', None)
        wr = getattr(tb, '_wr_perf', None)
        assert rd is not None and wr is not None, "rw_perf snapshots missing"
        # Per-monitor invariants. WINDOW_CYCLES is live-only (zeroed at close),
        # so bucket_total is the authoritative closed-window length; beats equals
        # productive cycles by construction (beat_count = prod_cycles).
        for name, perf in (('RDMON', rd), ('WRMON', wr)):
            assert perf['win_active'] == 0, f"{name} window did not close: {perf}"
            assert perf['bucket_total'] > 0, f"{name} window never opened/counted: {perf}"
            assert perf['bursts'] > 0, f"{name} no AR/AW bursts counted: {perf}"
            assert perf['beats'] > 0, f"{name} no data beats counted: {perf}"
            assert perf['productive'] > 0, f"{name} no productive cycles: {perf}"
            assert perf['beats'] == perf['productive'], \
                f"{name} beats != productive (beat_count = prod_cycles): {perf}"
            assert perf['bytes'] > 0, f"{name} no bytes counted: {perf}"
        # HARDWARE close: the window must auto-close when the datapath goes idle,
        # NOT wait for software to clear RUN. The TB idled 2000 cycles with RUN
        # still high before checking; WIN_ACTIVE must already be 0 (otherwise the
        # post-transfer idle inflates the buckets -- the bug seen on the board).
        rd_win = getattr(tb, '_rd_win_preclose', 1)
        wr_win = getattr(tb, '_wr_win_preclose', 1)
        assert rd_win == 0, ("RD window did NOT auto-close in hardware (still "
                             "active after 2000-cyc idle with RUN high) -- the "
                             "window would be contaminated by post-transfer idle")
        assert wr_win == 0, ("WR window did NOT auto-close in hardware (still "
                             "active after 2000-cyc idle with RUN high)")
        tb.log.info(f"RD/WR datapath perf windows verified (hardware-closed): "
                    f"rd={rd} wr={wr}")

        # Bubble budget: decompose each window into prod/bp/starv/idle as a
        # percent of bucket_total so the residual (100% - productive) is
        # attributed. RD starvation = read-latency / outstanding-depth (or the
        # modeled memory read latency); RD backpressure = SRAM full (write side
        # draining too slow). WR starvation = SRAM empty (read side feeding too
        # slow); WR backpressure = memory write / B-channel congestion.
        for name, perf in (('RDMON', rd), ('WRMON', wr)):
            tot = perf['bucket_total'] or 1
            pct = lambda k: 100.0 * perf[k] / tot
            tb.log.info(
                f"  {name} bubble budget (of {tot} cyc): "
                f"productive={perf['productive']} ({pct('productive'):.2f}%) "
                f"starv={perf['starvation']} ({pct('starvation'):.2f}%) "
                f"bp={perf['backpressure']} ({pct('backpressure'):.2f}%) "
                f"idle={perf['idle']} ({pct('idle'):.2f}%)")

        # RFC Stage C: per-channel buckets (in-core axi_bus_meter). The legacy
        # harness axi_bus_meter has been retired (RFC Stage E.4) -- its job, as
        # the equivalence oracle for the in-core meter, was proven in the Stage
        # E.1/E.2 bring-up. Going forward the in-core meter is the source of
        # truth, cross-checked here against the aggregate monitor: attributed
        # per-channel productive cannot exceed the aggregate productive, and
        # (read bus, where every beat carries a valid rid) per-channel sum equals
        # the aggregate. On the write bus the engine's active-channel sideband
        # does not cover every productive W beat (burst boundaries), so the sum
        # is <= aggregate; we log the (expected) shortfall.
        rd_ch = getattr(tb, '_rd_ch', None)
        wr_ch = getattr(tb, '_wr_ch', None)
        assert rd_ch and wr_ch, "per-channel snapshots missing"
        for bus, ch_list, agg in (('RD', rd_ch, rd['productive']),
                                  ('WR', wr_ch, wr['productive'])):
            prod_sum = sum(c['prod'] for c in ch_list)
            tb.log.info(f"  {bus} per-channel buckets={ch_list} "
                        f"prod_sum={prod_sum} vs aggregate={agg}")
            tol = max(4, agg // 100)
            assert prod_sum <= agg + tol, \
                (f"{bus} per-channel prod sum {prod_sum} exceeds aggregate {agg}")
            if bus == 'RD':
                assert abs(prod_sum - agg) <= tol, \
                    (f"RD per-channel prod sum {prod_sum} != aggregate {agg} "
                     f"(every read beat carries a valid rid)")
            elif prod_sum < agg - tol:
                tb.log.info(f"  {bus} {agg - prod_sum} productive cycles "
                            f"unattributed (channel_valid low -- expected on W bus)")
        tb.log.info("Per-channel buckets verified (in-core meter self-consistent "
                    "with aggregate)")

        # RFC Stage D: latency histograms. Each metric's total must equal the
        # corresponding burst/transaction count (every read burst contributes
        # one AR->firstR and one AR->RLAST sample; every write burst one AW->B),
        # the histogram bins must sum to that total, and the latency must land in
        # a plausible (non-zero) bin -- a real fetch cannot complete in 0 cycles.
        rd_firstr = getattr(tb, '_rd_hist_firstr', None)
        rd_rlast = getattr(tb, '_rd_hist_rlast', None)
        wr_b = getattr(tb, '_wr_hist_b', None)
        assert rd_firstr and rd_rlast and wr_b, "latency histogram snapshots missing"
        for name, hist, bursts in (('RD AR->firstR', rd_firstr, rd['bursts']),
                                   ('RD AR->RLAST', rd_rlast, rd['bursts']),
                                   ('WR AW->B', wr_b, wr['bursts'])):
            bin_sum = sum(hist['bins'])
            assert abs(hist['total'] - bursts) <= HIST_EDGE_TOL, \
                (f"{name} histogram total {hist['total']} vs burst count {bursts} "
                 f"differs by more than the {HIST_EDGE_TOL}-sample window-edge "
                 f"tolerance -- that is a real loss, not a boundary effect")
            assert bin_sum == hist['total'], \
                (f"{name} histogram bins sum {bin_sum} != total {hist['total']}")
            # Highest populated bin -> a coarse latency sanity check.
            hi_bin = max((b for b, c in enumerate(hist['bins']) if c > 0),
                         default=-1)
            assert hi_bin >= 1, \
                (f"{name} all latency in bin {hi_bin} (<2 cycles) -- implausible: "
                 f"{hist['bins']}")
            tb.log.info(f"  {name}: total={hist['total']} matches bursts={bursts}, "
                        f"highest bin={hi_bin} (~{1 << hi_bin}-{(1 << (hi_bin + 1)) - 1} cyc)")
        tb.log.info("Latency histograms verified (totals == burst counts, bins "
                    "sum to total, plausible bin placement)")

    elif test_type == 'obs_equiv':
        # Observer-vs-in-core equivalence (the "route STREAM through the external
        # axi4_dma_observer" validation). The observer is instantiated INLINE in
        # the harness, in parallel with the in-core monitors (USE_AXI_MONITORS=1).
        # Run a big multi-channel / multi-descriptor workload over lots of cycles,
        # then diff the observer's meter + histogram registers against the in-core
        # RDMON/WRMON perf CSRs. Equal => the observer measures STREAM equivalently
        # => confidence to later ship USE_AXI_MONITORS=0 and measure externally.
        tb.log.info("=== Observer vs in-core equivalence (RFC Stage E) ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_dma_test(
            # WORKLOAD SCALE. The full 1 MB (4ch x 4desc x 64KB) needs ~50 ms
            # of sim and ~25 min of wall clock, which is far past the point of
            # diminishing returns for an equivalence check -- the observer and
            # the in-core monitors either agree or they do not, and they do so
            # within a few thousand bursts. OBS_EQUIV_SCALE shrinks the
            # transfer so a run lands in 10-20 ms; set it to 1 for the full
            # soak. The channel and descriptor COUNTS are held, because the
            # multi-channel interleave is what the comparison is about.
            num_channels=4,
            descriptors_per_channel=4,
            transfer_bytes=65536 // int(os.environ.get('OBS_EQUIV_SCALE', '8')),
            timeout_clocks=600_000,
            measure_rw_perf=True,      # opens/closes in-core window, reads RDMON/WRMON + hists
        )
        assert ok, "obs_equiv: DMA workload failed"
        rd = getattr(tb, '_rd_perf', None)
        wr = getattr(tb, '_wr_perf', None)
        rd_hf = getattr(tb, '_rd_hist_firstr', None)
        rd_hl = getattr(tb, '_rd_hist_rlast', None)
        wr_hb = getattr(tb, '_wr_hist_b', None)
        assert rd and wr and rd_hf and rd_hl and wr_hb, "obs_equiv: in-core snapshots missing"

        # Read the observer entirely over CSR (the host path), no hierarchy probe.
        obs = await tb._read_observer_perf()
        tb.log.info(f"  in-core RD prod={rd['productive']} WR prod={wr['productive']}")
        tb.log.info(f"  observer RD prod={obs['rd_prod']} WR prod={obs['wr_prod']} "
                    f"(rd idle={obs['rd_idle']} wr idle={obs['wr_idle']})")

        # 1) Aggregate productive cycles must match (pass-through skid preserves
        #    throughput; allow a tiny window-edge slack).
        TOL = max(8, rd['productive'] // 1000)
        assert abs(obs['rd_prod'] - rd['productive']) <= TOL, (
            f"RD productive mismatch: observer {obs['rd_prod']} vs in-core "
            f"{rd['productive']} (tol {TOL})")
        assert abs(obs['wr_prod'] - wr['productive']) <= TOL, (
            f"WR productive mismatch: observer {obs['wr_prod']} vs in-core "
            f"{wr['productive']} (tol {TOL})")

        # 2) Latency-histogram TOTALS. Observer and in-core are two SEPARATE
        #    axi_perf_latency_hist instances with independent windows, so the
        #    same window-edge skew applies here as against the bus meter.
        for label, o, c in (('rd AR->firstR', obs['rd_hist_firstr'], rd_hf),
                            ('rd AR->RLAST',  obs['rd_hist_rlast'],  rd_hl),
                            ('wr AW->B',      obs['wr_hist_b'],      wr_hb)):
            assert abs(o['total'] - c['total']) <= HIST_EDGE_TOL, (
                f"{label} hist total mismatch: observer {o['total']} vs in-core "
                f"{c['total']} (exceeds the {HIST_EDGE_TOL}-sample window-edge "
                f"tolerance)")
            # bin-shift due to the observer's skid is tolerated; report it.
            same = (o['bins'] == c['bins'])
            tb.log.info(f"  {label}: total={o['total']} (match); per-bin "
                        f"{'identical' if same else 'shifted (skid latency)'}: "
                        f"obs={o['bins']} incore={c['bins']}")
        tb.log.info("OBSERVER EQUIVALENCE PASSED: productive + histogram totals "
                    "match the in-core monitors")

    elif test_type == 'compress_char':
        # Compression characterization: route monbus to the bulk-trace
        # (debug_sram) path -- mon_err_cfg=0 -- so the compressor is
        # exercised, run a DMA workload, then read dbg_wr_ptr + compressor
        # stats (logged by run_dma_test). Run at USE_MON_COMPRESSION=1 and 0
        # and diff dbg_wr_ptr to see the compression effect.
        num_ch = _built_channels()
        desc_per_ch = int(os.environ.get('DMA_DESC_PER_CH', '4'))
        xfer_bytes = int(os.environ.get('DMA_XFER_BYTES', '8192'))
        tb.log.info(f"=== Compression char: {num_ch}ch x {desc_per_ch}desc "
                    f"(bulk-trace routing) ===")
        ok = await tb.run_ping_test()
        ok &= await tb.run_dma_test(
            num_channels=num_ch,
            descriptors_per_channel=desc_per_ch,
            transfer_bytes=xfer_bytes,
            timeout_clocks=int(os.environ.get('DMA_TIMEOUT_CLOCKS', '80000')),
            mon_err_cfg=0,   # MON_ERR_CFG_BULK_TRACE -> debug_sram via compressor
            compress_en=True,  # set WRMON.COMPRESS_EN -> exercise the compressor
        )

    elif test_type == 'ext_suite':
        # TASK-101: run the named Stream extended-addressing suite (row/row,
        # row/col, col/row, col/col) over the real bridge RTL. Requires the
        # harness built with USE_ROW_COL_MAJOR_ADDRESSING=1.
        tb.log.info("=== TASK-101 extended-addressing suite (row/col x row/col) ===")
        ok = await tb.run_ping_test()
        W = int(os.environ.get('EXT_W', '4'))
        H = int(os.environ.get('EXT_H', '4'))
        ok &= await tb.run_ext_suite_test(W=W, H=H)
        assert ok, "ext_suite: one or more addressing cases failed"

    elif test_type == 'ext_char':
        # TASK-101 characterization: sweep the four modes x sizes, measure RD/WR
        # perf, dump JSON. Small sizes here validate the perf plumbing in sim;
        # the full sweep runs on the board via `make host-ext_char`.
        tb.log.info("=== TASK-101 extended-addressing characterization sweep ===")
        ok = await tb.run_ping_test()
        sizes = [tuple(int(x) for x in s.split('x'))
                 for s in os.environ.get('EXT_CHAR_SIZES', '8x8,16x16').split(',')]
        out = os.environ.get('EXT_CHAR_OUT', 'ext_char_sim.json')
        ok &= await tb.run_ext_char_test(sizes, out)
        assert ok, "ext_char: sweep failed (mode/size did not complete, or perf read zero)"

    elif test_type == 'ext_chain':
        # TASK-059 regression, aggressive: CHAIN strided/transpose extended
        # descriptors via next_ptr (the pre-si failure shape). The fix gates the
        # run-base generator start on w_is_ext; before it, a chained strided
        # descriptor read the wrong source and DROPPED write beats ("holes").
        # Verified board-side via the sink-slave beat count (TIMER_EXPECTED_BEATS)
        # + no CH_ERROR, and in sim via the exact rd/wr beat counters.
        tb.log.info("=== TASK-059 aggressive chained-transpose regression ===")
        ok = await tb.run_ping_test()
        W = int(os.environ.get('EXT_W', '4'))
        H = int(os.environ.get('EXT_H', '4'))
        depth = int(os.environ.get('EXT_CHAIN_DEPTH', '4'))
        ok &= await tb.run_ext_chain_test(W=W, H=H, depth=depth)
        assert ok, "ext_chain: chained strided/transpose descriptor regression failed"

    elif test_type == 'ext_chain_soak':
        # TASK-059 aggressive SOAK: loop randomized MIXED chained strided/transpose
        # descriptors (the pre-si failure shapes) at volume. Board-equivalent; scale
        # EXT_SOAK_ITERS up for the 10-min hardware run.
        tb.log.info("=== TASK-059 aggressive chained-transpose SOAK ===")
        ok = await tb.run_ping_test()
        iters = int(os.environ.get('EXT_SOAK_ITERS', '15'))
        seed = int(os.environ.get('EXT_SOAK_SEED', '0x5EED'), 0)
        ok &= await tb.run_ext_chain_soak(iterations=iters, seed=seed)
        assert ok, "ext_chain_soak: a mixed chained run dropped beats / stalled"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    report = tb.get_report()
    tb.log.info(f"Report: {report}")
    assert ok, f"Test '{test_type}' failed with {report['errors']} errors"


