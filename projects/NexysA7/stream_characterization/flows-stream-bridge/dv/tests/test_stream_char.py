"""
Stream Characterization Harness Test Runner

End-to-end test of the stream_char_harness through its UART interface.
Verifies UART → AXIL decode → CSR / desc_ram / APB paths in simulation
before committing to FPGA hardware.

Test Types (dispatched via TEST_TYPE env var):
  'ping'       : Scratch register write/readback + build ID check
  'desc_load'  : Descriptor loading into desc_ram via UART
  'csr_read'   : Read status, wr_ptr, CRC registers
  'apb_config' : Write/readback through axil2apb to STREAM APB space
  'desc_perf'  : Open descriptor-monitor perf window, run DMA, verify buckets
  'rw_perf'    : Open data-read/data-write datapath perf windows + per-channel
                 buckets + latency histograms, run DMA, verify from the in-core
                 monitor CSRs (RFC Stage E option 2, CSR route)

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches on TEST_TYPE)
  - Single parameter generator (test_type × config)
  - Single pytest wrapper (fully parametrised)

Simulation speed: UART_BAUD is overridden to 12.5 MHz (CLKS_PER_BIT=8)
so that UART transfers take ~80 ns/byte instead of ~87 us/byte.

Author: RTL Design Sherpa
Created: 2026-04-10
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# The flow directory uses hyphens (`flows-stream-bridge/`) for consistency with
# shell paths and FPGA tooling conventions, so it is not a valid Python package.
# Inject the flow's `dv/` directly into sys.path and import the tbclasses module
# unqualified.
_flow_dv = os.path.join(repo_root, "projects/NexysA7/stream_characterization/flows-stream-bridge/dv")
if _flow_dv not in sys.path:
    sys.path.insert(0, _flow_dv)

from tbclasses.stream_char_tb import StreamCharTB

# ==========================================================================
# CocoTB test function
# ==========================================================================

# Default 50 ms caps the entire test. Realistic breakdown: UART setup
# ~2.5 ms of sim time, poll window ~500 us, plus margin. Was 2000 ms;
# lowered so a broken DMA surfaces as a cocotb timeout in seconds, not
# minutes. Override via SIM_TIMEOUT_MS env var for deep-chain repro runs
# (16 desc x 2 ch needs ~200 ms sim time at 8 KB / desc).
@cocotb.test(timeout_time=int(os.environ.get('SIM_TIMEOUT_MS', '50')), timeout_unit="ms")
async def cocotb_test_stream_char(dut):
    """Unified stream characterization test — dispatches on TEST_TYPE."""
    test_type = os.environ.get('TEST_TYPE', 'ping')

    tb = StreamCharTB(dut)
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
        # count is BASE_RTL_PARAMS['NUM_CHANNELS'] (SIM_NUM_CHANNELS), so
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
                    f"{xfer_bytes}B  (build={BASE_RTL_PARAMS.get('NUM_CHANNELS')}, "
                    f"compress_en={compress_en}, mon_err_cfg={mon_err_cfg}) ===")
        ok = await tb.run_ping_test()
        timeout_clocks = int(os.environ.get('DMA_TIMEOUT_CLOCKS', '50000'))
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
            assert hist['total'] == bursts, \
                (f"{name} histogram total {hist['total']} != burst count {bursts}")
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
            num_channels=4,
            descriptors_per_channel=4,
            transfer_bytes=65536,      # 4ch x 4desc x 64KB = 1 MB moved => lots of cycles
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

        # 2) Latency-histogram TOTALS (= burst counts) must match exactly.
        for label, o, c in (('rd AR->firstR', obs['rd_hist_firstr'], rd_hf),
                            ('rd AR->RLAST',  obs['rd_hist_rlast'],  rd_hl),
                            ('wr AW->B',      obs['wr_hist_b'],      wr_hb)):
            assert o['total'] == c['total'], (
                f"{label} hist total mismatch: observer {o['total']} vs in-core "
                f"{c['total']}")
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
        num_ch = BASE_RTL_PARAMS.get('NUM_CHANNELS', 4)
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

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    report = tb.get_report()
    tb.log.info(f"Report: {report}")
    assert ok, f"Test '{test_type}' failed with {report['errors']} errors"


# ==========================================================================
# Parameter generation
# ==========================================================================

# Simulation-fast UART baud (CLKS_PER_BIT = 100MHz / 12.5MHz = 8)
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000

# RTL parameters for the harness
BASE_RTL_PARAMS = {
    'DATA_WIDTH': 128,
    'ADDR_WIDTH': 32,
    # Bandwidth-delay-product sizing for the read datapath. The rw_perf bubble
    # study showed the residual ~6% is 100% RD starvation (bp=0): with 16-beat
    # (256 B) bursts and a measured AR->firstR latency of 64-127 cyc, the old
    # AR_MAX_OUTSTANDING=8 (8 x 16 = 128 cyc coverage) sat right at the latency
    # knife-edge, costing ~1 dead cycle per burst boundary.
    #
    # Sizing target = 16: the per-channel SRAM that buffers in-flight read data
    # is BRAM, and 7-series BRAM is power-of-2 deep (512x72 / 1Kx36 / ... per
    # primitive). A 128-bit-wide buffer packs onto 512-deep tiles, so any depth
    # in (256, 512] costs the SAME BRAM as 512 -- a 384-deep SRAM just wastes
    # entries 384-511. So size outstanding to fill the pow-2 tile: AR=AW=16 ->
    # 16 x 16-beat = 256 beats in flight, x2 headroom = SRAM_DEPTH 512 (fully
    # justified, no dead space) and 256 cyc of latency coverage (>> the 127 cyc
    # worst case). Keeps bursts <= 1024 B (real-system QoS limit -- no long-burst
    # masking). The R/B response-delay models scale with the in-flight count so
    # the modeled memory never back-pressures and masks the engine. All
    # env-overridable to A/B the old 8/256/256 baseline: SIM_AR_OUTSTANDING /
    # SIM_AW_OUTSTANDING / SIM_SRAM_DEPTH / SIM_RESP_DELAY_R_CAP / _B_CAP.
    'SRAM_DEPTH': int(os.environ.get('SIM_SRAM_DEPTH', '512')),
    'AR_MAX_OUTSTANDING': int(os.environ.get('SIM_AR_OUTSTANDING', '16')),
    'AW_MAX_OUTSTANDING': int(os.environ.get('SIM_AW_OUTSTANDING', '16')),
    'RESP_DELAY_R_CAPACITY': int(os.environ.get('SIM_RESP_DELAY_R_CAP', '512')),
    'RESP_DELAY_B_CAPACITY': int(os.environ.get('SIM_RESP_DELAY_B_CAP', '32')),
    # NUM_CHANNELS shrunk from 8 to 4 to fit the Artix-7 100T BRAM budget.
    # Keep in lockstep with rtl/stream_char_top.sv. Override via
    # SIM_NUM_CHANNELS env var when investigating bugs that may be tied
    # to the 8-channel elab (e.g. the deep-chain hang first seen on the
    # NUM_CHANNELS=8 FPGA build); Verilator doesn't care about BRAM
    # tiles so bumping this for an investigation run is cheap.
    'NUM_CHANNELS': int(os.environ.get('SIM_NUM_CHANNELS', '4')),
    # Harness memories were the dominant BRAM consumers. Mirror the FPGA
    # values so sim exercises the same sizes as silicon. Bump either when a
    # test needs deeper descriptor chains or longer trace captures.
    'DESC_RAM_ENTRIES': 128,    # 128 × 256 b =  4 KB
    'DEBUG_SRAM_WORDS': 4096,   # 4K × 32 b   = 16 KB
    # MonBus bulk-trace compression. Project default is 1 (compressor in
    # path). Override with USE_MON_COMPRESSION=0 to build the uncompressed
    # baseline for the with/without compression characterization.
    'USE_MON_COMPRESSION': int(os.environ.get('USE_MON_COMPRESSION', '1')),
    # NOTE: the CAM pipeline is no longer a parameter -- the monbus compressor
    # CAM and the AXI monitor transaction CAM are ALWAYS pipelined in RTL.
}


def generate_stream_char_params():
    """
    Generate (test_type,) tuples.  Each level is CUMULATIVE:

    gate: ping                                               (1 test)
    func: gate + desc_load + csr_read + apb_config +
          dma_1ch + dma_2ch                                  (6 tests)
    full: func + dma_3ch + dma_4ch + ... + dma_<NCH>ch

    DMA tests: 2 descriptors/channel, 8 KB each = 16 KB moved per channel.
    The FULL set is capped at BASE_RTL_PARAMS['NUM_CHANNELS'] so we don't
    ask the harness to kick channels it doesn't have (FPGA build is 4-ch).
    """
    max_channels = BASE_RTL_PARAMS.get('NUM_CHANNELS', 8)
    gate_types = ['ping']
    func_types = ['desc_load', 'csr_read', 'apb_config', 'desc_perf', 'rw_perf',
                  'obs_equiv', 'dma_1ch', 'dma_2ch']
    full_types = [f'dma_{n}ch' for n in range(3, max_channels + 1)]
    full_types += ['compress_char']   # compression characterization run

    # Accept both TEST_LEVEL (Makefile convention) and REG_LEVEL (legacy)
    level = os.environ.get('TEST_LEVEL',
                os.environ.get('REG_LEVEL', 'FUNC')).upper()

    types = list(gate_types)                  # gate always included
    if level in ('FUNC', 'FULL'):
        types += func_types
    if level == 'FULL':
        types += full_types

    return [(t,) for t in types]


stream_char_params = generate_stream_char_params()


# ==========================================================================
# Pytest wrapper
# ==========================================================================

@pytest.mark.parametrize("test_type", [p[0] for p in stream_char_params])
def test_stream_char(request, test_type, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for stream characterization harness tests."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_char': 'projects/NexysA7/stream_characterization/flows-stream-bridge',
    })

    dut_name = "stream_char_harness"

    # Build source list via filelist.
    # Environment variables needed by the filelist:
    os.environ['STREAM_ROOT'] = os.path.join(repo_root_path, 'projects/components/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root_path, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root_path, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root_path, 'projects/NexysA7/stream_characterization/flows-stream-bridge')
    os.environ['FRAMEWORK_ROOT'] = os.path.join(repo_root_path, 'projects/NexysA7/stream_characterization/stream_char_framework')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/filelists/stream_char_harness.f',
    )

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_{test_type}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':   str(SIM_UART_BAUD),
        **{k: str(v) for k, v in BASE_RTL_PARAMS.items()},
    }

    extra_env = {
        'TEST_TYPE':        test_type,
        'FPGA_CLK_HZ':     str(SIM_FPGA_CLK_HZ),
        'UART_BAUD':        str(SIM_UART_BAUD),
        'TEST_LEVEL':       test_level,
        'DUT':              dut_name,
        'LOG_PATH':         log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED':             str(random.randint(0, 100000)),
        # DMA test parameters: 2 descriptors/ch x 8KB = 16KB moved per channel
        'DMA_DESC_PER_CH':  '2',
        'DMA_XFER_BYTES':   '8192',
    }

    # Use Verilator by default
    simulator = os.environ.get('SIM', 'verilator').lower()

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
        # --public-flat-rw exposes every internal signal/instance to VPI so
        # cocotb can probe deep state (e.g., axi_write_engine internals)
        # without needing top-level pass-through ports. Slight sim-perf cost.
        "--public-flat-rw",
        "-Wno-TIMESCALEMOD",
        "-Wno-MULTIDRIVEN",    # PeakRDL stream_regs.sv
        "-Wno-WIDTHEXPAND",    # minor width warnings in STREAM hierarchy
        "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE",       # descriptor_engine pre-existing slice warning
        "-Wno-UNOPTFLAT",      # dataint_crc combinational cascade (structural CRC)
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_stream_char",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=simulator,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"PASS {test_type}! Logs: {log_path}")
    except Exception as e:
        print(f"FAIL {test_type}: {e}")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        raise
