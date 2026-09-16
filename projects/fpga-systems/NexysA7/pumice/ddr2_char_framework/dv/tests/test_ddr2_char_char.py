# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Sim regression for the pumice access-pattern characterization suite.

Runs the SAME host characterization engine (pumice_char) that the board CLI
(`pumice_master.py --char`) uses, over the DFI-loopback sim, through the real
UART bridge RTL. It exercises all three access-pattern families -- incremental,
row_major (page-hit), col_major (same-bank page thrash) and its bank-interleaved
variant -- and the perf read-back path (axi_bus_meter + axi_perf_latency_hist,
by name via the harness regmap).

SCOPE -- what this proves and what it cannot. The DFI loopback (DFISlavePHY +
MemoryModel, no a7ddrphy) does NOT model DDR2 page timing, so the families move
identical data in identical time here: this test validates the *mechanism*
(program every family -> run -> freeze -> read counters -> derive metrics ->
integrity) and that the records are well-formed. The *timing separation* between
the families (the page-management penalty, bank parallelism) only appears on the
board -- see project_ddr2_char_sim_equivalence. So the asserts here are
functional (integrity clean, counters self-consistent, every read txn counted),
not perf-ordering.

The bringup mirrors test_ddr2_char_uart.py (kept self-contained so that passing
suite is untouched).
"""

import os
import sys

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.dfi.dfi_signals import DFIVersion, MemoryType
from CocoTBFramework.components.dfi.dfi_slave_phy import DFISlavePHY
from CocoTBFramework.components.dfi.dfi_base import DFIBase
from CocoTBFramework.components.dfi.dram_state import (
    AddressMapping, DramStateModel, ViolationPolicy,
)
from CocoTBFramework.components.dfi.jedec_timings import builtin_timings
from CocoTBFramework.components.dfi.dfi_timing import (
    READ_REF_COMMAND, WRITE_REF_WRDATA_EN, DFITimingProfile,
)
from CocoTBFramework.components.shared.memory_model import MemoryModel

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/pumice/"
                            "build-perf/host")
_TBC = os.path.join(_REPO, "projects/fpga-systems/NexysA7/pumice/"
                           "ddr2_char_framework/dv/tbclasses")
_BRIDGE = os.path.join(_REPO, "projects/components/converters/bin")
for _p in (_HOST, _TBC, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.harness import UartSimHarness      # noqa: E402
import ddr2_char as dc                                  # noqa: E402
import pumice_char as pc                                # noqa: E402


# UART bit rate in system clocks. MEASURED floor is 4: 3 and 2 both FAIL
# (uart_rx samples at (CLKS_PER_BIT-1)/2, which leaves no margin below 4),
# while 16 and 4 both pass. Was 16.
# The win is modest -- 126s -> 99s on the smoke test, ~1.3x -- so these
# suites are NOT UART-bound and further baud tuning will not help.
# Passed to the RTL as UART_BAUD = FPGA_CLK_HZ / CLKS_PER_BIT so the RTL
# divisor and this constant cannot drift apart.
CLKS_PER_BIT   = int(os.environ.get("TEST_CLKS_PER_BIT", "4"))
FPGA_CLK_HZ    = 100_000_000
UART_BAUD      = FPGA_CLK_HZ // CLKS_PER_BIT
ROW_W, COL_W   = 13, 10
NUM_BANKS      = 8
# JEDEC burst length in device beats, FOLLOWING the build under test.
#
# History, because the stale version of this comment cost real time: 72a73fe2
# moved DDR2 to BL8 because BL8 is the only legal a7ddrphy burst at nphases=4
# (a BL4 read filled 4 of the fixed 8 de-interleave slots and left the rest
# stale). That reasoning applied to an nphases=4 board. The board has since
# moved to DFI_RATE=2 / BL4 (build-perf ddr2_char_top.sv: DFI_RATE=2,
# DRAM_BL=4), where a BL4 burst fills its slots exactly and the constraint
# does not apply -- but the constant stayed pinned at 8 with a comment still
# asserting "BL8 is what the board runs".
#
# Consequence: no test in this suite could reach the geometry silicon ships,
# and "the char sim does not reproduce PUMICE-037" was recorded as a property
# of the DEFECT when it was a property of the TEST. Worse, a wrapper asking
# for BL4 got a BL4 *RTL* build with the HOST still programming BL8 through
# set_dfi_phase(bl=...) and bank_lsb -- a configuration matching neither.
# Follows the RTL parameter the wrapper elaborated with (_run passes the
# same value as TEST_DRAM_BL). As a hard literal this silently pinned the
# HOST to BL8 while a BL4 build ran underneath it: set_dfi_phase(bl=...)
# and the host's bank_lsb both come from here, so a BL4 test programmed
# BL8 and was not the configuration it claimed to be.
DRAM_BL        = int(os.environ.get("TEST_DRAM_BL", "8"))
DFI_RATE        = int(os.environ.get("TEST_DFI_RATE", "2"))
DRAM_BEAT_BYTES = int(os.environ.get("TEST_DRAM_BEAT_BYTES", "8"))
DRAM_DEVICE_BYTES = int(os.environ.get("TEST_DRAM_DEVICE_BYTES", str(DRAM_BEAT_BYTES)))
BEATS_PER_BURST  = DRAM_BL


def _make_dfi_slave(dut):
    num_lines = NUM_BANKS * (1 << ROW_W) * (1 << COL_W)
    memory = MemoryModel(num_lines=num_lines, bytes_per_line=DRAM_DEVICE_BYTES,
                         log=dut._log)
    mapping = AddressMapping(num_ranks=1, num_banks=NUM_BANKS,
                             num_rows=1 << ROW_W, num_cols=1 << COL_W,
                             mapping="row|bank|col")
    base = DFIBase(dfi_version=DFIVersion.V2_1, memory_type=MemoryType.DDR2,
                   timings=builtin_timings("ddr2-650-mt47h64m16hr"),
                   mapping=mapping, beats_per_burst=BEATS_PER_BURST)
    # READ CAPTURE WINDOW (read_en_gated) -- the ONE deviation from the stock
    # "legacy" profile, and it is a physics fix, not a tuning knob.
    #
    # The default profile self-times reads off the RD command and IGNORES
    # dfi_rddata_en, presenting each word for exactly ONE cycle and popping it
    # from the pending queue whether or not the controller captured it
    # (dfi_slave_phy.py::_serve_reads). Measured here, that put the first
    # rddata_valid a full cycle BEFORE the controller had EVER asserted
    # dfi_rddata_en (probe: first_valid=712950 first_en=712960,
    # en_cycles_before=0) -- a device answering before it was asked.
    #
    # That waveform is bit-identical to the a7ddrphy READ PREAMBLE, where the
    # cycle before the capture window carries UNDRIVEN DQ (all-ones on the
    # board ILA) and MUST be discarded. The two cannot be told apart by any
    # controller-side gate, so a rejected preamble and a destroyed data word
    # look the same; the aligner correctly rejects it and this model loses a
    # real beat, which then shifts every later beat ("read engine did not
    # complete", 62 beats mismatched).
    #
    # Real silicon does not behave the way the stock profile does: a gated PHY
    # holds the word until the capture window opens (the early-return path does
    # not popleft), and the free-running a7ddrphy model holds its last DQ word
    # for the same reason. Gating here makes the loopback obey that, changing
    # NOTHING else -- read_ref and the JEDEC-CL latency stay exactly as the
    # legacy profile had them, so the families still move identical data in
    # identical time and this test's scope (mechanism, not PHY fidelity) is
    # unchanged. The rest of this framework already moved off the unphysical
    # zero-latency loopback (test_ddr2_char_uart.py, test_ddr2_char_macro.py's
    # DFI_PROFILE=a7ddrphy); this file was the last one left on it.
    timing = DFITimingProfile(
        name="char_gated",
        read_ref=READ_REF_COMMAND,   # as legacy
        read_latency=None,           # as legacy: JEDEC CL
        # CHAR_READ_EN_GATED=0 reverts to the stock ungated model. Kept as a
        # switch so 'gating broke this' is a measurement rather than a
        # guess -- at BL4 the aligner's enable window is ceil(BL/DFI_RATE)
        # = 2 cycles against BL8's 4, so a model that only presents data
        # INSIDE that window has half the slack to hit it.
        read_en_gated=(os.environ.get("CHAR_READ_EN_GATED", "1") != "0"),
        write_ref=WRITE_REF_WRDATA_EN,  # as legacy
        write_latency=None,             # as legacy
    )
    slave = DFISlavePHY(dut, dut.aclk, base=base, memory=memory,
                        timing=timing, dfi_phase_bytes=DRAM_BEAT_BYTES)
    slave.dram = DramStateModel(timings=base.timings, num_banks=NUM_BANKS,
                                policy=ViolationPolicy(hard=frozenset()))
    return slave, memory


async def _bringup(dut, *, init_complete_delay: int = 20):
    """Common transport bringup via the shared UartSimHarness; only the
    DFI backend BFM + init_complete are DDR2-specific and stay here."""
    h = UartSimHarness(dut, clks_per_bit=CLKS_PER_BIT,
                       idle_inputs={"phy_dfi_init_complete": 0,
                                    "phy_dfi_ctrlupd_ack": 0,
                                    "phy_dfi_phyupd_req": 0,
                                    "phy_dfi_phyupd_type": 0})
    chan = await h.start()

    dfi_slave, memory = _make_dfi_slave(dut)

    async def _assert_init_complete():
        await ClockCycles(dut.aclk, init_complete_delay)
        dut.phy_dfi_init_complete.value = 1
    cocotb.start_soon(_assert_init_complete())

    drv = dc.DDR2CharDriver(bridge=h.make_bridge())
    return drv, chan, dfi_slave, memory


@cocotb.test(timeout_time=3000, timeout_unit="ms")
async def cocotb_test_char_families(dut):
    """Cross a few controller configs against a couple of access families;
    assert the mechanism + integrity. Exercises the paging-scheme switch
    (BANK_INTERLEAVE), the page policy (open_page) and the scheduling order
    CSR (inorder = SCHED_POLICY.order_mode), proving they
    round-trip clean over the loopback. Perf ordering is NOT asserted -- the
    loopback models no DDR2 page timing (see module docstring)."""
    drv, chan, _dfi, _mem = await _bringup(dut)

    # Pull the SAME run definition the board CLI uses (RUN_PROFILES["smoke"]);
    # the only difference from an FPGA run is txn_scale (sim=1 for speed, the
    # board uses ~1000). "smoke" crosses baseline/bank_interleave/open_page/inorder with
    # the incremental + col_major families -- enough to exercise the
    # config-apply CSR path (scheme switch + scheduler) and the perf read-back.
    profile = os.environ.get("TEST_CHAR_PROFILE", "smoke")

    def prog():
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        # set_dfi_phase writes the WHOLE DFI_PHASE word, so gear_ratio and bl
        # must be passed or they are clobbered rather than preserved.
        # gear_ratio = log2(active DFI rate): rate-2 => 1. Its CSR reset is 2
        # (the board's fixed 1:4), and pumice computes
        #     active_rate = (RATEW'(1) << gear_i),  RATEW = clog2(DFI_RATE)+1
        # so a stale gear_i=2 overflows the 2-bit shift to 0, every DFI phase
        # reads inactive, and dfi_wrdata_en is held low -- writes vanish with
        # B=OKAY and memory stays zero.
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=DFI_RATE.bit_length() - 1,
                          bl=DRAM_BL)
        return pc.run_profile(drv, profile, txn_scale=1, base_addr=0x0,
                              timeout_s=60)

    recs = await cocotb.external(prog)()
    configs = sorted({r.config for r in recs})
    dut._log.info("\n%s", pc.format_table(recs))

    # Optional raw-data dump (CHAR_DUMP=<path>) for eyeballing that the perf
    # counters are gathered properly: raw bus-meter buckets + the 16-bin
    # latency histogram per item. cocotb swallows the sim stdout, so this
    # writes to a file the caller can read. Inert unless CHAR_DUMP is set.
    _dump = os.environ.get("CHAR_DUMP")
    if _dump:
        with open(_dump, "w") as fh:
            for r in recs:
                sc = r.scenario
                fh.write(f"{r.config}/{sc.name}  ok={r.ok} mism={r.mismatched}"
                         f"  blen={sc.burst_len} txn={sc.txn_count}\n")
                fh.write(f"  WR cyc={r.wr_cycles:<6} "
                         f"[prod={r.wr_meter.prod} bp={r.wr_meter.bp} "
                         f"starv={r.wr_meter.starv} idle={r.wr_meter.idle}] "
                         f"util={r.wr_meter.util:.3f} bw={r.wr_bw_mb_s:.1f}\n")
                fh.write(f"  RD cyc={r.rd_cycles:<6} "
                         f"[prod={r.rd_meter.prod} bp={r.rd_meter.bp} "
                         f"starv={r.rd_meter.starv} idle={r.rd_meter.idle}] "
                         f"util={r.rd_meter.util:.3f} bw={r.rd_bw_mb_s:.1f} "
                         f"lat={r.rd_avg_latency_cyc:.1f}\n")
                fh.write(f"  RD hist(total={r.rd_hist_total}) = "
                         f"{list(r.rd_hist)}\n")
        dut._log.info("wrote raw perf dump to %s", _dump)

    seen_cfgs = set()
    for r in recs:
        sc = r.scenario
        seen_cfgs.add(r.config)
        tag = f"{r.config}/{sc.name}"
        # Integrity: every (config, family) round-trips clean -- proves the
        # scheme/scheduler CSR writes took effect without corrupting the path.
        assert r.ok and r.mismatched == 0, f"{tag}: integrity failed -- {r.notes}"
        # Counters self-consistent: meter buckets accumulated, util in range.
        assert r.rd_meter.total > 0, f"{tag}: read meter never counted"
        assert r.wr_meter.total > 0, f"{tag}: write meter never counted"
        assert 0.0 <= r.rd_meter.util <= 1.0, f"{tag}: rd util out of range"
        assert 0.0 <= r.wr_meter.util <= 1.0, f"{tag}: wr util out of range"
        # Latency histogram counted exactly one entry per read command.
        assert r.rd_hist_total == sc.txn_count, (
            f"{tag}: hist total {r.rd_hist_total} != txn {sc.txn_count}")
        # Derived bandwidth is finite/positive.
        assert r.rd_bw_mb_s > 0 and r.wr_bw_mb_s > 0, (
            f"{tag}: non-positive BW rd={r.rd_bw_mb_s} wr={r.wr_bw_mb_s}")

    assert seen_cfgs == set(configs), f"missing configs: {set(configs) - seen_cfgs}"
    # The (multi-config) summary + cross-config comparison run without error.
    lines = pc.summarize(recs)
    dut._log.info("summary:\n%s", "\n".join(lines))


# =============================================================================
# pytest wrapper
# =============================================================================
def _run(request, testcase: str, dfi_rate: int = 2, dram_beat_width: int = 64,
         dram_device_width: int = 0, dram_bl: int = None):
    if dram_device_width == 0:
        dram_device_width = dram_beat_width
    # BL is per-test, not a module constant. The board runs BL4 and this suite
    # was pinned to BL8, so the one geometry the board actually uses could not
    # be reached from here -- which is why the concurrent-gap defect was called
    # "does not reproduce in the char sim".
    bl = DRAM_BL if dram_bl is None else int(dram_bl)
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "ddr2_char_uart_tb_top"
    filelist_path = ("projects/fpga-systems/NexysA7/pumice/"
                     "ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    # sim_build named from the pytest node name -- already
    # <test_name>_<unique parameters> by repo convention, so unique per test by
    # construction. It was {testcase}_r{dfi_rate}, which gave the default and
    # x16 board-geometry builds ONE directory despite being different RTL.
    tag = request.node.name.replace("[", "_").replace("]", "").replace("-", "_")
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        # DFI-loopback sim: zero-skew BFM -> the host programs' board-tuple
        # PHY-timing defaults (t_phy_wrlat=1 / rddata_delay=7) do not apply.
        "TEST_CHAR_PROFILE": os.environ.get("TEST_CHAR_PROFILE", "smoke"),
        "TEST_T_PHY_WRLAT": os.environ.get("TEST_T_PHY_WRLAT", "0"),
        "TEST_RDDATA_DELAY": os.environ.get("TEST_RDDATA_DELAY", "0"),
        "DUT": dut_name,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml"),
        "TEST_DFI_RATE": str(dfi_rate),
        "TEST_DRAM_BEAT_BYTES": str(dram_beat_width // 8),
        "TEST_DRAM_DEVICE_BYTES": str(dram_device_width // 8),
        # The HOST also holds a burst length, and it is not decorative:
        # ddr2_char.BOARD_BURST_COLS = BOARD_DRAM_BL sets bank_lsb, because a
        # JEDEC burst spans exactly BL COLUMN units (the column address is
        # device-word granular). Leave the host at its BL4 default while the
        # RTL runs BL8 and the bank field lands INSIDE the burst's 8-column
        # span, striping every burst across banks -- which is the 2026-08-25
        # silicon signature this suite exists to reproduce, and exactly what
        # it reported here: "bank_interleave: 16 beats mismatched".
        # Pass-through knobs for the concurrent-gap repro. These must ride in
        # extra_env: cocotb_test hands the simulator THIS dict, so a shell
        # export alone is not guaranteed to reach the test.
        "TEST_GAPS": os.environ.get("TEST_GAPS", "0,8,13,15"),
        "TEST_TXN": os.environ.get("TEST_TXN", "64"),
        "CONCURRENT_DUMP": os.environ.get("CONCURRENT_DUMP", ""),
        "TEST_DRAM_BL": str(bl),
        # MR0 burst-length field must agree: A[2:0] 010 = BL4, 011 = BL8.
        "TEST_MR0": "0x0433" if bl == 8 else "0x0432",
    }
    compile_args = [
        "+define+USE_ASYNC_RESET",
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-VARHIDDEN", "-Wno-IMPLICIT",
        "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",  # subtractive-slave optional status outputs (matches make lint LINT_WAIVERS)
    ]
    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_ddr2_char_char",
        testcase=testcase,
        parameters={"UART_BAUD": str(UART_BAUD),
                    "FPGA_CLK_HZ": str(FPGA_CLK_HZ),
                    "DFI_RATE": str(dfi_rate),
                    "DRAM_BEAT_WIDTH": str(dram_beat_width),
                    "DRAM_DEVICE_WIDTH": str(dram_device_width),
                    # Explicit, not inherited: ddr2_char_uart_tb_top still
                    # defaults DRAM_BL=4, and a TB that does not pass an RTL
                    # parameter cannot track it when the RTL changes.
                    "DRAM_BL": str(DRAM_BL)},
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        # cocotb's verilator main only dumps when the RUNTIME --trace arg is
        # present; cocotb_test's waves=True adds only the compile-time flags,
        # and its Verilator runner forwards plus_args (not sim_args) to the
        # binary.
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")


@cocotb.test(timeout_time=6000, timeout_unit="ms")
async def cocotb_test_char_concurrent_gap(dut):
    """The PUMICE-037 shape, driven by the REAL hardware engines.

    Everything about the stimulus here is the silicon datapath: the same
    axi4_master_wr_pattern_gen / axi4_master_rd_crc_check instances inside
    char_gen_unit, the same pumice_top, the same harness CSRs, programmed by
    the same host code (pumice_char.measure_concurrent) that runs on the board.
    Only the PHY + DRAM are modelled. Nothing here approximates a generator
    with an AXI sequence and a delay -- that approximation is what made the
    controller-level TB pass at rd_gap=15 while silicon failed: at the board
    geometry it issued ONE column command per transaction inside a single DRAM
    page, where the board issues eight and crosses a page every 2048 B.

    On silicon (75 MHz, BL4 x16, open_page, 1 writer + 1 reader, incremental):
        gap 0..12  clean
        gap >= 13  wrong data -- 13: 1547, 14: 1436, 15: 709 beats mismatched
    with the fixed timing derivation applied. Reader-alone is clean at every
    gap, so it needs the concurrent writer.
    """
    drv, chan, _dfi, _mem = await _bringup(dut)
    gaps = [int(x) for x in os.environ.get("TEST_GAPS", "0,8,13,15").split(",")]
    txn = int(os.environ.get("TEST_TXN", "64"))

    def prog():
        drv.soft_reset()
        drv.set_dfi_cmd_delay(int(os.environ.get("TEST_CMD_DELAY", "0")))
        drv.set_dfi_phase(rd_phase=int(os.environ.get("TEST_RD_PHASE", "0")),
                          wr_phase=int(os.environ.get("TEST_WR_PHASE", "0")),
                          gear_ratio=DFI_RATE.bit_length() - 1,
                          bl=DRAM_BL)
        out = []
        for gap in gaps:
            sc = pc.Scenario(name=f"concurrent_gap{gap}",
                             family=pc.FAM_INCREMENTAL,
                             burst_len=8, txn_count=txn, gap=gap)
            r = pc.measure_concurrent(drv, sc, cfg=pc.CONFIGS["open_page"],
                                      n_wr=1, n_rd=1, timeout_s=120.0)
            out.append((gap, r))
        return out

    recs = await cocotb.external(prog)()

    # Results to a FILE, not just the log. cocotb output is swallowed on a
    # PASS, so a passing run leaves no evidence of what it actually ran -- and
    # a run that silently did not simulate (stale sim_build, a leftover
    # .sim_busy lock in the shared build dir) is indistinguishable from a
    # genuine clean result. Writing the per-gap numbers out makes "it passed"
    # checkable instead of trusted.
    dump = os.environ.get("CONCURRENT_DUMP")
    if dump:
        with open(dump, "w") as fh:
            fh.write(f"gaps={gaps} txn={txn} BL={DRAM_BL} "
                     f"rate={DFI_RATE} beat={DRAM_BEAT_BYTES}B "
                     f"dev={DRAM_DEVICE_BYTES}B\n")
            for gap, r in recs:
                fh.write(f"gap={gap} ok={r.ok} mismatched={r.mismatched} "
                         f"bytes={r.bytes_moved} notes={r.notes}\n")

    # A verdict needs a count behind it: a scenario that moved no read beats
    # would "pass" the mismatch check while proving nothing.
    bad = []
    for gap, r in recs:
        dut._log.info("gap %-3d ok=%s mismatched=%s notes=%s",
                      gap, r.ok, r.mismatched, r.notes)
        assert r.bytes_moved > 0, f"gap {gap}: no bytes moved -- vacuous check"
        if r.mismatched or not r.ok:
            bad.append((gap, r.mismatched, r.notes))
    assert not bad, ("concurrent gap defect reproduced: "
                     + "; ".join(f"gap{g}: {m} beats mismatched {n}"
                                 for g, m, n in bad))


def test_ddr2_char_char_families(request):
    _run(request, "cocotb_test_char_families")


def test_ddr2_char_char_families_x16(request):
    # The BOARD's geometry: 32b pumice beat over an x16 device. The column
    # address is DEVICE-WORD granular (BYTE_OFFSET_WIDTH=clog2(DEVICE/8)), so a
    # BL4 burst spans BL(=4) column units and the legal minimum bank_lsb for
    # BANK_INTERLEAVE is 2 -- NOT BL*DEVICE/BEAT(=2)->lsb=1, which lands the
    # bank field inside the burst's column span and stripes every burst across
    # banks (the 2026-08-25 board signature: bank_interleave 32000/32000 beats
    # mismatched while device==beat sim passed). At device==beat the wrong and
    # right formulas coincide, which is exactly why the default-geometry
    # families test above cannot catch this class.
    _run(request, "cocotb_test_char_families", dfi_rate=2, dram_beat_width=32,
         dram_device_width=16)


def test_ddr2_char_char_concurrent_gap_board(request):
    # The BOARD point exactly: DFI_RATE=2, 32b pumice beat over an x16 device,
    # and BL4 -- the burst length silicon runs. The x16 families test already
    # used the first three; BL was stuck at the module's 8, so no test in this
    # suite has ever run the geometry the board actually ships.
    _run(request, "cocotb_test_char_concurrent_gap", dfi_rate=2,
         dram_beat_width=32, dram_device_width=16, dram_bl=4)
