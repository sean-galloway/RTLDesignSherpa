# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_mon
# Purpose: Cosim run of the STREAM monitor harness (stream_harness) through
#          its UART interface: program small descriptors, run a DMA so the
#          in-core monitors emit packets, route them to the tally (which
#          replaced debug_sram at 0x40000), snapshot, and read the histogram.
#
# Reuses the proven StreamHarnessTB UART transport (the mon harness shares the perf
# harness's UART/CSR/descriptor interface). Pattern B.

import os
import sys
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# The reusable transport + its deps live in the perf flow's dv/ and host/ trees.
# The shared UART transport is COMPONENT level now (one class, both builds), so
# this is an ordinary import -- no explicit-file-path loader, and nothing
# pointing at the pre-migration tree. The area conftest puts <area>/dv and
# <area>/bin on sys.path; this adds them again so the module also imports when
# cocotb execs it directly, outside any pytest session.
_AREA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     '..', '..', '..'))
for _p in (os.path.join(_AREA, 'dv'), os.path.join(_AREA, 'bin')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from tbclasses.stream_harness_tb import StreamHarnessTB, CSR_CTRL, compose  # noqa: E402

# The tally exposes FOUR clean AXIL ports (2 wr, 2 rd). Count readback rides the
# ingest window's READ channel (stream_tally@0x40000 / slave_tally@0xC0000);
# config (profile-CAM load/clear) rides the cfg window's WRITE channel
# (stream_tally_cfg@0x100000 / slave_tally_cfg@0x140000).
STREAM_TALLY_RD   = 0x0004_0000       # count readback (ingest-window read port)
SLAVE_TALLY_RD    = 0x000C_0000
STREAM_TALLY_CFG  = 0x0010_0000       # config write (profile CAM), config readback
SLAVE_TALLY_CFG   = 0x0014_0000
BIN_COMPLETION0 = 0x0100              # {AXI, COMPLETION, evcode 0}

# CAM programming registers (offsets within a *_tally_cfg slave). Register-based
# (index comes from data, not address) -> bus-width independent, no stride hazard.
CAM_CLEAR_OFF = 0x0100               # any write invalidates all CAM entries
CAM_KEY_OFF   = 0x0108               # wdata[31:0] = key to load next
CAM_LOAD_OFF  = 0x0110               # wdata = (1<<31 valid) | index -> load CAM_KEY
MON_N_PROFILE = 64                   # legal-set size (matches MON_N_PROFILE)


def profile_key(agent, protocol, pkt_type, event_code):
    """Legal-set key: {agent[15:0],proto[3:0],type[3:0],event[7:0]} (mirrors RTL)."""
    return (((agent & 0xFFFF) << 16) | ((protocol & 0xF) << 12)
            | ((pkt_type & 0xF) << 8) | (event_code & 0xFF))


# STREAM legal set for profile mode: rd/wr datapath AddrMatch (agent 9/10, AXI,
# type 8 AddrMatch, event 0x01 = AXI_ADDR_RANGE_MATCH) + scheduler/desc CORE
# completions. Dense bin index = position in this list.
STREAM_PROFILE = [
    (9,  0, 8, 0x01),   # 0: rd datapath AddrMatch
    (10, 0, 8, 0x01),   # 1: wr datapath AddrMatch
    (48, 4, 1, 0x01),   # 2: scheduler DESC_COMPLETE
    (16, 4, 1, 0x40),   # 3: descriptor-engine DESCRIPTOR_LOADED
    (9,  0, 0, 0x0D),   # 4: rd ADDR_RANGE error (MISS)   <- TEST_MISS repro
    (10, 0, 0, 0x0D),   # 5: wr ADDR_RANGE error (MISS)
    (9,  0, 3, 0x00),   # 6: rd TIMEOUT cmd               <- the board's mystery packet
    (10, 0, 3, 0x00),   # 7: wr TIMEOUT cmd
]


async def profile_load(tb, base, legal):
    """Clear + load a legal set into a tally's CAM over its cfg AXIL slave."""
    await tb.uart_write(base + CAM_CLEAR_OFF, 0)
    for idx, (ag, pr, ty, ec) in enumerate(legal):
        await tb.uart_write(base + CAM_KEY_OFF, profile_key(ag, pr, ty, ec))
        await tb.uart_write(base + CAM_LOAD_OFF, (1 << 31) | idx)


async def _sweep_tally(tb, base, label, dut):
    nonzero = {}
    # Monitors-on UART reads are very slow, so scan only the bins the asserts
    # need (a full 30-bin sweep does not fit the sim wall-clock budget).
    scan = ([BIN_COMPLETION0 + e for e in range(0, 4)]   # COMPLETION (type 1) ev0..3
            + [0x0800, 0x0801]                            # ADDR_MATCH (type 8) ev0/ev1
            + [0x0000, 0x000D])                           # ERROR (type 0): generic + ADDR_RANGE
    for b in scan:
        v = await tb.uart_read(base + b * 4)
        if v:
            nonzero[b] = v
    dut._log.info(f"[stream_mon] {label} tally nonzero bins: "
                  + ", ".join(f"0x{b:04x}={c}" for b, c in sorted(nonzero.items())))
    return nonzero


@cocotb.test(timeout_time=int(os.environ.get('SIM_TIMEOUT_MS', '80')), timeout_unit="ms")
async def cocotb_test_stream_mon(dut):
    from harness_addrs import H   # harness CSR base, by name

    tb = StreamHarnessTB(dut)
    # No dma_slaves_path override: the TB probes for the beat counters and
    # resolves the wrapper depth itself. This used to be set here because the
    # mon harness wrapped the slaves one level deeper than the perf one -- with
    # a single shared harness that asymmetry is gone, and the override was the
    # thing that hid the perf side's broken default.
    await tb.setup_clocks_and_reset()

    assert await tb.run_ping_test(), "ping failed — harness not alive over UART"

    # DECISIVE PROBE: host <-> desc_ram round-trip over the NEW bridge
    # (32-bit AXIL host -> 32->256 upsize -> desc_ram slave @ 0x20000).
    DESC = 0x0002_0000
    pat = {0x00: 0xDEADBEEF, 0x04: 0x12345678, 0x20: 0xCAFEBABE, 0x24: 0x0BADF00D}
    for off, val in pat.items():
        await tb.uart_write(DESC + off, val)
    rb = {off: await tb.uart_read(DESC + off) for off in pat}
    dut._log.info("[desc_ram probe] wrote " + ", ".join(f"0x{o:02x}=0x{v:08x}" for o, v in pat.items()))
    dut._log.info("[desc_ram probe] read  " + ", ".join(f"0x{o:02x}=0x{(rb[o] or 0):08x}" for o in pat))
    bad = {o: rb[o] for o in pat if (rb[o] or 0) != pat[o]}
    assert not bad, (
        f"desc_ram write/read did NOT round-trip through the new bridge: {[(hex(o), hex(rb[o] or 0)) for o in bad]} "
        f"-> the host->desc_ram path is broken (descriptors never land -> DMA idles)")
    dut._log.info("[desc_ram probe] PASS — host<->desc_ram round-trips through the new bridge")

    # Internal probes: does each monbus group actually WRITE its m_axil master?
    # mon_awvalid  = STREAM in-core group -> stream_tally (the empty one).
    # slmon_awvalid = slave group -> slave_tally (the working one, reference).
    # Edge-triggered (no per-cycle Python cost); records first assertion.
    from cocotb.triggers import RisingEdge as _RE
    _emit = {'stream_mon_awvalid': 0, 'slave_slmon_awvalid': 0}
    async def _watch(sig_name, key):
        sig = getattr(dut, sig_name, None)
        if sig is None:
            dut._log.warning(f"[probe] signal dut.{sig_name} not found"); return
        while True:
            await _RE(sig)          # edge-triggered on the signal itself (cheap)
            _emit[key] += 1
    if os.environ.get('USE_MON', '0') == '1':
        cocotb.start_soon(_watch('mon_awvalid', 'stream_mon_awvalid'))
        cocotb.start_soon(_watch('slmon_awvalid', 'slave_slmon_awvalid'))

    # Program the in-core address-range checker (allowlist) via the MON-block
    # CSRs (@ 0x1000 + 0x200 RDMON / +0x230 WRMON). DEBUG ranges 0,1 = match-all
    # so every accepted AR/AW is a debug hit -> AddrMatch packet. (Flavor 4'b1100:
    # ranges 2,3 are ERROR; left disabled this pass, so no miss/Error packets.)
    # Address-range CSRs are QUEUED here, not written now: run_dma_test issues a
    # SOFT_RESET at its start that wipes the register block, so these must be
    # programmed *inside* run_dma_test after that reset (via addr_range_writes).
    # range0 = match-all on each monitor (rd @0x200, wr @0x230; ctrl @0x220/0x250);
    # range0 is DEBUG (flavor bit0=0) -> a hit emits AddrMatch.
    addr_range_writes = None
    if os.environ.get('USE_MON', '0') == '1':
        MON = 0x1000
        ctrl_val = 0x01 | (1 << 4) | (1 << 5)       # RANGE_EN=0b0001, CHECK_EN, MATCH_EN
        addr_range_writes = []
        for rbase, cbase in ((MON + 0x200, MON + 0x220), (MON + 0x230, MON + 0x250)):
            addr_range_writes += [(rbase + 0x00, 0x00000000),   # range0 LOW  = 0
                                  (rbase + 0x04, 0xFFFFFFFF),   # range0 HIGH = match-all
                                  (cbase,        ctrl_val)]     # enable range0 + check + match
        # MISS/error repro: arm range2 (ERROR-flavored, IS_ERROR bit2) with a tiny
        # high exclude window so EVERY command is an allowlist miss -> should emit
        # Error/ADDR_RANGE (type 0, event 0x0D) into bin 0x000D. CTRL adds RANGE_EN
        # bit2 + MISS_EN(6) on top of range0/match. This mirrors the board addr_error
        # scenario -- run with TEST_MISS=1 to reproduce the empty-error-bin symptom.
        if os.environ.get('TEST_MISS', '0') == '1':
            miss_ctrl = 0x01 | (1 << 2) | (1 << 4) | (1 << 5) | (1 << 6)  # r0+r2+check+match+miss
            for rbase, cbase in ((MON + 0x200, MON + 0x220), (MON + 0x230, MON + 0x250)):
                addr_range_writes += [(rbase + 0x10, 0xFFFFFFF0),  # range2 LOW  (excludes DMA)
                                      (rbase + 0x14, 0xFFFFFFFF),  # range2 HIGH
                                      (cbase,        miss_ctrl)]   # + range2 enable + MISS
            dut._log.info("[addr-range] TEST_MISS=1: armed ERROR range2 exclude + MISS_EN")
        # Load the STREAM legal set into the tally CAM HERE too: run_dma_test's
        # SOFT_RESET wipes the CAM (it fans out to unit_aresetn), so it MUST be
        # (re)loaded AFTER that reset, exactly like the addr-range CSRs. These go
        # to the tally's config WRITE port (0x100 clear, 0x200+i*4 = entry i).
        # Register-based CAM load: CAM_CLEAR, then per entry {CAM_KEY, CAM_LOAD}.
        # The index rides in CAM_LOAD data, so no bus-width/stride hazard.
        addr_range_writes += [(STREAM_TALLY_CFG + CAM_CLEAR_OFF, 0)]
        for i, (ag, pr, ty, ec) in enumerate(STREAM_PROFILE):
            addr_range_writes += [(STREAM_TALLY_CFG + CAM_KEY_OFF, profile_key(ag, pr, ty, ec)),
                                  (STREAM_TALLY_CFG + CAM_LOAD_OFF, (1 << 31) | i)]
        dut._log.info(f"[addr-range] queued match-all DEBUG range0 rd+wr + "
                      f"{len(STREAM_PROFILE)} CAM entries for post-reset programming")

    # Small workload: 1 channel, 2 descriptors, 4 KB each. mon_err_cfg=0
    # (BULK_TRACE) routes monitor packets to the debug_sram slot = our tally;
    # compress_en=False -> raw 3-beat records the tally reassembler expects.
    # Tiny workload: monitors-on sim is glacial and UART-bound, so keep the DMA
    # small (1 descriptor, 256 B = 16 beats). A handful of AR/AW is enough to
    # produce AddrMatch packets; the beat count still proves the datapath.
    # pkt_mask 0xFEF0 = ALLOW_BASIC with bit 8 cleared -> PktTypeAddrMatch (8)
    # passes the per-type drop mask; allow_addr_match clears MASK3.ADDR_MASK so it
    # also passes the event-code stage. Without these the STREAM group filters out
    # everything the (perf-only) in-core monitors emit.
    # The tally ALWAYS routes packets through the legal-set CAM (no direct-mapped
    # bypass). The CAM is (re)loaded POST-soft-reset via addr_range_writes above,
    # since run_dma_test's SOFT_RESET wipes it.
    ok = await tb.run_dma_test(
        num_channels=1, descriptors_per_channel=1, transfer_bytes=256,
        timeout_clocks=200_000, mon_err_cfg=0, compress_en=False,
        pkt_mask=0xFEF0, allow_addr_match=True,
        addr_range_writes=addr_range_writes)
    assert ok, "DMA workload did not complete"

    # Freeze for a coherent read boundary. Reads are LIVE (direct-mapped count
    # SRAM, no write-combining cache) -- no flush needed before reading.
    await tb.uart_write(CSR_CTRL, compose("CTRL", FREEZE_TRACE=1))
    await tb.wait_clocks(tb.clk_name, 50)

    # Dense bins: index = position in the loaded legal set; UNEXPECTED = N_PROFILE.
    # rd datapath AddrMatch = agent 9 -> bin 0; wr datapath = agent 10 -> bin 1.
    UNEXPECTED = MON_N_PROFILE
    dense = {}
    for b in list(range(len(STREAM_PROFILE))) + [UNEXPECTED]:
        v = await tb.uart_read(STREAM_TALLY_RD + b * 8)   # 8-byte stride (64-bit slave)
        if v:
            dense[b] = v
    rd_hits = dense.get(0, 0)   # agent 9  rd datapath AddrMatch
    wr_hits = dense.get(1, 0)   # agent 10 wr datapath AddrMatch
    dut._log.info(f"[tally] STREAM dense bins={dense} rd(agent9)={rd_hits} "
                  f"wr(agent10)={wr_hits} UNEXPECTED={dense.get(UNEXPECTED, 0)}")
    # Did each group's m_axil master actually write? Isolates emit vs bin.
    dut._log.info(f"[probe] m_axil awvalid edges: STREAM(mon)={_emit['stream_mon_awvalid']} "
                  f"SLAVE(slmon)={_emit['slave_slmon_awvalid']}  "
                  f"(STREAM=0 => in-core group never emits; >0 => emits)")

    # TEST_MISS repro: read the ADDR_RANGE error bins (4/5) and TIMEOUT bins (6/7)
    # and surface them via an assert so the counts print regardless of log capture.
    if os.environ.get('TEST_MISS', '0') == '1':
        rd_err = dense.get(4, 0); wr_err = dense.get(5, 0)
        rd_to  = dense.get(6, 0); wr_to  = dense.get(7, 0)
        msg = (f"[TEST_MISS] ADDR_RANGE error bins rd(4)={rd_err} wr(5)={wr_err} ; "
               f"TIMEOUT_cmd bins rd(6)={rd_to} wr(7)={wr_to} ; "
               f"AddrMatch rd(0)={rd_hits} wr(1)={wr_hits} ; full dense={dense}")
        dut._log.info(msg)
        assert (rd_err > 0 or wr_err > 0), (
            "MISS armed but NO ADDR_RANGE error packet reached the tally. " + msg)

    # ---- Observer perf counters: must work with USE_AXI_MONITORS=0 ---------
    # The perf build turns the in-core monitors OFF (USE_AXI_MONITORS=0) and
    # relies on axi4_intf_master_observer as its sole perf source. That path has
    # regressed silently before: USE_AXI_MONITORS=0 once over-gated the cheap
    # bus meters as well as the heavy monitors, so the build reported ZEROS
    # rather than merely losing monitor packets. Nothing caught it, because
    # nothing asserted the meters still count.
    #
    # Assert unconditionally -- the observer is instantiated outside the
    # USE_AXI_MONITORS generate, so it must count in BOTH flavors. If this ever
    # fails only in the USE_MON=0 run, the gate has crept back over the meters.
    # Read from the OBSERVER'S OWN window, not a harness_csr mirror.
    #
    # These counters used to be observer OUTPUT PORTS, fanned into harness_csr
    # and read at its 0x100 block. The observer owns its telemetry now
    # (OBS_STAT_SEL selects, OBS_STAT_DATA returns), so the mirror and the ~70
    # ports behind it are gone. Select-then-read, by name, against the
    # observer's APB window.
    from obs_addrs import O                     # observer APB base, by name
    STAT_SEL, STAT_DATA = O("OBS_STAT_SEL"), O("OBS_STAT_DATA")

    async def obs_metric(metric: int, is_write: int, tap: int = 0) -> int:
        """One telemetry counter: METRIC[23:16], IS_WRITE[24], TAP[7:0]."""
        await tb.uart_write(STAT_SEL, (metric << 16) | (is_write << 24) | tap)
        return await tb.uart_read(STAT_DATA) or 0

    rd_prod = await obs_metric(0, 0)            # METRIC 0 = aggregate productive
    wr_prod = await obs_metric(0, 1)
    # tb.log, NOT dut._log: pytest captures dut._log on PASS, so the numbers
    # vanish exactly when you want to confirm a green run did real work.
    tb.log.info(f"[observer] rd_prod={rd_prod} wr_prod={wr_prod} "
                f"(USE_MON={os.environ.get('USE_MON','0')})")
    assign_msg = (f"observer perf counters read ZERO (rd_prod={rd_prod} "
                  f"wr_prod={wr_prod}) after a completed DMA. The observer is "
                  f"the perf build's only perf source, so zeros here mean the "
                  f"USE_AXI_MONITORS gate has crept back over the bus meters.")
    assert rd_prod > 0 or wr_prod > 0, assign_msg

    # Tally asserts only when the in-core monitors are built (USE_MON=1).
    if os.environ.get('USE_MON', '0') == '1':
        assert rd_hits > 0 and wr_hits > 0, (
            f"per-agent AddrMatch not resolved in the STREAM tally: rd(bin0)={rd_hits} "
            f"wr(bin1)={wr_hits} (CAM load or agent binning failed); m_axil awvalid edges "
            f"STREAM={_emit['stream_mon_awvalid']} SLAVE={_emit['slave_slmon_awvalid']}")


# ----------------------------------------------------------------------------
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000


def _run_stream_mon(request, profile=False):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_harness': 'projects/fpga-systems/Genesys2/stream',
    })
    dut_name = "stream_harness"

    os.environ['STREAM_ROOT'] = os.path.join(repo_root, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root, 'projects/components/misc')
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root, 'projects/fpga-systems/Genesys2/stream')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/stream_harness.f')

    # Component-level shared layers: dv/ for tbclasses.stream_harness_tb, bin/ for
    # the host libraries it imports (descriptor_builder, stream_addrs, ...).
    area_dv  = os.path.join(repo_root, 'projects/fpga-systems/Genesys2/stream/dv')
    area_bin = os.path.join(repo_root, 'projects/fpga-systems/Genesys2/stream/bin')
    # Profile mode forces the in-core monitors on and builds both tallies in
    # agent-resolved profile mode; direct mode keeps the legacy 16-bit matrix.
    use_mon  = '1' if profile else os.environ.get('USE_MON', '0')
    test_name = "test_stream_mon_profile" if profile else "test_stream_mon"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'USE_AXI_MONITORS': use_mon,
        'DATA_WIDTH': '128', 'ADDR_WIDTH': '32',
        'SRAM_DEPTH': '512',
        # Match the board build (=2). Also keeps the in-core timeout CAM loop small
        # enough for Verilator to unroll (AR=16 tripped BLKLOOPINIT on axi_monitor_timeout).
        'AR_MAX_OUTSTANDING': os.environ.get('AR_MAX_OUTSTANDING', '2'),
        'AW_MAX_OUTSTANDING': os.environ.get('AW_MAX_OUTSTANDING', '2'),
        'RESP_DELAY_R_CAPACITY': '512', 'RESP_DELAY_B_CAPACITY': '512',
    }
    if profile:
        rtl_parameters['MON_N_PROFILE'] = str(MON_N_PROFILE)
    extra_env = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'DUT': dut_name,
        'NUM_CHANNELS': str(rtl_parameters.get('NUM_CHANNELS', 4)), 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'USE_MON': use_mon,
        'PROFILE_MODE': '1' if profile else '0',
    }
    if profile:
        # Monitors-on sim + the extra CAM-load/sweep UART traffic overruns the
        # default 30-min real-time safety wall before the dense-bin sweep; give
        # it room (this is a slow integration sim — real-time on the board).
        extra_env['TB_MAX_DURATION_MIN'] = '90'
        extra_env['SIM_TIMEOUT_MS'] = '250'
    # WAVES support — follows the repo-standard pattern (test_stream_char.py):
    # --trace-fst in compile_args + waves= + sim_args + plus_args=['--trace'].
    # The +trace plusarg is what actually opens the dump at runtime.
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    compile_args = [
        "--public-flat-rw", "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT", "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        # Monitor per-slot loops do delayed array assignment; Verilator must
        # unroll them (BLKLOOPINIT) — raise the unroll budget for the monitor
        # transaction tables (AMBA guide note).
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]
    # Tracing this whole harness every clock is ~1000x slower than the sim
    # itself — build/emit the FST ONLY when WAVES=1. Without it the monitors-on
    # profile sim runs in minutes, not the 30-min+ wall it hit before.
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
    run(
        python_search=[tests_dir, area_dv, area_bin],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_stream_mon",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
        keep_files=True, compile_args=compile_args,
        waves=enable_waves,
        sim_args=(["--trace", "--trace-structs", "--trace-depth", "99"]
                  if enable_waves else []),
        plus_args=['--trace'] if enable_waves else [],
    )


def test_stream_mon(request):
    """Direct 16-bit tally: bins by {protocol,pkt_type,event_code}."""
    _run_stream_mon(request, profile=False)


def test_stream_mon_profile(request):
    """Agent-resolved profile tally: load the legal set over the cfg AXIL slave,
    then prove per-agent AddrMatch (rd=9, wr=10) lands in distinct dense bins."""
    _run_stream_mon(request, profile=True)
