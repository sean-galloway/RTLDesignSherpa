# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_mon
# Purpose: Cosim run of the STREAM monitor harness (stream_mon_harness) through
#          its UART interface: program small descriptors, run a DMA so the
#          in-core monitors emit packets, route them to the tally (which
#          replaced debug_sram at 0x40000), snapshot, and read the histogram.
#
# Reuses the proven StreamCharTB UART transport (the mon harness shares the perf
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
# Load stream_char_tb by explicit file path to dodge the tbclasses namespace
# collision (both flows have a tbclasses package).
import importlib.util as _ilu
_FLOW = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', 'flows-stream-bridge'))
for _p in (os.path.join(_FLOW, 'host'), os.path.join(_FLOW, 'dv')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

def _load_stream_char_tb():
    _spec = _ilu.spec_from_file_location(
        'stream_char_tb', os.path.join(_FLOW, 'dv', 'tbclasses', 'stream_char_tb.py'))
    _m = _ilu.module_from_spec(_spec)
    _spec.loader.exec_module(_m)
    return _m

# Host bin-reads + profile-CAM load now go through each tally's dedicated cfg
# AXIL slave (record ingest stays on stream_tally@0x40000 / slave_tally@0xC0000).
STREAM_TALLY_BASE = 0x0010_0000       # stream_tally_cfg (read bins, write config)
SLAVE_TALLY_BASE  = 0x0014_0000       # slave_tally_cfg
BIN_COMPLETION0 = 0x0100              # {AXI, COMPLETION, evcode 0}

# cfg-slave config write windows (offsets within a *_tally_cfg slave):
PROFILE_CLEAR_OFF = 0x0100            # any write clears the legal-set CAM
PROFILE_ENTRY_OFF = 0x0200            # + idx*4: load dense-bin idx with a key
MON_N_PROFILE     = 64               # legal-set size (matches MON_N_PROFILE)


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
]


async def profile_load(tb, base, legal):
    """Clear + load a legal set into a tally's CAM over its cfg AXIL slave."""
    await tb.uart_write(base + PROFILE_CLEAR_OFF, 0)
    for idx, (ag, pr, ty, ec) in enumerate(legal):
        await tb.uart_write(base + PROFILE_ENTRY_OFF + idx * 4,
                            profile_key(ag, pr, ty, ec))


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
    _m = _load_stream_char_tb()
    StreamCharTB, CSR_CTRL, compose = _m.StreamCharTB, _m.CSR_CTRL, _m.compose

    tb = StreamCharTB(dut)
    # The mon harness wraps axi4_dma_slaves inside dma_slave_monitors (also
    # named u_dma_slaves), so the beat-count backdoor sits one level deeper.
    tb.dma_slaves_path = ('u_dma_slaves', 'u_dma_slaves')
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
        dut._log.info(f"[addr-range] queued match-all DEBUG range0 rd+wr (ctrl=0x{ctrl_val:02x}) for post-reset programming")

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
    # Profile mode: load the STREAM legal set into the tally CAM over its cfg
    # AXIL slave (persists across the DMA's soft-reset; the CAM resets only on
    # aresetn / an explicit clear).
    profile_mode = os.environ.get('PROFILE_MODE', '0') == '1'
    if profile_mode:
        await profile_load(tb, STREAM_TALLY_BASE, STREAM_PROFILE)
        dut._log.info(f"[profile] loaded {len(STREAM_PROFILE)} legal tuples into STREAM tally CAM")

    ok = await tb.run_dma_test(
        num_channels=1, descriptors_per_channel=1, transfer_bytes=256,
        timeout_clocks=200_000, mon_err_cfg=0, compress_en=False,
        pkt_mask=0xFEF0, allow_addr_match=True,
        addr_range_writes=addr_range_writes)
    assert ok, "DMA workload did not complete"

    # Snapshot the tally (freeze auto-flushes the cache into the count SRAM).
    await tb.uart_write(CSR_CTRL, compose("CTRL", FREEZE_TRACE=1))
    await tb.wait_clocks(tb.clk_name, 50)

    # Profile mode: bins are dense per-agent indices, not {type,event}. Sweep
    # the loaded dense bins + the UNEXPECTED bin and prove per-agent resolution
    # (rd=agent 9 at bin 0, wr=agent 10 at bin 1 both fired their AddrMatch).
    if profile_mode:
        UNEXPECTED = MON_N_PROFILE
        dense = {}
        for b in list(range(len(STREAM_PROFILE))) + [UNEXPECTED]:
            v = await tb.uart_read(STREAM_TALLY_BASE + b * 4)
            if v:
                dense[b] = v
        rd_hits = dense.get(0, 0)   # agent 9  rd datapath AddrMatch
        wr_hits = dense.get(1, 0)   # agent 10 wr datapath AddrMatch
        dut._log.info(f"[profile] STREAM dense bins={dense} "
                      f"rd(agent9)={rd_hits} wr(agent10)={wr_hits} "
                      f"UNEXPECTED={dense.get(UNEXPECTED, 0)}")
        assert rd_hits > 0 and wr_hits > 0, (
            f"per-agent AddrMatch not resolved in the profile tally: "
            f"rd(bin0)={rd_hits} wr(bin1)={wr_hits} (CAM load or agent binning failed)")
        return

    # Read BOTH tally SRAMs over the same UART (distinct address spaces).
    stream_bins = await _sweep_tally(tb, STREAM_TALLY_BASE, "STREAM", dut)
    slave_bins  = await _sweep_tally(tb, SLAVE_TALLY_BASE,  "SLAVE",  dut)

    stream_total = sum(stream_bins.values())
    slave_total  = sum(slave_bins.values())
    stream_compl = sum(c for b, c in stream_bins.items() if ((b >> 8) & 0xF) == 1)
    slave_compl  = sum(c for b, c in slave_bins.items()  if ((b >> 8) & 0xF) == 1)
    dut._log.info(f"[stream_mon] STREAM total={stream_total} compl={stream_compl} | "
                  f"SLAVE total={slave_total} compl={slave_compl}")

    # Internal-probe verdict: did each group's m_axil master actually write?
    dut._log.info(f"[probe] m_axil awvalid rising-edges: STREAM(mon)={_emit['stream_mon_awvalid']} "
                  f"SLAVE(slmon)={_emit['slave_slmon_awvalid']}  "
                  f"(STREAM=0 => the in-core group never emits; >0 => emits but tally not counting)")

    # Tally asserts only when the in-core monitors are built (USE_MON=1).
    if os.environ.get('USE_MON', '0') == '1':
        assert stream_total > 0, "STREAM tally counted nothing (in-core monitor path dead)"
        # Completion is informational here (the DMA is already proven by the beat
        # count); the primary assertion is that the address-range checker fired.
        dut._log.info(f"[stream_mon] STREAM completion packets = {stream_compl}")
        # Address-range checker: match-all DEBUG ranges -> AddrMatch (type 8) packets.
        stream_addrmatch = sum(c for b, c in stream_bins.items() if ((b >> 8) & 0xF) == 8)
        dut._log.info(f"[addr-range] STREAM AddrMatch (type 8) packets = {stream_addrmatch}")
        assert stream_addrmatch > 0, (
            "no ADDR_MATCH packets in the STREAM tally — the in-core address-range "
            "checker did not fire (check MON_N_ADDR_RANGES + the RDMON/WRMON_ADDR_RANGE CSR writes)")
    # The slave-side monitors are always built; if the DMA moved data they count.
    dut._log.info(f"[stream_mon] (info) slave tally total={slave_total} compl={slave_compl}")


# ----------------------------------------------------------------------------
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000


def _run_stream_mon(request, profile=False):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_mon': 'projects/NexysA7/stream_characterization/flows-stream-monitor',
    })
    dut_name = "stream_mon_harness"

    os.environ['STREAM_ROOT'] = os.path.join(repo_root, 'projects/components/dmas/stream')
    os.environ['CONVERTERS_ROOT'] = os.path.join(repo_root, 'projects/components/converters')
    os.environ['MISC_ROOT'] = os.path.join(repo_root, 'projects/components/misc')
    os.environ['STREAM_CHAR_ROOT'] = os.path.join(repo_root, 'projects/NexysA7/stream_characterization/flows-stream-monitor')
    os.environ['STREAM_CHAR_FRAMEWORK_ROOT'] = os.path.join(repo_root, 'projects/NexysA7/stream_characterization/stream_char_framework')
    os.environ['FRAMEWORK_ROOT'] = os.environ['STREAM_CHAR_FRAMEWORK_ROOT']

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/NexysA7/stream_characterization/flows-stream-monitor/rtl/filelists/stream_mon_harness.f')

    perf_dv_tests = os.path.join(repo_root, 'projects/NexysA7/stream_characterization/flows-stream-bridge/dv')
    perf_host     = os.path.join(repo_root, 'projects/NexysA7/stream_characterization/flows-stream-bridge/host')
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
        'SRAM_DEPTH': '512', 'AR_MAX_OUTSTANDING': '16', 'AW_MAX_OUTSTANDING': '16',
        'RESP_DELAY_R_CAPACITY': '512', 'RESP_DELAY_B_CAPACITY': '512',
    }
    if profile:
        rtl_parameters['MON_TALLY_PROFILE_MODE'] = '1'
        rtl_parameters['MON_N_PROFILE'] = str(MON_N_PROFILE)
    extra_env = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': str(random.randint(0, 100000)),
        'USE_MON': use_mon,
        'PROFILE_MODE': '1' if profile else '0',
    }
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
        "--trace-fst", "--trace-structs", "--trace-depth", "99",
    ]
    run(
        python_search=[tests_dir, perf_dv_tests, perf_host],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_stream_mon",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
        keep_files=True, compile_args=compile_args,
        waves=enable_waves,
        sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
        plus_args=['--trace'] if enable_waves else [],
    )


def test_stream_mon(request):
    """Direct 16-bit tally: bins by {protocol,pkt_type,event_code}."""
    _run_stream_mon(request, profile=False)


def test_stream_mon_profile(request):
    """Agent-resolved profile tally: load the legal set over the cfg AXIL slave,
    then prove per-agent AddrMatch (rd=9, wr=10) lands in distinct dense bins."""
    _run_stream_mon(request, profile=True)
