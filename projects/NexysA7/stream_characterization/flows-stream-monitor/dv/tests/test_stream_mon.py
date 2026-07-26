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

STREAM_TALLY_BASE = 0x0004_0000       # stream tally (bridge slave stream_tally)
SLAVE_TALLY_BASE  = 0x000C_0000       # slave  tally (bridge slave slave_tally)
BIN_COMPLETION0 = 0x0100              # {AXI, COMPLETION, evcode 0}


async def _sweep_tally(tb, base, label, dut):
    nonzero = {}
    scan = [pt << 8 for pt in range(16)] + [BIN_COMPLETION0 + e for e in range(1, 8)]
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

    # Small workload: 1 channel, 2 descriptors, 4 KB each. mon_err_cfg=0
    # (BULK_TRACE) routes monitor packets to the debug_sram slot = our tally;
    # compress_en=False -> raw 3-beat records the tally reassembler expects.
    ok = await tb.run_dma_test(
        num_channels=1, descriptors_per_channel=2, transfer_bytes=4096,
        timeout_clocks=200_000, mon_err_cfg=0, compress_en=False)
    assert ok, "DMA workload did not complete"

    # Snapshot the tally (freeze auto-flushes the cache into the count SRAM).
    await tb.uart_write(CSR_CTRL, compose("CTRL", FREEZE_TRACE=1))
    await tb.wait_clocks(tb.clk_name, 50)

    # Read BOTH tally SRAMs over the same UART (distinct address spaces).
    stream_bins = await _sweep_tally(tb, STREAM_TALLY_BASE, "STREAM", dut)
    slave_bins  = await _sweep_tally(tb, SLAVE_TALLY_BASE,  "SLAVE",  dut)

    stream_total = sum(stream_bins.values())
    slave_total  = sum(slave_bins.values())
    stream_compl = sum(c for b, c in stream_bins.items() if ((b >> 8) & 0xF) == 1)
    slave_compl  = sum(c for b, c in slave_bins.items()  if ((b >> 8) & 0xF) == 1)
    dut._log.info(f"[stream_mon] STREAM total={stream_total} compl={stream_compl} | "
                  f"SLAVE total={slave_total} compl={slave_compl}")

    # Tally asserts only when the in-core monitors are built (USE_MON=1).
    if os.environ.get('USE_MON', '0') == '1':
        assert stream_total > 0, "STREAM tally counted nothing (in-core monitor path dead)"
        assert stream_compl > 0, "no COMPLETION packets in the STREAM tally"
    # The slave-side monitors are always built; if the DMA moved data they count.
    dut._log.info(f"[stream_mon] (info) slave tally total={slave_total} compl={slave_compl}")


# ----------------------------------------------------------------------------
SIM_FPGA_CLK_HZ = 100_000_000
SIM_UART_BAUD   = 12_500_000


def test_stream_mon(request):
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
    test_name = "test_stream_mon"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'USE_AXI_MONITORS': os.environ.get('USE_MON', '0'),  # OFF for fast isolation
        'DATA_WIDTH': '128', 'ADDR_WIDTH': '32',
        'SRAM_DEPTH': '512', 'AR_MAX_OUTSTANDING': '16', 'AW_MAX_OUTSTANDING': '16',
        'RESP_DELAY_R_CAPACITY': '512', 'RESP_DELAY_B_CAPACITY': '512',
    }
    extra_env = {
        'FPGA_CLK_HZ': str(SIM_FPGA_CLK_HZ), 'UART_BAUD': str(SIM_UART_BAUD),
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': str(random.randint(0, 100000)),
    }
    compile_args = [
        "--public-flat-rw", "-Wno-TIMESCALEMOD", "-Wno-MULTIDRIVEN",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-UNOPTFLAT", "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
        # Monitor per-slot loops do delayed array assignment; Verilator must
        # unroll them (BLKLOOPINIT) — raise the unroll budget for the monitor
        # transaction tables (AMBA guide note).
        "--unroll-count", "4096", "--unroll-stmts", "20000",
    ]
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    run(
        python_search=[tests_dir, perf_dv_tests, perf_host],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_stream_mon",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env,
        keep_files=True, compile_args=compile_args,
    )
