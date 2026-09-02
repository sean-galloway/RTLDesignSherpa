# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""High-volume binning test for monbus_tally_axil.

This block is the primary test vehicle for the monitor stack: it bins
100,000+ packets across many types. It had never been tested at component
level -- only inside a ~21 minute harness build, six packets at a time, which
is exactly why "the tally reads zero" went undiagnosed for so long.

TEST_LEVEL scales the packet count:
    gate ->   2,000     func ->  50,000     full -> 200,000
"""

import os
import sys
import importlib.util as _ilu

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# projects/fpga-systems has a hyphen, so it is not importable as a package.
# Load the TB by path.
_TB = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   os.pardir, os.pardir, "tbclasses", "monbus_tally_axil_tb.py")
_spec = _ilu.spec_from_file_location("monbus_tally_axil_tb", os.path.abspath(_TB))
_mod = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
MonbusTallyTB = _mod.MonbusTallyTB
make_packet = _mod.make_packet

N_PROFILE = 64          # bins; UNEXPECTED lives at index N_PROFILE

# (agent, protocol, packet_type, event_code) -- the legal set, in bin order.
# Spread across packet TYPES on purpose: the block bins by type, so a test
# that only sends completions proves almost nothing about it.
LEGAL = [
    (9,  0, 1, 0),      # bin 0  AXI Completion TRANS_COMPLETE
    (10, 0, 1, 2),      # bin 1  AXI Completion WRITE_COMPLETE
    (9,  0, 0, 0),      # bin 2  AXI Error      SLVERR
    (9,  0, 0, 1),      # bin 3  AXI Error      DECERR
    (10, 0, 3, 1),      # bin 4  AXI Timeout    DATA
    (9,  0, 2, 1),      # bin 5  AXI Threshold  LATENCY
    (10, 0, 4, 7),      # bin 6  AXI Perf
    (9,  0, 8, 1),      # bin 7  AXI AddrMatch  RANGE_MATCH
]

_LEVELS = {"gate": 2_000, "func": 50_000, "full": 200_000}


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_tally_high_volume(dut):
    """Bin a large, known mix and require EXACT per-bin counts."""
    level = os.environ.get("TEST_LEVEL", "gate").lower()
    total = _LEVELS.get(level, _LEVELS["gate"])

    tb = MonbusTallyTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.program_legal_set(LEGAL)

    expect = {i: 0 for i in range(len(LEGAL))}
    unexpected = 0
    packets = []
    for n in range(total):
        if n % 10 == 9:                       # 10% illegal
            key = (11, 0, 5, (n % 7))
            unexpected += 1
        else:
            idx = n % len(LEGAL)
            key = LEGAL[idx]
            expect[idx] += 1
        packets.append(make_packet(*key, channel=n % 8, data=n))

    dut._log.info("[tally] TEST_LEVEL=%s: driving %d packets (%d illegal) "
                  "into %d bins" % (level, total, unexpected, len(LEGAL)))
    await tb.send_records(packets)

    # read TWO past the legal set: if the CAM index maps one high, LEGAL[7]
    # lands in bin 8 and reading only 0..7 would hide it entirely.
    bins = await tb.read_bins(len(LEGAL), N_PROFILE)
    dut._log.info("[tally] bins=%s" % (bins,))

    got_total = sum(v for k, v in bins.items() if k != "UNEXPECTED")
    assert got_total or bins["UNEXPECTED"], (
        "drove %d packets and EVERY bin reads zero. The ingest path is not "
        "accepting records -- check rec_wready and the 3-beat framing." % total)

    for i in range(len(LEGAL)):
        assert bins.get(i, 0) == expect[i], (
            "bin %d %s: expected %d, got %d"
            % (i, LEGAL[i], expect[i], bins.get(i, 0)))
    assert bins["UNEXPECTED"] == unexpected, (
        "UNEXPECTED: expected %d, got %d -- illegal packets must be counted, "
        "not dropped" % (unexpected, bins["UNEXPECTED"]))

    dut._log.info("[tally] %d packets binned exactly, %d to UNEXPECTED"
                  % (total, unexpected))


def test_monbus_tally_axil(request):
    """Component-level high-volume binning."""
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'stream_rtl': '../../../rtl',
    })
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/fpga-systems/Genesys2/stream/rtl/filelists/monbus_tally_axil.f')

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel='monbus_tally_axil',
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_tally_high_volume",
        parameters={'N_PROFILE': N_PROFILE, 'TALLY_ADDR_BITS': 7,
                    'ADDR_WIDTH': 32, 'DATA_WIDTH': 64},
        sim_build=sim_build_path(tests_dir, 'monbus_tally_axil'),
        timescale="1ns/1ps",
        waves=bool(int(os.environ.get('WAVES', '0'))),
        sim_args=(["--trace", "--trace-structs", "--trace-depth", "99"]
                  if int(os.environ.get('WAVES', '0')) else []),
        plus_args=['--trace'] if int(os.environ.get('WAVES', '0')) else [],
        compile_args=(["--trace-fst", "--trace-structs", "--trace-depth", "99"]
                      if int(os.environ.get('WAVES', '0')) else []) +
                     ["--unroll-count", "16384", "--unroll-stmts", "200000",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-SELRANGE",
                      "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY",
                      "-Wno-UNOPTFLAT", "-Wno-MULTIDRIVEN"],
    )
