"""
Pytest wrapper: cosim perf measurement of the iDMA rw_axi backend.

Reuses the area flow's generated filelists (run `make gen` in flows-idma-bridge
first). Sweep the same knobs STREAM uses via env vars:
  IDMA_XFER_BEATS, IDMA_RESP_DELAY, IDMA_MAX_LLEN
"""
import os
import pytest
from cocotb_test.simulator import run

HERE = os.path.dirname(os.path.abspath(__file__))
FLOW = os.path.dirname(HERE)
FLISTS = os.path.join(FLOW, "flists")


def _read_flist(path):
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            out.append(line)
    return out


def _sources():
    deps = _read_flist(os.path.join(FLISTS, "deps.f"))
    be = _read_flist(os.path.join(FLISTS, "idma_backend.f"))
    # de-dup, preserve order
    seen, srcs = set(), []
    for s in deps + be:
        if s.endswith(".vlt"):
            continue
        if s not in seen:
            seen.add(s)
            srcs.append(s)
    return srcs


def _incdirs():
    return _read_flist(os.path.join(FLISTS, "incdirs.f"))


def test_idma_backend_perf(request):
    if not os.path.isdir(FLISTS):
        pytest.skip("filelists missing -- run `make gen` in flows-idma-bridge first")

    sim_build = os.path.join(HERE, "sim_build")
    run(
        verilog_sources=_sources(),
        includes=_incdirs(),
        toplevel="idma_backend_synth_rw_axi",
        module="cocotb_idma_backend_perf",
        python_search=[HERE],
        testcase="cocotb_test_idma_backend_perf",
        parameters={
            "DataWidth": 128,
            "AddrWidth": 32,
            "UserWidth": 1,
            "AxiIdWidth": 4,
            "NumAxInFlight": 8,
            "TFLenWidth": 32,
        },
        compile_args=[
            "-Wno-fatal", "--timescale", "1ns/1ps",
            "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-UNOPTFLAT",
            "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN", "-Wno-SELRANGE",
            "-Wno-LATCH", "-Wno-WIDTHCONCAT",
        ],
        sim_build=sim_build,
        waves=bool(int(os.environ.get("WAVES", "0"))),
    )
