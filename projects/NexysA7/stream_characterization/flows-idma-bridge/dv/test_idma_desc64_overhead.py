"""
Pytest wrapper: descriptor-fetch overhead of the iDMA desc64 frontend.
Reuses the area flow's desc64 filelist (run `make gen` first) plus the flat
cocotb wrapper. Sweep via env: IDMA_DESC_COUNT, IDMA_DESC_LEN.
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
            if line and not line.startswith("#"):
                out.append(line)
    return out


def _sources():
    deps = _read_flist(os.path.join(FLISTS, "deps.f"))
    fe = _read_flist(os.path.join(FLISTS, "idma_desc64.f"))
    seen, srcs = set(), []
    for s in deps + fe + [os.path.join(HERE, "idma_desc64_fe_flat.sv")]:
        if s.endswith(".vlt") or s in seen:
            continue
        seen.add(s)
        srcs.append(s)
    return srcs


def test_idma_desc64_overhead(request):
    if not os.path.isdir(FLISTS):
        pytest.skip("filelists missing -- run `make gen` in flows-idma-bridge first")
    run(
        verilog_sources=_sources(),
        includes=_read_flist(os.path.join(FLISTS, "incdirs.f")),
        toplevel="idma_desc64_fe_flat",
        module="cocotb_idma_desc64_overhead",
        python_search=[HERE],
        testcase="cocotb_test_idma_desc64_overhead",
        compile_args=[
            "-Wno-fatal", "--timescale", "1ns/1ps",
            "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-UNOPTFLAT",
            "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN", "-Wno-SELRANGE",
            "-Wno-LATCH", "-Wno-WIDTHCONCAT", "-Wno-PINMISSING",
        ],
        sim_build=os.path.join(HERE, "sim_build_desc64"),
        waves=bool(int(os.environ.get("WAVES", "0"))),
    )
