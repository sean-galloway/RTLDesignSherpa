# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh performance-model calibration (Task 12)
#
# Runs the tornado traffic pattern at three offered loads on a generated
# 4x4x1 mesh fabric and compares measured injection-to-ejection latency
# against the analytical model in bin/delta_mesh_perf.py (tr=4 cycles/hop,
# the measured ring latency from Task 9).  The zero-load comparison is the
# regression tripwire: measured T0 must not exceed the model by more than
# 20%.  Loaded-latency deltas are recorded as information only because the
# small 4x4 fabric is too noisy for a tight loaded-latency bound.

import math
import os
import subprocess
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_multiple_filelists
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_TBCLASSES = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tbclasses'))
if _TBCLASSES not in sys.path:
    sys.path.insert(0, _TBCLASSES)

# bin/delta_mesh_perf.py lives at repo-root/bin.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..', '..', '..'))
_BIN = os.path.join(_REPO_ROOT, 'bin')
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from delta_mesh_perf import (
    MeshPerfParams, loaded_latency, latency, pattern_traffic)  # noqa: E402
from delta_mesh_tb import DeltaMeshFabricTB  # noqa: E402

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_4x4_th.sv'
DUT_TOP = 'delta_mesh_fabric_4x4_th'
FABRIC_SV = 'delta_mesh_fabric_4x4x1.sv'
CELL_SV = 'delta_mesh_cell.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
# The cell's dependencies, from their owning areas' filelists (mirrors the
# -f set in rtl/filelists/delta_mesh.f).
DEP_FILELISTS = (
    'rtl/amba/filelists/reset_defs.f',
    'rtl/amba/filelists/gaxi_skid_buffer.f',
    'rtl/common/filelists/arbiter_matrix.f',
)

# Calibration parameters.  Single-beat (one 64-bit flit) packets:
# L = 8 bytes, b = 8 bytes/cycle, so L/b = 1 cycle serialization.
# Serialization distance D = 0 because the packet is already at the
# destination when the last beat is accepted.
TR = 4.0
L_BYTES = 8.0
B_BYTES_PER_CYC = 8.0
SER_D = 0.0
V = 1.0

# Three offered loads for the loaded-latency sweep.
LOADS = (0.20, 0.40, 0.60)

# Zero-load regression threshold: measured T0 may not exceed modeled T0 by
# more than this fraction.
T0_MARGIN = 0.20


@pytest.fixture(scope="module")
def fabric_gen_dir(tmp_path_factory):
    """Generate the 4x4x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_perf")
    result = subprocess.run(
        [
            sys.executable,
            DELTA_GENERATOR,
            "--topology", "mesh",
            "--cells-x", "4",
            "--cells-y", "4",
            "--cells-z", "1",
            "--user-width", "64",
            "--output-dir", str(gen_dir),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, (
        f"delta_generator.py mesh failed:\n{result.stdout}\n{result.stderr}")
    assert (gen_dir / CELL_SV).is_file(), "mesh cell artifact not emitted"
    assert (gen_dir / FABRIC_SV).is_file(), "4x4x1 fabric artifact not emitted"
    return gen_dir


class DeltaMeshPerfTB(DeltaMeshFabricTB):
    """TB for perf calibration on the 4x4x1 fabric."""

    BOUNDARY_COORDS = (
        (0, 0, 0), (1, 0, 0), (2, 0, 0), (3, 0, 0),
        (0, 1, 0), (1, 1, 0), (2, 1, 0), (3, 1, 0),
        (0, 2, 0), (1, 2, 0), (2, 2, 0), (3, 2, 0),
        (0, 3, 0), (1, 3, 0), (2, 3, 0), (3, 3, 0),
    )
    PORTS = tuple((f'b{i}', i) for i in range(len(BOUNDARY_COORDS)))

    def __init__(self, dut):
        super().__init__(dut)
        self.COORD_W = self.convert_to_int(os.environ.get('TEST_COORD_W', '2'))
        self.hdr_offsets = __import__('delta_mesh.header', fromlist=['build_header_offsets']).build_header_offsets(self.COORD_W)

    def _sig(self, bidx, suffix):
        return getattr(self.dut, f'b{bidx}_{suffix}')

    async def _measure_latency(self, src_bidx, dst_bidx, pid, tag):
        """Raw-drive a single-beat packet; return injection->ejection cycles."""
        s = f'b{src_bidx}'
        d = f'b{dst_bidx}'
        sv = self._sig(src_bidx, 's_axis_tvalid')
        sr = self._sig(src_bidx, 's_axis_tready')
        sd = self._sig(src_bidx, 's_axis_tdata')
        su = self._sig(src_bidx, 's_axis_tuser')
        sl = self._sig(src_bidx, 's_axis_tlast')
        dv = self._sig(dst_bidx, 'm_axis_tvalid')
        dr = self._sig(dst_bidx, 'm_axis_tready')
        dd = self._sig(dst_bidx, 'm_axis_tdata')
        dl = self._sig(dst_bidx, 'm_axis_tlast')

        header = self.build_header(
            dst=self.BOUNDARY_COORDS[dst_bidx],
            src=self.BOUNDARY_COORDS[src_bidx],
            qos=1, vc=0, packet_id=pid)
        data = ((0xD1A << 48) | (src_bidx << 44) | (dst_bidx << 40)
                | (pid & 0xFFFFF))

        sv.value = 1
        sd.value = data
        su.value = header
        sl.value = 1
        in_cyc = None
        out_cyc = None
        cyc = 0
        while out_cyc is None:
            await RisingEdge(self.aclk)
            cyc += 1
            if in_cyc is None and int(sv.value) and int(sr.value):
                in_cyc = cyc
                sv.value = 0
                sl.value = 0
                su.value = 0
                sd.value = 0
            if int(dv.value) and int(dr.value) and int(dl.value):
                got_data = int(dd.value)
                if got_data != data:
                    raise AssertionError(
                        f"{tag}: b{src_bidx}->b{dst_bidx} data mismatch: "
                        f"got 0x{got_data:x}, expected 0x{data:x}")
                out_cyc = cyc
            if cyc > 2000:
                raise AssertionError(
                    f"{tag}: b{src_bidx}->b{dst_bidx} timed out")
        return out_cyc - in_cyc

    async def run_tornado_zero_load(self):
        """Measure T0 for the tornado pattern; compare to the model."""
        tag = "tornado-zero-load"
        pairs = pattern_traffic("tornado", (4, 4, 1))
        latencies = []
        for src, dst in pairs:
            src_bidx = self.BOUNDARY_COORDS.index(src)
            dst_bidx = self.BOUNDARY_COORDS.index(dst)
            lat = await self._measure_latency(
                src_bidx, dst_bidx, self._next_pid(), tag)
            latencies.append(lat)

        measured_t0 = sum(latencies) / len(latencies)
        avg_hops = sum(abs(s[0] - d[0]) + abs(s[1] - d[1]) + abs(s[2] - d[2])
                       for s, d in pairs) / len(pairs)
        modeled_t0 = latency(MeshPerfParams(
            hops=avg_hops, tr=TR, serialization_d=SER_D, v=V,
            l=L_BYTES, b=B_BYTES_PER_CYC, load=0.0))

        self.log.info(
            f"perf calibration (zero-load): measured T0 = {measured_t0:.2f} c, "
            f"modeled T0 = {modeled_t0:.2f} c, avg hops = {avg_hops:.2f}, "
            f"ratio = {measured_t0 / modeled_t0:.3f}")

        if measured_t0 > modeled_t0 * (1.0 + T0_MARGIN):
            raise AssertionError(
                f"{tag}: measured T0 {measured_t0:.2f} cycles exceeds modeled "
                f"T0 {modeled_t0:.2f} cycles by more than {T0_MARGIN * 100:.0f}% "
                f"(ratio {measured_t0 / modeled_t0:.3f}); lookahead or pipeline "
                f"regression suspected (issue #120)")
        return measured_t0, modeled_t0

    async def _loaded_sweep(self, load, npkts):
        """Inject sustained tornado traffic at `load`; return average latency."""
        tag = f"tornado-load-{load}"
        pairs = pattern_traffic("tornado", (4, 4, 1))
        nb = len(self.BOUNDARY_COORDS)

        # Traffic generation: each source injects a new single-beat packet
        # every 1/load cycles on average (geometric inter-arrival).
        # We drive all sources concurrently and measure head-to-tail latency.
        arrivals = {src_bidx: [] for src_bidx in range(nb)}
        completions = {src_bidx: [] for src_bidx in range(nb)}

        def src_idx(coord):
            return self.BOUNDARY_COORDS.index(coord)

        rev_map = {src_idx(dst): src_idx(src) for src, dst in pairs}

        async def sender(src_bidx):
            dst = pairs[src_bidx][1]
            dst_bidx = src_idx(dst)
            sv = self._sig(src_bidx, 's_axis_tvalid')
            sr = self._sig(src_bidx, 's_axis_tready')
            sd = self._sig(src_bidx, 's_axis_tdata')
            su = self._sig(src_bidx, 's_axis_tuser')
            sl = self._sig(src_bidx, 's_axis_tlast')
            rng = self.rng
            cyc = 0
            pid_base = src_bidx * 0x1000
            for k in range(npkts):
                pid = pid_base + k
                header = self.build_header(
                    dst=dst, src=self.BOUNDARY_COORDS[src_bidx],
                    qos=1, vc=0, packet_id=pid)
                data = ((0xD1A << 48) | (src_bidx << 44) | (dst_bidx << 40)
                        | (pid & 0xFFFFF))
                sv.value = 1
                sd.value = data
                su.value = header
                sl.value = 1
                while True:
                    await RisingEdge(self.aclk)
                    cyc += 1
                    if int(sv.value) and int(sr.value):
                        arrivals[src_bidx].append((cyc, pid))
                        break
                sv.value = 0
                # Inter-arrival gap: geometric with mean 1/load cycles.
                if 0.0 < load < 1.0:
                    u = rng.random()
                    # Inverse-CDF sampling for geometric(p): P(X=k)=p(1-p)^(k-1).
                    gap = (math.ceil(math.log(u) / math.log(1.0 - load)) - 1
                           if u > 0.0 else 0)
                    for _ in range(gap):
                        await RisingEdge(self.aclk)
                        cyc += 1

        async def receiver(dst_bidx):
            dv = self._sig(dst_bidx, 'm_axis_tvalid')
            dr = self._sig(dst_bidx, 'm_axis_tready')
            dd = self._sig(dst_bidx, 'm_axis_tdata')
            dl = self._sig(dst_bidx, 'm_axis_tlast')
            cyc = 0
            seen = 0
            src_bidx = rev_map[dst_bidx]
            while seen < npkts:
                await RisingEdge(self.aclk)
                cyc += 1
                if int(dv.value) and int(dr.value) and int(dl.value):
                    seen += 1
                    data = int(dd.value)
                    pid = data & 0xFFFFF
                    completions[src_bidx].append((cyc, pid))

        senders = [cocotb.start_soon(sender(i)) for i in range(nb)]
        receivers = [cocotb.start_soon(receiver(i)) for i in range(nb)]
        for s in senders:
            await s
        for r in receivers:
            await r

        # Match arrivals to completions by pid and compute latency samples.
        samples = []
        for src_bidx in range(nb):
            arr = {pid: cyc for cyc, pid in arrivals[src_bidx]}
            for cyc, pid in completions[src_bidx]:
                if pid not in arr:
                    raise AssertionError(
                        f"{tag}: completion pid 0x{pid:x} from b{src_bidx} "
                        f"without matching injection")
                samples.append(cyc - arr[pid])

        if not samples:
            raise AssertionError(f"{tag}: no latency samples collected")
        avg_lat = sum(samples) / len(samples)
        return avg_lat

    async def run_tornado_loaded_sweep(self):
        """Run tornado at three loads; log measured vs modeled deltas."""
        tag = "tornado-loaded-sweep"
        npkts = {'gate': 50, 'func': 200, 'full': 500}[self.TEST_LEVEL]
        results = []
        for load in LOADS:
            measured = await self._loaded_sweep(load, npkts)
            pairs = pattern_traffic("tornado", (4, 4, 1))
            avg_hops = sum(abs(s[0] - d[0]) + abs(s[1] - d[1]) + abs(s[2] - d[2])
                           for s, d in pairs) / len(pairs)
            modeled = loaded_latency(MeshPerfParams(
                hops=avg_hops, tr=TR, serialization_d=SER_D, v=V,
                l=L_BYTES, b=B_BYTES_PER_CYC, load=load))
            ratio = measured / modeled if modeled > 0 else 0.0
            results.append((load, measured, modeled, ratio))
            self.log.info(
                f"perf calibration (load {load:.2f}): measured = {measured:.2f} c, "
                f"modeled = {modeled:.2f} c, ratio = {ratio:.3f}")
        return results


@cocotb.test(timeout_time=60000, timeout_unit="ms")
async def cocotb_test_delta_mesh_perf_tornado(dut):
    tb = DeltaMeshPerfTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_tornado_zero_load()
    await tb.run_tornado_loaded_sweep()


def _run(testcase, test_level, gen_dir):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dep_sources, dep_includes = get_sources_from_multiple_filelists(
        repo_root=repo_root, filelist_paths=list(DEP_FILELISTS))
    verilog_sources = [
        *dep_sources,
        str(gen_dir / CELL_SV),
        str(gen_dir / FABRIC_SV),
        os.path.join(repo_root, HARNESS),
    ]
    includes = list(dict.fromkeys([os.path.join(repo_root, RESET_DEFS_INCDIR), *dep_includes]))

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{DUT_TOP}_{testcase}_{test_level}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir, os.path.join(tests_dir, '..', 'tbclasses')],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=DUT_TOP,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        waves=False,
        make_args=["-j", str(os.cpu_count())],
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'TEST_COORD_W': '2',
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_perf_calibration(request, test_level, fabric_gen_dir):
    _run("cocotb_test_delta_mesh_perf_tornado", test_level, fabric_gen_dir)
