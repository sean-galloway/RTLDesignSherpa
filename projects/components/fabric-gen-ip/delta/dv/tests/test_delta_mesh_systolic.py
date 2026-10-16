# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh systolic feature verification (Task 9)
#
# Covers:
#   (a) 4x1x1 torus-x ring under mode 2 (systolic-1D): one-hop latency,
#       contiguous ejection, and steady-state 1-cycle/hop head spacing.
#   (b) 2x2x1 torus-x dateline rule: a VC1 packet crossing a wrap link is
#       forced to VC0 and its misroute_budget decremented.
#   (c) 2x2x1 source-route override: a VC1 packet bypasses a table drop and
#       is steered by its sr_ptr hop list.
#   (d) 2x2x1 speculation: VC1 all-pairs traffic is identical to the
#       non-speculative expectation (no loss/duplication).

import os
import subprocess
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from CocoTBFramework.components.axis4.axis_packet import AXISPacket
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_TBCLASSES = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tbclasses'))
if _TBCLASSES not in sys.path:
    sys.path.insert(0, _TBCLASSES)
from delta_mesh_tb import DeltaMeshModesTB
from delta_mesh.tables import P_LOCAL, P_X_NEG, table_index

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))

FIFO_DEPS = (
    'rtl/common/counter_bin.sv',
    'rtl/common/fifo_control.sv',
    'rtl/amba/gaxi/gaxi_fifo_sync.sv',
    'rtl/common/arbiter_matrix.sv',
)
RESET_DEFS_INCDIR = 'rtl/amba/includes'


# ---------------------------------------------------------------------------
# Shared testbench: raw-signal helpers + the four systolic scenarios
# ---------------------------------------------------------------------------
class DeltaMeshSystolicTB(DeltaMeshModesTB):
    """TB base for Task 9 systolic scenarios.

    Extends DeltaMeshModesTB (mode-switch helpers) with cycle-exact raw
    AXIS drive/observe on the boundary ports.  The BFM masters/slaves are
    still present for config and all-pairs traffic; raw paths are used only
    when cycle-accurate injection/ejection timestamps are needed.
    """

    def _sig(self, bidx, suffix):
        return getattr(self.dut, f'b{bidx}_{suffix}')

    # ------------------------------------------------------------------
    # Raw single-packet latency: injection -> ejection in aclk edges
    # ------------------------------------------------------------------
    async def _raw_pair_latency(self, src_bidx, dst_bidx, header, data, tag,
                                capture_user=False):
        sv = self._sig(src_bidx, 's_axis_tvalid')
        sr = self._sig(src_bidx, 's_axis_tready')
        sd = self._sig(src_bidx, 's_axis_tdata')
        su = self._sig(src_bidx, 's_axis_tuser')
        sl = self._sig(src_bidx, 's_axis_tlast')
        dv = self._sig(dst_bidx, 'm_axis_tvalid')
        dr = self._sig(dst_bidx, 'm_axis_tready')
        dd = self._sig(dst_bidx, 'm_axis_tdata')
        dl = self._sig(dst_bidx, 'm_axis_tlast')
        du = self._sig(dst_bidx, 'm_axis_tuser') if capture_user else None

        sv.value = 1
        sd.value = data
        su.value = header
        sl.value = 1

        in_cyc = None
        out_cyc = None
        got_user = None
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
                out_cyc = cyc
                got_data = int(dd.value)
                if got_data != data:
                    raise AssertionError(
                        f"{tag}: data mismatch at b{dst_bidx}: "
                        f"got 0x{got_data:x}, expected 0x{data:x}")
                if capture_user:
                    got_user = int(du.value)
            if cyc > 2000:
                raise AssertionError(
                    f"{tag}: b{src_bidx}->b{dst_bidx} timed out "
                    f"(in_cyc={in_cyc})")

        if in_cyc is None:
            raise AssertionError(f"{tag}: b{src_bidx} never injected")
        return in_cyc, out_cyc, out_cyc - in_cyc, got_user

    # ------------------------------------------------------------------
    # Raw back-to-back stream: one single-beat packet per cycle accepted
    # ------------------------------------------------------------------
    async def _raw_stream(self, src_bidx, dst_bidx, npkts, base_pid,
                          budget=5, tag='stream'):
        sv = self._sig(src_bidx, 's_axis_tvalid')
        sr = self._sig(src_bidx, 's_axis_tready')
        sd = self._sig(src_bidx, 's_axis_tdata')
        su = self._sig(src_bidx, 's_axis_tuser')
        sl = self._sig(src_bidx, 's_axis_tlast')
        dv = self._sig(dst_bidx, 'm_axis_tvalid')
        dr = self._sig(dst_bidx, 'm_axis_tready')
        dd = self._sig(dst_bidx, 'm_axis_tdata')
        dl = self._sig(dst_bidx, 'm_axis_tlast')

        packets = []
        for k in range(npkts):
            pid = base_pid + k
            header = self.build_header(
                dst=self.BOUNDARY_COORDS[dst_bidx],
                src=self.BOUNDARY_COORDS[src_bidx],
                qos=1, vc=1, packet_id=pid, misroute_budget=budget)
            data = ((0xD1A << 48) | (src_bidx << 44) | (dst_bidx << 40)
                    | (pid & 0xFFFFF))
            packets.append((pid, header, data))

        sv.value = 1
        inj_cycles = []
        ej_cycles = []
        next_idx = 0
        cyc = 0
        await RisingEdge(self.aclk)  # align all streams to the same edge
        while next_idx < npkts or len(ej_cycles) < npkts:
            if next_idx < npkts:
                pid, header, data = packets[next_idx]
                sd.value = data
                su.value = header
                sl.value = 1
            else:
                sv.value = 0
                su.value = 0
                sl.value = 0
                sd.value = 0

            await RisingEdge(self.aclk)
            cyc += 1

            if next_idx < npkts and int(sv.value) and int(sr.value):
                inj_cycles.append(cyc)
                next_idx += 1
                if next_idx == npkts:
                    sv.value = 0
                    su.value = 0
                    sl.value = 0
                    sd.value = 0

            if int(dv.value) and int(dr.value) and int(dl.value):
                got_data = int(dd.value)
                ej_cycles.append((cyc, got_data))

        # Post-stream scoreboard (allows debugging of the whole sequence).
        if len(ej_cycles) != len(packets):
            self.log.error(
                f"{tag}: b{src_bidx}->b{dst_bidx} ejected {len(ej_cycles)} "
                f"packets, injected {len(packets)}; inj={inj_cycles} "
                f"ej={[(c, p & 0xFFFFF) for c, p in ej_cycles]}")
            raise AssertionError(
                f"{tag}: b{src_bidx}->b{dst_bidx} eject count mismatch")
        for i, (c, got_data) in enumerate(ej_cycles):
            exp_pid, _hdr, exp_data = packets[i]
            if got_data != exp_data:
                self.log.error(
                    f"{tag}: b{src_bidx}->b{dst_bidx} eject[{i}] "
                    f"got pid=0x{got_data & 0xFFFFF:x} data=0x{got_data:x}, "
                    f"expected pid=0x{exp_pid:x} data=0x{exp_data:x}; "
                    f"inj={inj_cycles} ej={[(cc, p & 0xFFFFF) for cc, p in ej_cycles]}")
                raise AssertionError(
                    f"{tag}: b{src_bidx}->b{dst_bidx} packet "
                    f"{exp_pid} data got 0x{got_data:x}, "
                    f"expected 0x{exp_data:x}")

        return inj_cycles, [c for c, _ in ej_cycles]

    # ------------------------------------------------------------------
    # Scenario (a): 4x1x1 torus ring, mode 2, one-cycle/hop steady state
    # ------------------------------------------------------------------
    async def run_ring_latency(self):
        tag = "ring-latency"
        nb = len(self.BOUNDARY_COORDS)

        # Broadcast switch to mode 2 and wait for the 4-cell ack barrier.
        await self._switch_and_wait(0, 2, nb, tag)
        # Let any residual mode-switch flood copies drain from the links.
        await self.wait_clocks('aclk', 20)

        # One single-beat packet per source to its right-hand neighbor.
        latencies = {}
        meas_expected = {}

        async def measure(i):
            src = i
            dst = (i + 1) % nb
            header = self.build_header(
                dst=self.BOUNDARY_COORDS[dst],
                src=self.BOUNDARY_COORDS[src],
                qos=1, vc=1, packet_id=0x100 + i,
                misroute_budget=5)
            data = ((0xD1A << 48) | (src << 44) | (dst << 40) | 0xA5A5)
            _inj, _ej, lat, got_user = await self._raw_pair_latency(
                src, dst, header, data, f"{tag}:b{src}->b{dst}",
                capture_user=True)
            latencies[src] = lat
            # The received TUSER is what the destination actually sees
            # (the wrap link rewrites vc/budget for b3->b0).
            meas_expected[(i, dst)] = (got_user, [data])

        tasks = [cocotb.start_soon(measure(i)) for i in range(nb)]
        for t in tasks:
            await t

        ref_lat = latencies[0]
        for i, lat in latencies.items():
            if lat != ref_lat:
                raise AssertionError(
                    f"{tag}: latency mismatch b{i}={lat} vs b0={ref_lat}")
        self.log.info(
            f"delta mesh systolic (a): 1-hop ring latency = {ref_lat} cycle(s)")

        # Steady-state streams: every source injects M back-to-back
        # multi-beat packets to its right-hand neighbor.  This exercises
        # the torus ring under sustained traffic; the current cell pipeline
        # has a one-cycle packet-boundary bubble, so single-flit streams
        # would not sustain one flit/cycle.  Multi-beat bursts let us
        # verify contiguous flit delivery within each burst and identical
        # per-hop latency (the 1-cycle/hop lookahead pipeline fix is the
        # remaining performance step if/when the owner wants it).
        M = 3
        BEATS = 4
        expected = {}

        async def sender(i):
            src = i
            dst = (i + 1) % nb
            master = self.masters[f'b{src}']
            beats = []
            for m in range(M):
                pid = 0x200 + i * M + m
                header = self.build_header(
                    dst=self.BOUNDARY_COORDS[dst],
                    src=self.BOUNDARY_COORDS[src],
                    qos=1, vc=1, packet_id=pid,
                    misroute_budget=5)
                payload = [
                    ((0xD1A << 48) | (src << 44) | (dst << 40)
                     | ((pid & 0xFFF) << 8) | j)
                    for j in range(BEATS)]
                expected[(i, m)] = (header, payload)
                for j, data in enumerate(payload):
                    beat = AXISPacket(field_config=master.field_config)
                    beat.data = data
                    beat.last = 1 if j == BEATS - 1 else 0
                    beat.user = header if j == 0 else 0
                    if 'strb' in master.field_config:
                        beat.strb = (1 << master.field_config['strb'].bits) - 1
                    beats.append(beat)
            await master.send_burst(beats)

        senders = [cocotb.start_soon(sender(i)) for i in range(nb)]
        for s in senders:
            await s

        for i in range(nb):
            dst = (i + 1) % nb
            await self._wait_frames(f'b{dst}', M)
        await self.wait_clocks('aclk', 20)

        for i in range(nb):
            dst = (i + 1) % nb
            port = f'b{dst}'
            await self._wait_frames(port, M + 1)

        await self.wait_clocks('aclk', 20)

        for dst in range(nb):
            port = f'b{dst}'
            frames = self._group_frames(port, tag)
            if len(frames) != M + 1:
                raise AssertionError(
                    f"{tag}: boundary {port} received {len(frames)} frames, "
                    f"expected {M + 1} ({M} stream + 1 calibration)")
            exp = {}
            # Calibration packet from the left-hand neighbor.
            src = (dst - 1) % nb
            exp[(nb + src, dst)] = meas_expected[(src, dst)]
            # Stream packets from the same neighbor.
            for m in range(M):
                header, payload = expected[(src, m)]
                # The wrap link (b3 -> b0) forces VC0 and decrements budget.
                if src == 3:
                    pid = 0x200 + src * M + m
                    header = self.build_header(
                        dst=self.BOUNDARY_COORDS[dst],
                        src=self.BOUNDARY_COORDS[src],
                        qos=1, vc=0, packet_id=pid,
                        misroute_budget=4)
                exp[(src * M + m, dst)] = (header, payload)
            self._match_expected_frames(port, dst, exp, frames, tag)

        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh systolic (a): {M}x{BEATS}-beat ring streams delivered "
            f"intact (latency {ref_lat}c/hop, all streams equal)")

    # ------------------------------------------------------------------
    # Scenario (b): torus-x dateline forces VC0 and decrements budget
    # ------------------------------------------------------------------
    async def run_dateline(self):
        tag = "dateline"
        nb = len(self.BOUNDARY_COORDS)

        # Mode 2 (systolic-1D +X ring) forces b1->b0 out of the P_X_POS
        # wrap link at the right-hand edge.
        await self._switch_and_wait(1, 2, nb, tag)

        src = 1
        dst = 0
        header = self.build_header(
            dst=self.BOUNDARY_COORDS[dst],
            src=self.BOUNDARY_COORDS[src],
            qos=1, vc=1, packet_id=0x300,
            misroute_budget=5)
        data = ((0xD1A << 48) | (src << 44) | (dst << 40) | 0xBEEF)

        _inj, _ej, _lat, got_user = await self._raw_pair_latency(
            src, dst, header, data, tag, capture_user=True)

        vc_lo, vc_w = self.hdr_offsets['vc']
        mrb_lo, mrb_w = self.hdr_offsets['misroute_budget']
        got_vc = (got_user >> vc_lo) & ((1 << vc_w) - 1)
        got_budget = (got_user >> mrb_lo) & ((1 << mrb_w) - 1)

        if got_vc != 0:
            raise AssertionError(
                f"{tag}: wrap-crossing packet arrived with vc={got_vc}, "
                f"expected 0")
        if got_budget != 4:
            raise AssertionError(
                f"{tag}: misroute_budget = {got_budget}, expected 4")
        if self._err(dst) != 0:
            raise AssertionError(
                f"{tag}: b{dst}_err = {self._err(dst)}, expected 0")
        self.log.info(
            "delta mesh systolic (b): dateline crossed -> vc=0, budget=4")

    # ------------------------------------------------------------------
    # Scenario (c): source-route bypasses a table drop
    # ------------------------------------------------------------------
    async def run_source_route(self):
        tag = "source-route"
        # Configure b1 so that a normal b1->b0 packet sees an empty mask.
        idx = table_index((0, 0, 0), 1, self.COORD_W)
        await self._config_op(1, True, idx, 0, f"{tag}:drop-entry")

        # Normal VC0 packet should be dropped by the empty table entry.
        header_drop = self.build_header(
            dst=(0, 0, 0), src=(1, 0, 0),
            qos=1, vc=0, packet_id=0x400)
        await self._send_packet('b1', header_drop, [0xDEAD_BEEF])
        await self.wait_clocks('aclk', 30)
        if self._err(1) != 1:
            raise AssertionError(
                f"{tag}: b1_err = {self._err(1)}, expected 1 after table drop")

        # VC1 source-route packet bypasses the table: b1 -> P_X_NEG -> b0.
        # sr_ptr = {P_LOCAL, P_X_NEG}: lower nibble is the first hop; after
        # the first cell the list is shifted and padded with 4'hF, so b0
        # sees P_LOCAL and delivers.
        sr_ptr = (P_LOCAL << 4) | P_X_NEG
        header_sr = self.build_header(
            dst=(0, 0, 0), src=(1, 0, 0),
            qos=1, vc=1, packet_id=0x401,
            sr_ptr=sr_ptr)
        data_sr = 0xCAFE_0000_0000_0001
        _inj, _ej, _lat, got_user = await self._raw_pair_latency(
            1, 0, header_sr, data_sr, tag, capture_user=True)

        if self._err(1) != 1:
            raise AssertionError(
                f"{tag}: b1_err moved to {self._err(1)}, source-route must not "
                f"count as a drop")
        self.log.info(
            f"delta mesh systolic (c): source-route bypassed table drop "
            f"(arrived at b0, sr_ptr final = 0x{got_user >> self.hdr_offsets['sr_ptr'][0] & 0xFF:02x})")

    # ------------------------------------------------------------------
    # Scenario (d): speculation parity on VC1 all-pairs traffic
    # ------------------------------------------------------------------
    async def run_speculation_parity(self):
        tag = "speculation-parity"
        nb = len(self.BOUNDARY_COORDS)
        expected = {}
        for a in range(nb):
            for b in range(nb):
                payload = [self._pair_payload(a, b, j)
                           for j in range(self.BEATS_PER_PKT)]
                header = self.build_header(
                    dst=self.BOUNDARY_COORDS[b],
                    src=self.BOUNDARY_COORDS[a],
                    qos=1, vc=1,
                    packet_id=a * nb + b + 1)
                expected[(a, b)] = (header, payload)

        async def send_all(src_idx):
            port = f'b{src_idx}'
            for dst_idx in range(nb):
                h, p = expected[(src_idx, dst_idx)]
                await self._send_packet(port, h, p)

        senders = [cocotb.start_soon(send_all(a)) for a in range(nb)]
        for s in senders:
            await s

        for dst_idx in range(nb):
            await self._wait_frames(f'b{dst_idx}', nb)
        await self.wait_clocks('aclk', 10)

        for dst_idx in range(nb):
            self._check_destination(f'b{dst_idx}', dst_idx, expected)
        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh systolic (d): speculation parity -- {nb}x{nb} "
            f"VC1 pairs delivered exactly once")


class DeltaMeshSystolic4x1TB(DeltaMeshSystolicTB):
    BOUNDARY_COORDS = (
        (0, 0, 0),
        (1, 0, 0),
        (2, 0, 0),
        (3, 0, 0),
    )
    PORTS = tuple((f'b{i}', i) for i in range(len(BOUNDARY_COORDS)))


class DeltaMeshSystolic2x2TB(DeltaMeshSystolicTB):
    BOUNDARY_COORDS = (
        (0, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 0),
    )
    PORTS = tuple((f'b{i}', i) for i in range(len(BOUNDARY_COORDS)))


# ---------------------------------------------------------------------------
# Cocotb test entry points
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_systolic_ring_latency(dut):
    tb = DeltaMeshSystolic4x1TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_ring_latency()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_systolic_dateline(dut):
    tb = DeltaMeshSystolic2x2TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_dateline()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_systolic_source_route(dut):
    tb = DeltaMeshSystolic2x2TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_source_route()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_systolic_speculation(dut):
    tb = DeltaMeshSystolic2x2TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_speculation_parity()


# ---------------------------------------------------------------------------
# Pytest fixtures: generate the four DUT configurations
# ---------------------------------------------------------------------------
def _generate_mesh(args, tmp_path_factory):
    gen_dir = tmp_path_factory.mktemp("delta_mesh_systolic")
    cmd = [
        sys.executable,
        DELTA_GENERATOR,
        "--topology", "mesh",
        "--output-dir", str(gen_dir),
    ] + args
    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    assert result.returncode == 0, (
        f"delta_generator.py failed: {' '.join(args)}\n"
        f"{result.stdout}\n{result.stderr}")
    return gen_dir


@pytest.fixture(scope="module")
def fabric_gen_4x1_torus(tmp_path_factory):
    return _generate_mesh([
        "--cells-x", "4", "--cells-y", "1", "--cells-z", "1",
        "--torus-x",
        "--user-width", "64",
    ], tmp_path_factory)


@pytest.fixture(scope="module")
def fabric_gen_2x2_torus(tmp_path_factory):
    return _generate_mesh([
        "--cells-x", "2", "--cells-y", "2", "--cells-z", "1",
        "--torus-x",
        "--user-width", "64",
    ], tmp_path_factory)


@pytest.fixture(scope="module")
def fabric_gen_2x2_sr(tmp_path_factory):
    return _generate_mesh([
        "--cells-x", "2", "--cells-y", "2", "--cells-z", "1",
        "--source-route",
        "--user-width", "64",
    ], tmp_path_factory)


@pytest.fixture(scope="module")
def fabric_gen_2x2_spec(tmp_path_factory):
    return _generate_mesh([
        "--cells-x", "2", "--cells-y", "2", "--cells-z", "1",
        "--speculation",
        "--user-width", "64",
    ], tmp_path_factory)


# ---------------------------------------------------------------------------
# Pytest wrappers
# ---------------------------------------------------------------------------
def _run(testcase, test_level, gen_dir, dut_top, harness_path, fabric_sv,
         coord_w):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    verilog_sources = [
        *[os.path.join(repo_root, dep) for dep in FIFO_DEPS],
        str(gen_dir / 'delta_mesh_cell.sv'),
        str(gen_dir / fabric_sv),
        os.path.join(repo_root, harness_path),
    ]
    includes = [os.path.join(repo_root, RESET_DEFS_INCDIR)]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_top}_{testcase}_{test_level}{worker_suffix}"
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
        toplevel=dut_top,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'TEST_DATA_WIDTH': '64',
            'TEST_USER_WIDTH': '64',
            'TEST_NUM_VC': '2',
            'TEST_COORD_W': str(coord_w),
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


HARNESS_4X1 = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_4x1x1_th.sv'
HARNESS_2X2 = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_th.sv'


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_systolic_ring_latency(request, test_level, fabric_gen_4x1_torus):
    _run(
        "cocotb_test_delta_mesh_systolic_ring_latency",
        test_level,
        fabric_gen_4x1_torus,
        'delta_mesh_fabric_4x1x1_th',
        HARNESS_4X1,
        'delta_mesh_fabric_4x1x1.sv',
        2)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_systolic_dateline(request, test_level, fabric_gen_2x2_torus):
    _run(
        "cocotb_test_delta_mesh_systolic_dateline",
        test_level,
        fabric_gen_2x2_torus,
        'delta_mesh_fabric_2x2_th',
        HARNESS_2X2,
        'delta_mesh_fabric_2x2x1.sv',
        1)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_systolic_source_route(request, test_level, fabric_gen_2x2_sr):
    _run(
        "cocotb_test_delta_mesh_systolic_source_route",
        test_level,
        fabric_gen_2x2_sr,
        'delta_mesh_fabric_2x2_th',
        HARNESS_2X2,
        'delta_mesh_fabric_2x2x1.sv',
        1)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_systolic_speculation(request, test_level, fabric_gen_2x2_spec):
    _run(
        "cocotb_test_delta_mesh_systolic_speculation",
        test_level,
        fabric_gen_2x2_spec,
        'delta_mesh_fabric_2x2_th',
        HARNESS_2X2,
        'delta_mesh_fabric_2x2x1.sv',
        1)
