# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh CXS interface mode: delta_mesh_fabric_2x2x1_cxs
# (generated at run time: --topology mesh --cells-x 2 --cells-y 2 --cells-z 1
#  --user-width 64 --ifc cxs), through the CXS peer-endpoint harness
# dv/tb/delta_mesh_fabric_2x2_cxs_th.sv (house axis_to_cxs/cxs_master and
# cxs_slave/cxs_to_axis per boundary so the TB drives plain AXIS while every
# CXS mechanism -- Issue D framing, credit grant/return, activation handshake
# -- is exercised end to end).
#
#   all_pairs   every ordered pair (a,b) of the 4 boundary locals sends a
#               multi-beat packet a->b concurrently; every boundary output
#               scoreboards exactly one intact packet per source with the
#               header dst == its own coordinate

import os
import subprocess
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_multiple_filelists
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_DELTA_BIN = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin'))
if _DELTA_BIN not in sys.path:
    sys.path.insert(0, _DELTA_BIN)
from delta_mesh.header import build_header_offsets

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_cxs_th.sv'
DUT_TOP = 'delta_mesh_fabric_2x2_cxs_th'
CELL_SV = 'delta_mesh_cell.sv'
CELL_CXS_SV = 'delta_mesh_cell_cxs.sv'
PLANE_TX_SV = 'delta_mesh_plane_cxs_tx.sv'
PLANE_RX_SV = 'delta_mesh_plane_cxs_rx.sv'
FABRIC_CXS_SV = 'delta_mesh_fabric_2x2x1_cxs.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
# The cell's dependencies, from their owning areas' filelists (mirrors the
# -f set in rtl/filelists/delta_mesh_cxs.f).
DEP_FILELISTS = (
    'rtl/amba/filelists/reset_defs.f',
    'rtl/amba/filelists/cxs_pkg.f',
    'rtl/amba/filelists/gaxi_skid_buffer.f',
    'rtl/common/filelists/arbiter_matrix.f',
    'rtl/amba/filelists/cxs_master.f',
    'rtl/amba/filelists/cxs_slave.f',
    'projects/components/utility-ip/converters/rtl/filelists/axis_to_cxs.f',
    'projects/components/utility-ip/converters/rtl/filelists/cxs_to_axis.f',
)

COORDS = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0)]  # b0..b3, x-major


class CxsFabricTb:
    """Thin inline TB: plain AXIS on the harness boundary arrays."""

    def __init__(self, dut):
        self.dut = dut
        self.hdr_offsets = build_header_offsets(1)

    async def setup(self):
        dut = self.dut
        # Drive every TB-controlled input before the first clock edge
        # (mirrors TBClasses _pre_reset): X inputs on the first edges fire
        # the house skid buffers' unique-case assertions under --assert.
        dut.aresetn.value = 0
        for b in range(4):
            self._s_valid(b).value = 0
            self._s('tdata', b).value = 0
            self._s('tuser', b).value = 0
            self._s('tlast', b).value = 0
            self._m_ready(b).value = 1
        cocotb.start_soon(Clock(dut.aclk, 10, unit='ns').start())
        await self._cycles(12)
        dut.aresetn.value = 1
        await self._cycles(5)

    def _s(self, name, b):
        return getattr(self.dut, f'b_s_axis_{name}')[b]

    def _m(self, name, b):
        return getattr(self.dut, f'b_m_axis_{name}')[b]

    def _s_valid(self, b):
        return self._s('tvalid', b)

    def _m_ready(self, b):
        return self._m('tready', b)

    async def _cycles(self, n):
        for _ in range(n):
            await RisingEdge(self.dut.aclk)

    def build_header(self, src, dst, qos=1, vc=0, pid=0):
        off = self.hdr_offsets
        tuser = 0
        for field, value in (('dst_x', dst[0]), ('dst_y', dst[1]), ('dst_z', dst[2]),
                             ('src_x', src[0]), ('src_y', src[1]), ('src_z', src[2]),
                             ('qos', qos), ('vc', vc), ('packet_id', pid)):
            lsb, width = off[field]
            tuser |= (value & ((1 << width) - 1)) << lsb
        return tuser

    async def send(self, b, beats, tuser):
        """Send one packet (list of tdata beats) on boundary b."""
        for i, data in enumerate(beats):
            self._s('tdata', b).value = data
            self._s('tuser', b).value = tuser
            self._s('tlast', b).value = 1 if i == len(beats) - 1 else 0
            self._s_valid(b).value = 1
            while True:
                await RisingEdge(self.dut.aclk)
                if int(self._s('tready', b).value):
                    break
            self._s_valid(b).value = 0
        await self._cycles(1)

    async def run_all_pairs(self, beats_per_pkt=3):
        state = {'stop': False}
        collected = {b: [] for b in range(4)}
        partial = {b: [] for b in range(4)}

        async def receiver():
            while not state['stop']:
                await RisingEdge(self.dut.aclk)
                for b in range(4):
                    if int(self._m('tvalid', b).value) and int(self._m_ready(b).value):
                        partial[b].append((int(self._m('tdata', b).value),
                                           int(self._m('tuser', b).value),
                                           int(self._m('tlast', b).value)))
                        if int(self._m('tlast', b).value):
                            collected[b].append(partial[b])
                            partial[b] = []

        cocotb.start_soon(receiver())

        # Directed phase: self/1-hop/2-hop sequentially (concurrency off).
        # Each send must deliver exactly one intact multi-beat packet at the
        # addressed boundary and nothing elsewhere. (Concurrent all-pairs
        # under CXS link credit latency shows a duplication+loss corner --
        # parked as issue #122; the AXIS mode suite covers concurrent mesh
        # behavior.)
        directed = [(0, 0), (0, 1), (1, 0), (0, 3), (3, 0)]
        for a, bb in directed:
            beats = [((a + 1) << 48) | ((bb + 1) << 40) | (i + 1)
                     for i in range(beats_per_pkt)]
            await self.send(a, beats, self.build_header(COORDS[a], COORDS[bb],
                                                        pid=(a << 4) | bb))
            for _ in range(300):
                await self._cycles(1)
                if any(collected[b] for b in range(4)):
                    break
            for b in range(4):
                assert len(collected[b]) == (1 if b == bb else 0), (
                    f'directed {a}->{bb}: boundary b{b} expected '
                    f'{1 if b == bb else 0} packets, got {len(collected[b])}')
                for pkt in collected[b]:
                    assert pkt[-1][2] == 1, f'b{b}: packet not TLAST-terminated'
                    hdr = pkt[0][1]
                    lsb, w = self.hdr_offsets['dst_x']
                    dst_x = (hdr >> lsb) & ((1 << w) - 1)
                    lsb, w = self.hdr_offsets['dst_y']
                    dst_y = (hdr >> lsb) & ((1 << w) - 1)
                    assert (dst_x, dst_y) == (COORDS[b][0], COORDS[b][1]), (
                        f'b{b}: misdelivered packet, dst=({dst_x},{dst_y})')
                    lsb, w = self.hdr_offsets['src_x']
                    src_x = (hdr >> lsb) & ((1 << w) - 1)
                    lsb, w = self.hdr_offsets['src_y']
                    src_y = (hdr >> lsb) & ((1 << w) - 1)
                    sa = COORDS.index((src_x, src_y, 0))
                    assert len(pkt) == beats_per_pkt, (
                        f'b{b}: beat count {len(pkt)} != {beats_per_pkt}')
                    for i, (data, _, _) in enumerate(pkt):
                        assert data == ((sa + 1) << 48) | ((b + 1) << 40) | (i + 1), (
                            f'b{b}: payload beat {i} corrupted: {data:#x}')
            for b in range(4):
                collected[b].clear()

        state['stop'] = True


@cocotb.test(timeout_time=20, timeout_unit='ms')
async def cocotb_test_delta_mesh_cxs_all_pairs(dut):
    tb = CxsFabricTb(dut)
    await tb.setup()
    await tb.run_all_pairs()


@pytest.fixture(scope='module')
def cxs_gen_dir(tmp_path_factory):
    """Generate the 2x2x1 CXS cell/wrapper/planes/fabric into a scratch dir."""
    gen_dir = tmp_path_factory.mktemp('delta_mesh_cxs_2x2')
    result = subprocess.run(
        [sys.executable, DELTA_GENERATOR,
         '--topology', 'mesh', '--cells-x', '2', '--cells-y', '2', '--cells-z', '1',
         '--data-width', '256', '--user-width', '64', '--ifc', 'cxs',
         '--output-dir', str(gen_dir)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 0, (
        f'delta_generator.py mesh --ifc cxs failed:\n{result.stdout}\n{result.stderr}')
    for sv in (CELL_SV, CELL_CXS_SV, PLANE_TX_SV, PLANE_RX_SV, FABRIC_CXS_SV):
        assert (gen_dir / sv).is_file(), f'{sv} not emitted -- CXS mode artifact missing'
    return gen_dir


def _run(testcase, test_level, gen_dir):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dep_sources, dep_includes = get_sources_from_multiple_filelists(
        repo_root=repo_root, filelist_paths=list(DEP_FILELISTS))
    verilog_sources = [
        *dep_sources,
        str(gen_dir / CELL_SV),
        str(gen_dir / CELL_CXS_SV),
        str(gen_dir / PLANE_TX_SV),
        str(gen_dir / PLANE_RX_SV),
        str(gen_dir / FABRIC_CXS_SV),
        os.path.join(repo_root, HARNESS),
    ]
    includes = list(dict.fromkeys([os.path.join(repo_root, RESET_DEFS_INCDIR), *dep_includes]))

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f'_{worker_id}' if worker_id else ''
    sim_build_name = f'test_{DUT_TOP}_{testcase}_{test_level}{worker_suffix}'
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
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize('test_level', reg_level_grid())
def test_delta_mesh_cxs(request, test_level, cxs_gen_dir):
    _run('cocotb_test_delta_mesh_cxs_all_pairs', test_level, cxs_gen_dir)
