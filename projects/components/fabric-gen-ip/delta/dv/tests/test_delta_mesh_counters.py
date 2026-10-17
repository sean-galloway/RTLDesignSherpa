# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh: Ocelus counter suite + DFT 3-configuration test mode (Task 10)
# (generated at run time: --topology mesh --cells-x 2 --cells-y 2 --cells-z 1
#  --user-width 64), through the flattening harness
# dv/tb/delta_mesh_fabric_2x2_th.sv, with RDS-DV AXIS BFMs on all four
# boundary local ports.
#
#   counters_basic   read the eleven counter indices at reset, send one
#                    packet b0->b1, then read back and verify the
#                    deterministic counters (flits/packets in/out).
#   dft_patterns     enable each DFT pattern on a selected boundary cell and
#                    verify the fixed route + o_dft_active + clean disable.
#   counters_frozen  parameterized DUT with ENABLE_COUNTERS=0: counters stay
#                    at zero despite traffic.

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
from delta_mesh_tb import DeltaMeshModesTB

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_th.sv'
DUT_TOP = 'delta_mesh_fabric_2x2_th'
FABRIC_SV = 'delta_mesh_fabric_2x2x1.sv'
CELL_SV = 'delta_mesh_cell.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
# The cell's dependencies, from their owning areas' filelists (mirrors the
# -f set in rtl/filelists/delta_mesh.f).
DEP_FILELISTS = (
    'rtl/amba/filelists/reset_defs.f',
    'rtl/amba/filelists/gaxi_skid_buffer.f',
    'rtl/common/filelists/arbiter_matrix.f',
)

# Counter-bank index constants (mirror delta_mesh_cell localparams)
C_FLITS_IN = 0
C_FLITS_OUT = 1
C_PKTS_IN = 2
C_PKTS_OUT = 3
C_STALL_CYCLES = 4
C_CREDIT_STALL = 5
C_ERR_DROP = 6
C_MODE_ACKS = 7
C_BULK_STARVE = 8
C_SPEC_COMMITS = 9
C_SPEC_REVOKES = 10
COUNTER_BANK_BIT = 0x8000
DFT_INDEX = 0xD000


def _generate_fabric(gen_dir, no_counters=False):
    cmd = [
        sys.executable,
        DELTA_GENERATOR,
        "--topology", "mesh",
        "--cells-x", "2",
        "--cells-y", "2",
        "--cells-z", "1",
        "--user-width", "64",
        "--output-dir", str(gen_dir),
    ]
    if no_counters:
        cmd.append("--no-counters")
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, (
        f"delta_generator.py mesh failed:\n{result.stdout}\n{result.stderr}")
    assert (gen_dir / CELL_SV).is_file(), "mesh cell artifact not emitted"
    assert (gen_dir / FABRIC_SV).is_file(), "mesh fabric artifact not emitted"


@pytest.fixture(scope="module")
def fabric_gen_dir(tmp_path_factory):
    """Generate the 2x2x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_counters")
    _generate_fabric(gen_dir)
    return gen_dir


@pytest.fixture(scope="module")
def fabric_gen_dir_no_counters(tmp_path_factory):
    """Generate the 2x2x1 cell + fabric with ENABLE_COUNTERS=0."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_counters_nc")
    _generate_fabric(gen_dir, no_counters=True)
    return gen_dir


class DeltaMeshCountersTB(DeltaMeshModesTB):
    """TB for Task 10 counter bank + DFT mode on the 2x2x1 fabric."""

    async def _read_counter(self, bidx, counter_idx, tag):
        """Read one counter-bank entry; return the 32-bit counter value."""
        index = COUNTER_BANK_BIT | counter_idx
        coord = self.BOUNDARY_COORDS[bidx]
        header = self.build_config_header(False, self._next_pid(), coord)
        payload = index  # entry field = 0
        before = self._data_frame_count(f'b{bidx}')
        await self._send_packet(f'b{bidx}', header, [payload])
        frames = []
        for _ in range(2000):
            all_frames, _trailing = self._group_frames_lenient(
                self.slaves[f'b{bidx}'])
            frames = [f for f in all_frames if not self._is_ack_frame(f)]
            if len(frames) >= before + 1:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(f"{tag}: no counter response at b{bidx}")
        beat = frames[-1][0]
        got_data = int(beat.fields['data'])
        got_last = int(beat.fields.get('last', 0))
        got_user = int(beat.fields.get('user', 0))
        if got_last != 1 or got_user != 0:
            raise AssertionError(
                f"{tag}: counter response tlast/tuser {got_last}/{got_user}, "
                f"expected 1/0")
        return (got_data >> 16) & 0xFFFFFFFF

    async def _write_dft(self, bidx, enable, pattern, tag):
        """Write the DFT escape register on boundary bidx."""
        entry = ((pattern & 3) << 1) | (1 if enable else 0)
        await self._config_op(bidx, True, DFT_INDEX, entry, tag)

    def _dft_active(self, bidx):
        return int(getattr(self.dut, f'b{bidx}_dft_active').value)

    def _err(self, bidx):
        return int(getattr(self.dut, f'b{bidx}_err').value)

    async def run_counters_basic(self):
        """Send packets b0->b1 and verify deterministic counter deltas.

        Config reads themselves count as flits, so we snapshot the same
        subset of counters before and after the data traffic and compare
        deltas; the read overhead cancels out.
        """
        tag = "counters-basic"
        NPKTS = 3
        COUNTERS_TO_CHECK = (C_FLITS_IN, C_FLITS_OUT, C_PKTS_IN, C_PKTS_OUT,
                             C_ERR_DROP)

        async def snapshot(bidx):
            return {
                c: await self._read_counter(bidx, c, f"{tag}:snap-b{bidx}-{c}")
                for c in COUNTERS_TO_CHECK
            }

        before_b0 = await snapshot(0)
        before_b1 = await snapshot(1)

        header = self.build_header(
            dst=self.BOUNDARY_COORDS[1],
            src=self.BOUNDARY_COORDS[0],
            qos=1, packet_id=self._next_pid())
        payload = [0xC0FF_EE00_1234_5678]
        for _ in range(NPKTS):
            await self._send_packet('b0', header, payload)
        await self._wait_frames('b1', NPKTS)
        await self.wait_clocks('aclk', 10)

        after_b0 = await snapshot(0)
        after_b1 = await snapshot(1)

        # Each counter read itself adds one flit/packet, and all reads in
        # the final snapshot occur AFTER the data traffic, so the expected
        # delta is NPKTS plus the number of counters read in that snapshot.
        read_overhead = len(COUNTERS_TO_CHECK)
        for cnt in (C_FLITS_IN, C_FLITS_OUT, C_PKTS_IN, C_PKTS_OUT):
            delta_b0 = after_b0[cnt] - before_b0[cnt]
            if delta_b0 != NPKTS + read_overhead:
                raise AssertionError(
                    f"{tag}: b0 counter {cnt} delta {delta_b0}, "
                    f"expected {NPKTS + read_overhead}")
            delta_b1 = after_b1[cnt] - before_b1[cnt]
            if delta_b1 != NPKTS + read_overhead:
                raise AssertionError(
                    f"{tag}: b1 counter {cnt} delta {delta_b1}, "
                    f"expected {NPKTS + read_overhead}")

        if after_b0[C_ERR_DROP] != before_b0[C_ERR_DROP]:
            raise AssertionError(
                f"{tag}: b0 err_drop changed from {before_b0[C_ERR_DROP]} to "
                f"{after_b0[C_ERR_DROP]}")
        if after_b1[C_ERR_DROP] != before_b1[C_ERR_DROP]:
            raise AssertionError(
                f"{tag}: b1 err_drop changed from {before_b1[C_ERR_DROP]} to "
                f"{after_b1[C_ERR_DROP]}")

        self.log.info("delta mesh counters (a): basic flit/packet counter deltas passed")

    async def run_dft_patterns(self):
        """Exercise the three DFT routing patterns on a 2x2x1 fabric."""
        tag = "dft-patterns"

        # --- Pattern 0 (local loopback) on b0 ---
        # A packet b0->b1 is overridden to P_LOCAL, so it ejects at b0.
        await self._write_dft(0, True, 0, f"{tag}:enable-p0")
        if self._dft_active(0) != 1:
            raise AssertionError(f"{tag}: b0_dft_active low after enable")

        header_p0 = self.build_header(
            dst=self.BOUNDARY_COORDS[1],
            src=self.BOUNDARY_COORDS[0],
            qos=1, packet_id=self._next_pid())
        payload_p0 = [0xA0B0_0000_0000_0001]
        counts0 = self._data_frame_counts()
        await self._send_packet('b0', header_p0, payload_p0)
        await self._wait_frames('b0', counts0[0] + 1)
        await self.wait_clocks('aclk', 10)
        if self._data_frame_count('b1') != counts0[1]:
            raise AssertionError(
                f"{tag}: pattern 0 leaked to b1")
        self._match_expected_frames(
            'b0', 0, {(0, 0): (header_p0, payload_p0)},
            self._group_frames('b0', f"{tag}:p0")[counts0[0]:],
            f"{tag}:p0-loopback")

        # --- Pattern 1 (+X ring) on b0: packet to b1 exits +X cleanly ---
        await self._write_dft(0, True, 1, f"{tag}:enable-p1")
        if self._dft_active(0) != 1:
            raise AssertionError(f"{tag}: b0_dft_active low after p1 enable")

        header_p1 = self.build_header(
            dst=self.BOUNDARY_COORDS[1],
            src=self.BOUNDARY_COORDS[0],
            qos=1, packet_id=self._next_pid())
        payload_p1 = [0xA1B1_0000_0000_0001]
        counts1 = self._data_frame_counts()
        await self._send_packet('b0', header_p1, payload_p1)
        await self._wait_frames('b1', counts1[1] + 1)
        await self.wait_clocks('aclk', 10)
        if self._data_frame_count('b0') != counts1[0]:
            raise AssertionError(
                f"{tag}: pattern 1 did not leave b0 (got "
                f"{self._data_frame_count('b0')} frames, expected {counts1[0]})")
        self._match_expected_frames(
            'b1', 1, {(0, 1): (header_p1, payload_p1)},
            self._group_frames('b1', f"{tag}:p1")[counts1[1]:],
            f"{tag}:p1-xpos")

        # --- Pattern 1 drop at X-max edge on b1 ---
        # Local delivery has precedence, so use a non-local dst (b3) that
        # pattern 1 tries to route +X; b1 is already at X-max, so it drops.
        err_before = self._err(1)
        await self._write_dft(1, True, 1, f"{tag}:enable-p1-b1")
        header_p1_drop = self.build_header(
            dst=self.BOUNDARY_COORDS[3],
            src=self.BOUNDARY_COORDS[1],
            qos=1, packet_id=self._next_pid())
        payload_p1_drop = [0xA1D1_0000_0000_0001]
        counts1_drop = self._data_frame_counts()
        await self._send_packet('b1', header_p1_drop, payload_p1_drop)
        for _ in range(200):
            await RisingEdge(self.aclk)
            if self._err(1) != err_before:
                break
        else:
            raise AssertionError(f"{tag}: b1 err_drop did not increment for p1 drop")
        await self.wait_clocks('aclk', 10)
        if self._data_frame_count('b1') != counts1_drop[1]:
            raise AssertionError(
                f"{tag}: pattern-1 drop leaked as a data frame at b1")
        if self._data_frame_count('b3') != counts1_drop[3]:
            raise AssertionError(
                f"{tag}: pattern-1 drop leaked to b3")

        # --- Pattern 2 (DOR to root) on b3 ---
        # Local delivery precedence: a self-destined packet stays local even
        # when pattern 2 is enabled. This also verifies the override does not
        # accidentally drag a local packet toward root.
        await self._write_dft(3, True, 2, f"{tag}:enable-p2")
        if self._dft_active(3) != 1:
            raise AssertionError(f"{tag}: b3_dft_active low after p2 enable")

        header_p2 = self.build_header(
            dst=self.BOUNDARY_COORDS[3],
            src=self.BOUNDARY_COORDS[3],
            qos=1, packet_id=self._next_pid())
        payload_p2 = [0xA2B2_0000_0000_0001]
        counts2 = self._data_frame_counts()
        await self._send_packet('b3', header_p2, payload_p2)
        await self._wait_frames('b3', counts2[3] + 1)
        await self.wait_clocks('aclk', 10)
        self._match_expected_frames(
            'b3', 3, {(3, 3): (header_p2, payload_p2)},
            self._group_frames('b3', f"{tag}:p2")[counts2[3]:],
            f"{tag}:p2-local-precedence")

        # --- Pattern 2 non-local DOR-to-root override proof ---
        # Install a custom table entry at b3 that would normally deliver a
        # b3 -> b0 packet locally. With DFT pattern 2 enabled, the override
        # must ignore that entry and route DOR toward (0,0,0): b3 -> b2 -> b0.
        # 2x2x1 coords: COORD_W=1, table index = {qos[1:0], z, y, x}.
        rt_index_b3_b0 = (1 << 3) | 0  # qos=1, dst=(0,0,0)
        rt_entry_local = 1 << 8        # P_LOCAL, VC0
        rt_entry_xneg = 1 << 0         # P_X_NEG, VC0 (default DOR restore)
        await self._config_op(3, True, rt_index_b3_b0, rt_entry_local,
                              f"{tag}:b3-rt-b0-local")

        header_p2nl = self.build_header(
            dst=self.BOUNDARY_COORDS[0],
            src=self.BOUNDARY_COORDS[3],
            qos=1, packet_id=self._next_pid())
        payload_p2nl = [0xA2C0_0000_0000_0001]
        counts2nl = self._data_frame_counts()
        await self._send_packet('b3', header_p2nl, payload_p2nl)
        await self._wait_frames('b0', counts2nl[0] + 1)
        await self.wait_clocks('aclk', 10)
        self._match_expected_frames(
            'b0', 0, {(3, 0): (header_p2nl, payload_p2nl)},
            self._group_frames('b0', f"{tag}:p2nl")[counts2nl[0]:],
            f"{tag}:p2-root-override")

        # Restore default DOR entry so later tests are not contaminated.
        await self._config_op(3, True, rt_index_b3_b0, rt_entry_xneg,
                              f"{tag}:b3-rt-b0-restore")

        # --- Disable DFT on all cells and verify normal traffic resumes ---
        for bidx in range(len(self.BOUNDARY_COORDS)):
            await self._write_dft(bidx, False, 0, f"{tag}:disable-b{bidx}")
            if self._dft_active(bidx) != 0:
                raise AssertionError(
                    f"{tag}: b{bidx}_dft_active high after disable")

        header_normal = self.build_header(
            dst=self.BOUNDARY_COORDS[3],
            src=self.BOUNDARY_COORDS[0],
            qos=1, packet_id=self._next_pid())
        payload_normal = [0xC0DE_0000_0000_0001]
        countsN = self._data_frame_counts()
        await self._send_packet('b0', header_normal, payload_normal)
        await self._wait_frames('b3', countsN[3] + 1)
        await self.wait_clocks('aclk', 10)
        self._match_expected_frames(
            'b3', 3, {(0, 3): (header_normal, payload_normal)},
            self._group_frames('b3', f"{tag}:normal")[countsN[3]:],
            f"{tag}:normal-resume")

        self.log.info("delta mesh counters (b): DFT patterns + clean exit passed")

    async def run_counters_frozen(self):
        """With ENABLE_COUNTERS=0 every counter read returns zero."""
        tag = "counters-frozen"
        # Sanity: send a packet and verify it delivers, but counters stay 0.
        header = self.build_header(
            dst=self.BOUNDARY_COORDS[1],
            src=self.BOUNDARY_COORDS[0],
            qos=1, packet_id=self._next_pid())
        payload = [0xF0EE_0000_0000_0001]
        await self._send_packet('b0', header, payload)
        await self._wait_frames('b1', 1)
        await self.wait_clocks('aclk', 10)

        for idx in range(11):
            val = await self._read_counter(0, idx, f"{tag}:b0-{idx}")
            if val != 0:
                raise AssertionError(
                    f"{tag}: counter {idx} at b0 == {val}, expected 0 with "
                    f"ENABLE_COUNTERS=0")
            val = await self._read_counter(1, idx, f"{tag}:b1-{idx}")
            if val != 0:
                raise AssertionError(
                    f"{tag}: counter {idx} at b1 == {val}, expected 0 with "
                    f"ENABLE_COUNTERS=0")

        self.log.info("delta mesh counters (c): ENABLE_COUNTERS=0 freeze passed")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_counters_basic(dut):
    tb = DeltaMeshCountersTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_counters_basic()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_dft_patterns(dut):
    tb = DeltaMeshCountersTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_dft_patterns()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_counters_frozen(dut):
    tb = DeltaMeshCountersTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_counters_frozen()


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
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'TEST_COORD_W': '1',
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_counters_basic(request, test_level, fabric_gen_dir):
    _run("cocotb_test_delta_mesh_counters_basic", test_level, fabric_gen_dir)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_dft_patterns(request, test_level, fabric_gen_dir):
    _run("cocotb_test_delta_mesh_dft_patterns", test_level, fabric_gen_dir)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_counters_frozen(request, test_level, fabric_gen_dir_no_counters):
    _run("cocotb_test_delta_mesh_counters_frozen", test_level, fabric_gen_dir_no_counters)
