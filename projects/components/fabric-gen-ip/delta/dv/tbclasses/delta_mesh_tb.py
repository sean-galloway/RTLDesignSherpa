# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: delta_mesh_tb
# Purpose: TB for the delta mesh cell (delta_mesh_cell) via its flattening
#          harness dv/tb/delta_mesh_cell_th.sv.
#
# Subsystem: delta (dv)
#
# Author: sean galloway
# Created: 2026-10-14

"""
Delta mesh cell TB, default-DOR flavor.

Binds one RDS-DV AXIS master BFM to every cell input port
(``<port>_s_axis_``) and one AXIS slave BFM to every output port
(``<port>_m_axis_``) of the flattening harness ``dv/tb/delta_mesh_cell_th.sv``.
The harness instantiates ``delta_mesh_cell`` at POS (1,1,0) of a 4x4x1 grid
with DATA_WIDTH=64, USER_WIDTH=64, COORD_W=2.

The DUT carries no TSTRB/TID/TDEST: routing rides in the TUSER head-flit
header (see delta_mesh.header), so the BFMs bind those fields as optional.

What this TB checks (power-on default DOR, no config write):

- a packet injected at the local port with dst (3,0,0) leaves on P_X_POS
  (dst_x > POS_X), head-flit header and payload beats intact, in order;
- a packet arriving on P_X_NEG from the (0,1,0) neighbor -- src (0,1,0),
  dst (1,0,0) -- leaves on P_Y_NEG (dst_y < POS_Y, the hop toward y=0);
- every other output port stays silent for the whole run.
"""

import os
import random
import sys

import cocotb
from cocotb.triggers import RisingEdge

_here = os.path.dirname(os.path.abspath(__file__))
_DELTA_BIN = os.path.abspath(os.path.join(_here, '..', '..', 'bin'))
for _p in (_DELTA_BIN,):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from CocoTBFramework.components.axis4.axis_factories import (
    create_axis_master,
    create_axis_slave,
)
from CocoTBFramework.components.axis4.axis_packet import AXISPacket
from delta_mesh.header import build_header_offsets
from delta_mesh.tables import (
    P_DIA,
    P_DIA2,
    P_LOCAL,
    P_X_POS,
    P_Y_POS,
    table_index,
)
from TBClasses.shared.tbbase import TBBase


class DeltaMeshCellTB(TBBase):
    """TB for delta_mesh_cell (default DOR) via its harness."""

    # Harness port prefixes, index == cell port id (Task 6c: P_DIA at
    # index 6, P_DIA2 at 7, P_LOCAL moved to 8):
    #   0 = P_X_NEG, 1 = P_X_POS, 2 = P_Y_NEG, 3 = P_Y_POS,
    #   4 = P_Z_NEG, 5 = P_Z_POS, 6 = P_DIA, 7 = P_DIA2, 8 = P_LOCAL
    PORTS = (
        ('xneg', 0),
        ('xpos', 1),
        ('yneg', 2),
        ('ypos', 3),
        ('zneg', 4),
        ('zpos', 5),
        ('dia', 6),
        ('dia2', 7),
        ('local', 8),
    )

    def __init__(self, dut):
        super().__init__(dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '64'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '64'))
        self.COORD_W = self.convert_to_int(os.environ.get('TEST_COORD_W', '2'))
        self.POS = (
            self.convert_to_int(os.environ.get('TEST_POS_X', '1')),
            self.convert_to_int(os.environ.get('TEST_POS_Y', '1')),
            self.convert_to_int(os.environ.get('TEST_POS_Z', '0')),
        )
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        # Depth knobs: packets per scenario, beats (flits) per packet
        self.PKTS_PER_SCENARIO = {'gate': 1, 'func': 3, 'full': 8}[self.TEST_LEVEL]
        self.BEATS_PER_PKT = {'gate': 2, 'func': 3, 'full': 4}[self.TEST_LEVEL]
        self.rng = random.Random(self.SEED)
        self.hdr_offsets = build_header_offsets(self.COORD_W)

        self.aclk = dut.aclk
        self.aresetn = dut.aresetn
        self.masters = {}
        self.slaves = {}

        self.log.info(f"delta mesh cell TB: DW={self.DATA_WIDTH} UW={self.USER_WIDTH} "
                      f"COORD_W={self.COORD_W} POS={self.POS} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # Mandatory TB methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self._init_inputs()
        self._build_bfms()
        await self.assert_reset()
        await self.deassert_reset()

    async def assert_reset(self):
        self.aresetn.value = 0
        await self.wait_clocks('aclk', 5)

    async def deassert_reset(self):
        self.aresetn.value = 1
        await self.wait_clocks('aclk', 3)

    # ------------------------------------------------------------------
    # Setup
    # ------------------------------------------------------------------
    def _init_inputs(self):
        for name, _ in self.PORTS:
            dut = self.dut
            getattr(dut, f"{name}_s_axis_tvalid").value = 0
            getattr(dut, f"{name}_s_axis_tdata").value = 0
            getattr(dut, f"{name}_s_axis_tlast").value = 0
            getattr(dut, f"{name}_s_axis_tuser").value = 0
            getattr(dut, f"{name}_m_axis_tready").value = 1
            # Credits: all-ones = both VC levels set (max credits). The
            # fabric harness ties its boundary credits internally, so only
            # drive the signal when the harness exposes it.
            credit = getattr(dut, f"{name}_s_credit", None)
            if credit is not None:
                credit.value = (1 << 2) - 1  # NUM_VC=2: 2'b11 per port

    def _build_bfms(self):
        # The cell carries no TSTRB/TID/TDEST: id_width=0/dest_width=0 drop
        # those fields from the config entirely; 'strb' is bound as optional
        # so a missing signal reads 0 forever (header rides in TUSER).
        for name, _ in self.PORTS:
            self.masters[name] = create_axis_master(
                dut=self.dut,
                clock=self.dut.aclk,
                prefix=f"{name}_s_axis_",
                data_width=self.DATA_WIDTH,
                id_width=0,
                dest_width=0,
                user_width=self.USER_WIDTH,
                log=self.log,
                optional_fields=('strb',),
            )['interface']
            self.slaves[name] = create_axis_slave(
                dut=self.dut,
                clock=self.dut.aclk,
                prefix=f"{name}_m_axis_",
                data_width=self.DATA_WIDTH,
                id_width=0,
                dest_width=0,
                user_width=self.USER_WIDTH,
                log=self.log,
                ready_policy='always',
                optional_fields=('strb',),
            )['interface']

    # ------------------------------------------------------------------
    # Header / packet helpers
    # ------------------------------------------------------------------
    def build_header(self, dst, src, qos=0, vc=0, packet_id=0, sr_ptr=0,
                     mcast=0):
        """Pack a head-flit header int per delta_mesh.header layout."""
        hdr = 0
        for value, fields in ((dst, ('dst_x', 'dst_y', 'dst_z')),
                              (src, ('src_x', 'src_y', 'src_z'))):
            for coord, field in zip(value, fields):
                lo, width = self.hdr_offsets[field]
                hdr |= (coord & ((1 << width) - 1)) << lo
        for field, value in (('qos', qos), ('mcast', mcast), ('vc', vc),
                             ('sr_ptr', sr_ptr), ('packet_id', packet_id)):
            lo, width = self.hdr_offsets[field]
            hdr |= (value & ((1 << width) - 1)) << lo
        return hdr

    async def _send_packet(self, port, header, payload):
        """Send one packet: head beat (header in TUSER) + payload beats."""
        master = self.masters[port]
        n = len(payload)
        for i, data in enumerate(payload):
            last = 1 if i == n - 1 else 0
            user = header if i == 0 else 0
            await master.send_single_beat(data=data, last=last, user=user)

    async def _expect_packet(self, port, header, payload, exp_frames, tag):
        """Wait for one packet at `port` and verify header + payload intact.

        The send already drained before we are called, so poll the slave's
        cumulative frame count instead of waiting for a new-frame edge.
        """
        slave = self.slaves[port]
        n = len(payload)
        for _ in range(1000):
            if slave.frames_received >= exp_frames:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(f"{tag}: no frame observed on port '{port}'")
        beats = slave.get_observed_packets()[-n:]
        if len(beats) != n:
            raise AssertionError(f"{tag}: expected {n} beats on '{port}', got {len(beats)}")
        for i, (beat, exp_data) in enumerate(zip(beats, payload)):
            got_data = int(beat.fields['data'])
            got_user = int(beat.fields.get('user', 0))
            exp_last = 1 if i == n - 1 else 0
            got_last = int(beat.fields.get('last', 0))
            if got_data != exp_data:
                raise AssertionError(
                    f"{tag}: beat {i} data mismatch on '{port}': "
                    f"got 0x{got_data:x}, expected 0x{exp_data:x}")
            if got_last != exp_last:
                raise AssertionError(
                    f"{tag}: beat {i} tlast mismatch on '{port}': "
                    f"got {got_last}, expected {exp_last}")
            exp_user = header if i == 0 else 0
            if got_user != exp_user:
                raise AssertionError(
                    f"{tag}: beat {i} tuser mismatch on '{port}': "
                    f"got 0x{got_user:x}, expected 0x{exp_user:x}")

    def _check_idle_ports(self, active_ports, tag):
        for name, _ in self.PORTS:
            if name in active_ports:
                continue
            slave = self.slaves[name]
            if slave.packets_received != 0:
                raise AssertionError(
                    f"{tag}: port '{name}' observed {slave.packets_received} "
                    f"beats, expected 0 (misrouted flit)")

    def _random_payload(self):
        return [self.rng.getrandbits(self.DATA_WIDTH)
                for _ in range(self.BEATS_PER_PKT)]

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------
    async def run_dor_routing(self):
        # Scenario A (brief: dst (3,0,0) at POS (1,1,0) -> first DOR hop
        # P_X_POS): injected at the local port.
        header_a = self.build_header(dst=(3, 0, 0), src=self.POS, packet_id=1)
        for pkt in range(self.PKTS_PER_SCENARIO):
            payload = self._random_payload()
            await self._send_packet('local', header_a, payload)
            await self._expect_packet('xpos', header_a, payload, pkt + 1,
                                      tag=f"A{pkt}: local->xpos dst(3,0,0)")

        # Scenario B: a flit that arrived from the (0,1,0) neighbor on
        # P_X_NEG -- src (0,1,0) -- bound for dst (1,0,0) takes the second
        # hop toward y=0 out P_Y_NEG (dst_y < POS_Y, x already equal).
        header_b = self.build_header(dst=(1, 0, 0), src=(0, 1, 0), packet_id=2)
        for pkt in range(self.PKTS_PER_SCENARIO):
            payload = self._random_payload()
            await self._send_packet('xneg', header_b, payload)
            await self._expect_packet('yneg', header_b, payload, pkt + 1,
                                      tag=f"B{pkt}: xneg->yneg dst(1,0,0)")

        # Drain, then every non-target port must have stayed silent.
        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({'xpos', 'yneg'}, tag="idle")
        self.log.info("delta mesh cell DOR routing: all scenarios passed")


class DeltaMeshFabricTB(DeltaMeshCellTB):
    """TB for a delta mesh fabric top (all-pairs over the boundary locals).

    Binds one RDS-DV AXIS master BFM to every boundary local input of the
    fabric harness (``b<i>_s_axis_``) and one AXIS slave BFM to every
    boundary local output (``b<i>_m_axis_``). Derived from the cell TB: the
    BFM construction helpers key off ``self.PORTS``, so the subclass only
    redefines the port table, the boundary coordinate map, and the scenario.

    The default harness is ``dv/tb/delta_mesh_fabric_2x2_th.sv`` (2x2x1,
    NUM_BOUNDARY=4). Boundary index -> coordinate map is x-major, then y,
    then z (documented in the fabric's header comment); with Z=1 both z
    faces are boundary so every cell qualifies:
        b0 = (0,0,0), b1 = (1,0,0), b2 = (0,1,0), b3 = (1,1,0)
    """

    # Harness boundary port prefixes, index == fabric boundary index.
    BOUNDARY_COORDS = (
        (0, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 0),
    )
    PORTS = tuple((f'b{i}', i) for i in range(len(BOUNDARY_COORDS)))

    def _pair_payload(self, a, b, beat):
        """Globally unique payload word per (source, destination, beat).

        The tag travels in the data field, so a beat delivered to any wrong
        boundary -- or out of order within its packet -- fails the match on
        data alone.
        """
        return ((0xD1A << 48) | (a << 40) | (b << 32)
                | (beat << 24) | 0xA5A5)

    async def _wait_frames(self, port, n):
        """Poll a slave BFM until it has counted `n` complete frames."""
        slave = self.slaves[port]
        for _ in range(4000):
            if slave.frames_received >= n:
                return
            await RisingEdge(self.aclk)
        raise AssertionError(
            f"fabric all-pairs: boundary '{port}' saw {slave.frames_received} "
            f"frames, expected {n}")

    def _group_frames(self, port, tag):
        """Group a boundary slave's observed beats into TLAST-delimited
        frames (trailing beats without tlast raise)."""
        beats = self.slaves[port].get_observed_packets()
        frames = []
        current = []
        for beat in beats:
            current.append(beat)
            if int(beat.fields.get('last', 0)):
                frames.append(current)
                current = []
        if current:
            raise AssertionError(
                f"{tag}: boundary ended mid-packet "
                f"({len(current)} trailing beats without tlast)")
        return frames

    def _match_expected_frames(self, port, dst_idx, exp_pairs, frames, tag):
        """Match frames against {(src_idx, dst_idx): (header, payload), ...}.

        Arrival order between packets is arbitrary (output contention at
        interior cells); order within a frame must be exactly as sent.
        Distinct headers per packet catch duplication.
        """
        by_head = {}
        for frame in frames:
            head_user = int(frame[0].fields.get('user', 0))
            if head_user in by_head:
                raise AssertionError(
                    f"{tag}: boundary {dst_idx} received two "
                    f"packets with header 0x{head_user:x} (duplicate)")
            by_head[head_user] = frame

        for (src_idx, dst), (header, payload) in exp_pairs.items():
            frame = by_head.get(header)
            tag2 = f"b{src_idx}->b{dst}"
            if frame is None:
                raise AssertionError(
                    f"{tag}: packet {tag2} never arrived at "
                    f"boundary {dst_idx}")
            if len(frame) != len(payload):
                raise AssertionError(
                    f"{tag}: {tag2} delivered {len(frame)} beats, "
                    f"expected {len(payload)}")
            for i, (beat, exp_data) in enumerate(zip(frame, payload)):
                got_data = int(beat.fields['data'])
                got_user = int(beat.fields.get('user', 0))
                exp_last = 1 if i == len(payload) - 1 else 0
                got_last = int(beat.fields.get('last', 0))
                if got_data != exp_data:
                    raise AssertionError(
                        f"{tag}: {tag2} beat {i} data mismatch: "
                        f"got 0x{got_data:x}, expected 0x{exp_data:x}")
                if got_last != exp_last:
                    raise AssertionError(
                        f"{tag}: {tag2} beat {i} tlast mismatch: "
                        f"got {got_last}, expected {exp_last}")
                exp_user = header if i == 0 else 0
                if got_user != exp_user:
                    raise AssertionError(
                        f"{tag}: {tag2} beat {i} tuser mismatch: "
                        f"got 0x{got_user:x}, expected 0x{exp_user:x}")

    def _check_destination(self, port, dst_idx, expected):
        """Scoreboard one boundary output against the expected packets."""
        nb = len(self.BOUNDARY_COORDS)
        # Match frames to expectations by the head-flit header in TUSER;
        # duplicate heads mean a packet was duplicated, not just reordered.
        frames = self._group_frames(port, "fabric all-pairs")
        if len(frames) != nb:
            heads = sorted(int(f[0].fields.get('user', 0)) for f in frames)
            raise AssertionError(
                f"fabric all-pairs: boundary {dst_idx} received {len(frames)} "
                f"packets, expected {nb} (one per source); heads: "
                + ", ".join(f"0x{h:x}" for h in heads))
        exp = {(src_idx, dst_idx): expected[(src_idx, dst_idx)]
               for src_idx in range(nb)}
        self._match_expected_frames(port, dst_idx, exp, frames,
                                    "fabric all-pairs")

    async def run_all_pairs(self):
        """Every ordered pair (a,b) of boundary locals, driven concurrently.

        One sender task per source boundary injects its packets back to back
        (b = 0..NUM_BOUNDARY-1, self-pair included: dst == own coordinate
        delivers on the same cell's local port, the dst==POS DOR case); the
        four senders run concurrently, so interior outputs contend. After
        all sends drain, every boundary output must hold exactly one intact
        packet per source. Multi-hop pairs (every a!=b on 2x2x1, e.g.
        b0=(0,0,0) -> b3=(1,1,0) via the (1,0,0)/(0,1,0) interior hop)
        exercise the DOR path across a neighbor cell.
        """
        nb = len(self.BOUNDARY_COORDS)
        expected = {}
        for a in range(nb):
            for b in range(nb):
                payload = [self._pair_payload(a, b, j)
                           for j in range(self.BEATS_PER_PKT)]
                # Data rides QoS class 1 (latency); class 0 is the config
                # class (plan-pinned): a class-0 packet addressed to the
                # cell itself is intercepted as a config transaction, so
                # self-pairs (dst == own coordinate) must not use it.
                header = self.build_header(
                    dst=self.BOUNDARY_COORDS[b],
                    src=self.BOUNDARY_COORDS[a],
                    qos=1,
                    packet_id=a * nb + b + 1)
                expected[(a, b)] = (header, payload)

        async def send_all(src_idx):
            port = f'b{src_idx}'
            for dst_idx in range(nb):
                header, payload = expected[(src_idx, dst_idx)]
                await self._send_packet(port, header, payload)

        senders = [cocotb.start_soon(send_all(a)) for a in range(nb)]
        for sender in senders:
            await sender

        for dst_idx in range(nb):
            await self._wait_frames(f'b{dst_idx}', nb)
        await self.wait_clocks('aclk', 10)

        for dst_idx in range(nb):
            self._check_destination(f'b{dst_idx}', dst_idx, expected)
        self.log.info(
            f"delta mesh fabric all-pairs: {nb}x{nb} ordered pairs passed")


class DeltaMeshFlowControlTB(DeltaMeshCellTB):
    """TB for delta_mesh_cell flow control: per-VC input buffers, credit
    sideband protocol, and packet atomicity under downstream exhaustion.

    Derived from the cell TB. The harness exposes per-port s_credit inputs
    (one credit level bit per VC); the test drives them to model the
    downstream neighbor's advertised credits, so credit exhaustion and
    return are directly controllable. Scenario beat/packet counts are
    fixed (not TEST_LEVEL-scaled): the brief pins exact fill depths.

    Scenario traffic: all packets are VC0 with dst (3,0,0) at POS (1,1,0),
    whose first DOR hop is P_X_POS -- the 'xpos' output is the link under
    test.
    """

    XPOS = 'xpos'

    # ------------------------------------------------------------------
    # Credit / monitoring helpers
    # ------------------------------------------------------------------
    def _drive_credit(self, port, value):
        getattr(self.dut, f"{port}_s_credit").value = value

    async def _send_burst(self, port, packets):
        """Send whole packets back-to-back with zero producer bubble.

        `packets` is a list of (header, payload) pairs. Every beat becomes
        one AXISPacket and the whole list is queued on the master's
        transmit pipeline in one shot (send_burst), so beats stream
        contiguously -- per-beat `send()` would drain the pipeline between
        beats and add producer-side gaps the scenario must not measure.
        """
        master = self.masters[port]
        beats = []
        for header, payload in packets:
            n = len(payload)
            for i, data in enumerate(payload):
                beat = AXISPacket(field_config=master.field_config)
                beat.data = data
                beat.last = 1 if i == n - 1 else 0
                beat.user = header if i == 0 else 0
                if 'strb' in master.field_config:
                    beat.strb = (1 << master.field_config['strb'].bits) - 1
                beats.append(beat)
        await master.send_burst(beats)

    async def _wait_handshakes(self, port, n, tag):
        """Wait until `n` tvalid&tready handshakes are observed on a port."""
        v = getattr(self.dut, f"{port}_m_axis_tvalid")
        r = getattr(self.dut, f"{port}_m_axis_tready")
        for _ in range(2000):
            await RisingEdge(self.aclk)
            if int(v.value) and int(r.value):
                n -= 1
                if n == 0:
                    return
        raise AssertionError(f"{tag}: timed out waiting for {n} handshakes")

    async def _wait_beats(self, port, n, tag):
        """Poll a slave BFM until it has counted `n` beats."""
        slave = self.slaves[port]
        for _ in range(2000):
            if slave.packets_received >= n:
                return
            await RisingEdge(self.aclk)
        raise AssertionError(
            f"{tag}: port '{port}' saw {slave.packets_received} beats, "
            f"expected {n}")

    def _frames_at(self, port):
        """Group a slave's observed beats into TLAST-delimited frames."""
        frames = []
        current = []
        for beat in self.slaves[port].get_observed_packets():
            current.append(beat)
            if int(beat.fields.get('last', 0)):
                frames.append(current)
                current = []
        if current:
            raise AssertionError(
                f"flow control: port '{port}' ended mid-packet "
                f"({len(current)} trailing beats without tlast)")
        return frames

    def _verify_frames(self, frames, expected, tag):
        """Scoreboard frames against [(header, payload), ...].

        Arrival order between packets is arbitrary; within a frame beats
        must be exact and in order. Distinct headers per packet catch
        duplication.
        """
        if len(frames) != len(expected):
            raise AssertionError(
                f"{tag}: got {len(frames)} frames, expected {len(expected)}")
        by_head = {}
        for frame in frames:
            head = int(frame[0].fields.get('user', 0))
            if head in by_head:
                raise AssertionError(
                    f"{tag}: two frames with header 0x{head:x} (duplicate)")
            by_head[head] = frame
        for header, payload in expected:
            label = f"{tag}: packet 0x{header:x}"
            frame = by_head.get(header)
            if frame is None:
                raise AssertionError(f"{label} never arrived")
            if len(frame) != len(payload):
                raise AssertionError(
                    f"{label}: {len(frame)} beats, expected {len(payload)}")
            for i, (beat, exp) in enumerate(zip(frame, payload)):
                got_data = int(beat.fields['data'])
                got_last = int(beat.fields.get('last', 0))
                exp_last = 1 if i == len(payload) - 1 else 0
                if got_data != exp:
                    raise AssertionError(
                        f"{label} beat {i}: got 0x{got_data:x}, "
                        f"expected 0x{exp:x}")
                if got_last != exp_last:
                    raise AssertionError(
                        f"{label} beat {i}: tlast {got_last}, "
                        f"expected {exp_last}")

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------
    async def run_credit_exhaustion_and_drain(self):
        """(a) Downstream credits exhausted: producer stalls once the input
        FIFO (DEPTH=4) absorbs 4 beats, nothing is presented on the
        credit-less link, nothing is dropped; releasing credits drains the
        payload complete and in order."""
        tag = "exhaustion"
        BEATS = 6  # > input FIFO DEPTH (4): the FIFO must fill and stall
        header = self.build_header(dst=(3, 0, 0), src=self.POS, packet_id=0xA1)
        payload = [self.rng.getrandbits(self.DATA_WIDTH) for _ in range(BEATS)]

        self._drive_credit(self.XPOS, 0)
        sender = cocotb.start_soon(self._send_packet('local', header, payload))
        v = self.dut.local_s_axis_tvalid
        r = self.dut.local_s_axis_tready
        accepted = 0
        for _ in range(20):
            await RisingEdge(self.aclk)
            if int(v.value) and int(r.value):
                accepted += 1
        if accepted != 4:
            raise AssertionError(
                f"{tag}: producer accepted {accepted} beats with the xpos "
                f"link out of credits, expected 4 (input FIFO DEPTH)")
        if self.slaves[self.XPOS].packets_received != 0:
            raise AssertionError(
                f"{tag}: flits delivered on 'xpos' with zero credits")
        if int(self.dut.xpos_m_axis_tvalid.value) != 0:
            raise AssertionError(
                f"{tag}: tvalid raised on 'xpos' with zero credits")
        credit = int(self.dut.local_m_credit.value)
        if credit != 0b10:
            raise AssertionError(
                f"{tag}: m_credit[local] == 2'b{credit:02b}, expected "
                f"2'b10 (VC0 FIFO full, VC1 empty)")

        self._drive_credit(self.XPOS, (1 << 2) - 1)
        await sender
        await self._wait_beats(self.XPOS, BEATS, tag)
        await self.wait_clocks('aclk', 4)
        self._verify_frames(self._frames_at(self.XPOS), [(header, payload)], tag)
        credit = int(self.dut.local_m_credit.value)
        if credit != 0b11:
            raise AssertionError(
                f"{tag}: m_credit[local] == 2'b{credit:02b} after drain, "
                f"expected 2'b11 (both FIFOs empty)")
        self.log.info("flow control (a): credit exhaustion stall + drain passed")

    async def run_atomicity_one_credit_left(self):
        """(b) Review Focus #3: exactly one flit of credit space left on the
        xpos link; two sources start 4-beat packets to the same output.
        The granted packet holds the output; no interleaving, no loss."""
        tag = "atomicity"
        BEATS = 4
        # Both packets: dst (3,0,0) at POS (1,1,0) -> first DOR hop P_X_POS,
        # so both sources contend for the 'xpos' output.
        header_a = self.build_header(dst=(3, 0, 0), src=(0, 1, 0), packet_id=0xB1)
        header_b = self.build_header(dst=(3, 0, 0), src=self.POS, packet_id=0xB2)
        payload_a = [self.rng.getrandbits(self.DATA_WIDTH) for _ in range(BEATS)]
        payload_b = [self.rng.getrandbits(self.DATA_WIDTH) for _ in range(BEATS)]

        self._drive_credit(self.XPOS, 0b01)  # VC0: one space; VC1: none
        ta = cocotb.start_soon(self._send_packet('xneg', header_a, payload_a))
        tb = cocotb.start_soon(self._send_packet('local', header_b, payload_b))
        await self._wait_handshakes(self.XPOS, 1, tag)
        # The single free slot is consumed by whichever head won the grant;
        # the link is now full -- the neighbor would advertise zero.
        self._drive_credit(self.XPOS, 0)
        v = self.dut.xpos_m_axis_tvalid
        for _ in range(10):
            await RisingEdge(self.aclk)
            if self.slaves[self.XPOS].packets_received != 1:
                raise AssertionError(
                    f"{tag}: more than one flit passed on the full link")
            if int(v.value) != 0:
                raise AssertionError(
                    f"{tag}: tvalid raised on the credit-less link")

        self._drive_credit(self.XPOS, (1 << 2) - 1)
        await ta
        await tb
        await self._wait_beats(self.XPOS, 2 * BEATS, tag)
        await self.wait_clocks('aclk', 4)
        self._verify_frames(self._frames_at(self.XPOS),
                            [(header_a, payload_a), (header_b, payload_b)], tag)
        self.log.info(
            "flow control (b): one-credit-left atomicity: no interleaving, "
            "no loss")

    async def run_back_to_back_steady_state(self):
        """(c) Back-to-back packets on one output sustain 1 flit/clk; the
        only allowed idle output cycles are the documented 1-cycle bubble
        per packet boundary (P-1 bubbles for P packets)."""
        tag = "steady-state"
        PKTS, BEATS = 4, 4
        expected = []
        for i in range(PKTS):
            header = self.build_header(dst=(3, 0, 0), src=self.POS,
                                       packet_id=0xC0 + i)
            payload = [self.rng.getrandbits(self.DATA_WIDTH)
                       for _ in range(BEATS)]
            expected.append((header, payload))

        async def monitor():
            v = getattr(self.dut, f"{self.XPOS}_m_axis_tvalid")
            r = getattr(self.dut, f"{self.XPOS}_m_axis_tready")
            hs = 0
            idle = 0
            started = False
            for _ in range(5000):
                await RisingEdge(self.aclk)
                if int(v.value) and int(r.value):
                    hs += 1
                    started = True
                    if hs == PKTS * BEATS:
                        return hs, idle
                elif started:
                    idle += 1
            raise AssertionError(f"{tag}: monitor timed out")

        mon = cocotb.start_soon(monitor())
        # One burst, all beats queued up front: the producer streams
        # contiguously, so the only idle cycles must be the RTL's own.
        await self._send_burst('local', expected)
        hs, idle = await mon
        if hs != PKTS * BEATS:
            raise AssertionError(
                f"{tag}: monitor counted {hs} handshakes, expected "
                f"{PKTS * BEATS}")
        if idle > PKTS - 1:
            raise AssertionError(
                f"{tag}: {idle} idle output cycles for {PKTS} back-to-back "
                f"packets, expected <= {PKTS - 1} (the documented 1-cycle "
                f"bubble per packet boundary)")
        self._verify_frames(self._frames_at(self.XPOS), expected, tag)
        self.log.info(
            f"flow control (c): back-to-back sustained 1 flit/clk "
            f"({idle} idle cycles, <= {PKTS - 1} allowed)")


class DeltaMeshTablesTB(DeltaMeshCellTB):
    """TB for the route_table RAM: in-band config read/write/readback with
    a reroute verify, and the malformed-dst drop path with err_drop_cnt
    (Task 5). Derived from the cell TB; uses the same harness
    (dv/tb/delta_mesh_cell_th.sv) at POS (1,1,0) of the 4x4x1 grid.

    Config transaction (plan-pinned format): a single-beat packet on the
    local port addressed to the cell itself (dst == POS), QoS class 0,
    ``sr_ptr[0]`` = 1 write / 0 read, command in the payload beat's TDATA:
    ``{table_index[15:0], entry[8:0]}`` (entry = {port_mask[7:0], vc};
    the mask widened to 8 bits when P_DIA landed, Task 6b).
    The response is a single beat on the local master's m_axis carrying
    the same ``{table_index, entry}`` shape: a write acks with the written
    entry, a read returns the table value. Responses carry tuser = 0.
    """

    GRID = (4, 4, 1)  # must match the harness GRID_* parameters

    # ------------------------------------------------------------------
    # Config helpers
    # ------------------------------------------------------------------
    def build_config_header(self, is_write, packet_id):
        return self.build_header(dst=self.POS, src=self.POS, qos=0,
                                 packet_id=packet_id,
                                 sr_ptr=1 if is_write else 0)

    @staticmethod
    def build_config_payload(index, entry):
        return (entry << 16) | index

    async def _config_op(self, is_write, index, entry, packet_id, tag):
        """Send one config transaction; returns the expected response frame
        count at the local master."""
        header = self.build_config_header(is_write, packet_id)
        payload = self.build_config_payload(index, entry)
        frames_before = self.slaves['local'].frames_received
        await self._send_packet('local', header, [payload])
        return frames_before + 1

    async def _expect_response(self, exp_index, exp_entry, exp_frames, tag):
        slave = self.slaves['local']
        for _ in range(1000):
            if slave.frames_received >= exp_frames:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(f"{tag}: no config response observed")
        beat = slave.get_observed_packets()[-1]
        got_data = int(beat.fields['data'])
        got_last = int(beat.fields.get('last', 0))
        got_user = int(beat.fields.get('user', 0))
        exp_data = self.build_config_payload(exp_index, exp_entry)
        if got_data != exp_data:
            raise AssertionError(
                f"{tag}: response data mismatch: got 0x{got_data:x}, "
                f"expected 0x{exp_data:x} (index {exp_index}, entry 0x{exp_entry:02x})")
        if got_last != 1:
            raise AssertionError(f"{tag}: response tlast {got_last}, expected 1")
        if got_user != 0:
            raise AssertionError(
                f"{tag}: response tuser 0x{got_user:x}, expected 0")

    async def _wait_err_count(self, exp, tag):
        for _ in range(200):
            await RisingEdge(self.aclk)
            if int(self.dut.err_drop_cnt.value) == exp:
                return
        raise AssertionError(
            f"{tag}: err_drop_cnt == {int(self.dut.err_drop_cnt.value)}, "
            f"expected {exp}")

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------
    async def run_config_read_write_reroute(self):
        """(b) Read a power-on entry; rewrite one dst to a different port;
        traffic follows the new route; readback confirms."""
        tag = "config"
        idx_d30 = table_index((3, 0, 0), 0, self.COORD_W)
        idx_d22 = table_index((2, 2, 0), 0, self.COORD_W)

        # (1) power-on readback: dst (3,0,0) routes P_X_POS on the image.
        f = await self._config_op(False, idx_d30, 0, 0x51, tag)
        await self._expect_response(idx_d30, 1 << P_X_POS, f,
                                    f"{tag}: read dst(3,0,0)")

        # (2) traffic follows the default image before any write.
        header = self.build_header(dst=(3, 0, 0), src=self.POS,
                                   packet_id=0x52)
        payload = self._random_payload()
        await self._send_packet('local', header, payload)
        await self._expect_packet('xpos', header, payload, 1,
                                  f"{tag}: default route dst(3,0,0)")

        # (3) rewrite dst (2,2,0) to P_Y_POS -- DOR would route P_X_POS
        # first at POS (1,1,0), so a ypos exit proves the table drove it.
        new_entry = 1 << P_Y_POS
        f = await self._config_op(True, idx_d22, new_entry, 0x53, tag)
        await self._expect_response(idx_d22, new_entry, f,
                                    f"{tag}: write ack dst(2,2,0)")

        # (4) readback confirms.
        f = await self._config_op(False, idx_d22, 0, 0x54, tag)
        await self._expect_response(idx_d22, new_entry, f,
                                    f"{tag}: readback dst(2,2,0)")

        # (5) traffic follows the NEW route; the old route stays silent.
        header = self.build_header(dst=(2, 2, 0), src=self.POS,
                                   packet_id=0x55)
        payload = self._random_payload()
        await self._send_packet('local', header, payload)
        await self._expect_packet('ypos', header, payload, 1,
                                  f"{tag}: rerouted dst(2,2,0)")
        if self.slaves['xpos'].frames_received != 1:
            raise AssertionError(
                f"{tag}: xpos saw {self.slaves['xpos'].frames_received} "
                f"frames, expected 1 (pre-write packet only)")

        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({'xpos', 'ypos', 'local'}, tag)
        self.log.info("delta mesh tables: config read/write/reroute passed")

    async def run_err_drop(self):
        """(c) Review Focus #2: an out-of-range dst is dropped at the head,
        err_drop_cnt counts heads only, and subsequent traffic is
        unaffected. COORD_W=2 fields cannot encode 9 on a 4-wide grid, so
        the out-of-range coordinate uses the Z axis (grid Z=1, dst_z=1 is
        representable and out of range)."""
        tag = "err-drop"
        if int(self.dut.err_drop_cnt.value) != 0:
            raise AssertionError(f"{tag}: err_drop_cnt not zero at reset")

        # (1) multi-beat packet, out-of-range dst: head counted once, the
        # body beats drain silently.
        header = self.build_header(dst=(0, 0, 1), src=self.POS,
                                   packet_id=0x61)
        payload = self._random_payload()
        await self._send_packet('local', header, payload)
        await self._wait_err_count(1, f"{tag}: head drop")
        await self.wait_clocks('aclk', 10)
        if int(self.dut.err_drop_cnt.value) != 1:
            raise AssertionError(
                f"{tag}: err_drop_cnt {int(self.dut.err_drop_cnt.value)}, "
                f"expected 1 (body beats must drain without counting)")
        self._check_idle_ports(set(), f"{tag}: leak")

        # (2) single-beat out-of-range packet: counter -> 2.
        header = self.build_header(dst=(2, 2, 1), src=self.POS,
                                   packet_id=0x62)
        await self._send_packet('local', header, [0xDEAD_BEEF])
        await self._wait_err_count(2, f"{tag}: single-beat drop")
        self._check_idle_ports(set(), f"{tag}: leak2")

        # (3) the fabric keeps working: normal post-drop traffic delivers.
        header = self.build_header(dst=(3, 0, 0), src=self.POS,
                                   packet_id=0x63)
        payload = self._random_payload()
        await self._send_packet('local', header, payload)
        await self._expect_packet('xpos', header, payload, 1,
                                  f"{tag}: post-drop traffic")
        if int(self.dut.err_drop_cnt.value) != 2:
            raise AssertionError(
                f"{tag}: err_drop_cnt moved on good traffic")
        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({'xpos'}, tag)
        self.log.info("delta mesh tables: err_drop + counter passed")

    async def run_err_drop_vc1(self):
        """Cross-VC drop-drain characterization: a VC1 packet with an
        out-of-range dst drains only its own VC FIFO, and VC0 traffic
        arriving mid-drain is delivered untouched with the head counted
        once. Guards two mechanisms that keep the drain on its own VC:
        drop_req fires only on the presented head (so the drain's
        rd_ready always addresses the presented VC), and the drain's
        first consume forms the per-input packet lock, pinning sel_vc
        to the drain VC until the dropped packet's TLAST.

        Deterministic construction: a VC0 packet is granted on xpos and
        stalled on zero credits; a VC1 drop packet of exactly the FIFO
        depth is then fully buffered (the held port cannot present its
        head, so nothing drains). Releasing credits drains the VC0
        packet, the VC1 head drops (err_drop_cnt -> 1), the whole
        buffered VC1 packet drains, and a second VC0 packet is
        raw-driven into the drain window."""
        tag = "err-drop-vc1"
        V1_BEATS = 4  # == input FIFO DEPTH: fully buffered pre-drop
        header_a = self.build_header(dst=(3, 0, 0), src=self.POS, vc=0,
                                     packet_id=0x70)
        payload_a = [self.rng.getrandbits(self.DATA_WIDTH)
                     for _ in range(2)]
        header_v1 = self.build_header(dst=(0, 0, 1), src=self.POS, vc=1,
                                      packet_id=0x71)
        payload_v1 = [self.rng.getrandbits(self.DATA_WIDTH)
                      for _ in range(V1_BEATS)]
        header_b = self.build_header(dst=(3, 0, 0), src=self.POS, vc=0,
                                     packet_id=0x72)
        payload_b = [self.rng.getrandbits(self.DATA_WIDTH)]

        # (1) VC0 packet A granted on xpos, then stalled by zero
        # credits: the grant is packet-atomic, so the output holds
        # while the packet waits for credit (credits model the
        # downstream stall, as in the flow-control suite; tready stays
        # with the always-ready slave BFM).
        self.dut.xpos_s_credit.value = 0
        await self._send_packet('local', header_a, payload_a)
        await self.wait_clocks('aclk', 4)  # A granted + held

        # (2) The VC1 drop packet is fully buffered in the VC1 FIFO
        # while A holds the port: its head cannot be presented (the
        # port presents VC0), so nothing drains and the producer
        # completes all DEPTH beats. Wait for the BFM queue to drain so
        # the intake packet boundary (in_pkt) is closed before the next
        # injection -- a beat arriving mid-packet would be steered into
        # the wrong VC by the in_pkt latch.
        await self._send_packet('local', header_v1, payload_v1)
        for _ in range(200):
            await RisingEdge(self.aclk)
            if not int(self.dut.local_s_axis_tvalid.value):
                break
        else:
            raise AssertionError(f"{tag}: V1 producer never went idle")

        # (3) Release credits: A drains and completes, the VC1 head
        # presents and drops, and the whole buffered VC1 packet drains
        # afterwards.
        self.dut.xpos_s_credit.value = (1 << 2) - 1
        await self._wait_err_count(1, f"{tag}: vc1 head drop")

        # (4) VC0 packet B lands while the VC1 drain is mid-flight. Raw
        # drive: the BFM pipeline turnaround would let a short drain
        # finish first. Pre-fix this beat is eaten by the wandering
        # drain; post-fix it waits in VC0 and routes after the drain.
        dut = self.dut
        dut.local_s_axis_tvalid.value = 1
        dut.local_s_axis_tdata.value = payload_b[0]
        dut.local_s_axis_tuser.value = header_b
        dut.local_s_axis_tlast.value = 1
        for _ in range(10):
            await RisingEdge(self.aclk)
            if int(dut.local_s_axis_tready.value):
                break
        else:
            raise AssertionError(f"{tag}: vc0 beat B not accepted")
        dut.local_s_axis_tvalid.value = 0
        dut.local_s_axis_tlast.value = 0
        dut.local_s_axis_tuser.value = 0
        dut.local_s_axis_tdata.value = 0

        # (5) Both VC0 packets delivered intact and in order (A was
        # granted first); the drop counted the VC1 head only; the
        # stranded-body poison (pre-fix: re-parsed VC1 beats exit
        # xneg) never emitted.
        slave = self.slaves['xpos']
        for _ in range(1000):
            if slave.frames_received >= 2:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(
                f"{tag}: xpos saw {slave.frames_received} frames, "
                f"expected 2 (packets A and B)")
        beats = slave.get_observed_packets()
        exp = ((header_a, payload_a), (header_b, payload_b))
        offset = 0
        for e_header, e_payload in exp:
            n = len(e_payload)
            frame = beats[offset:offset + n]
            offset += n
            if len(frame) != n:
                raise AssertionError(
                    f"{tag}: frame truncated: {len(frame)} beats, "
                    f"expected {n}")
            for i, (beat, e_data) in enumerate(zip(frame, e_payload)):
                got_data = int(beat.fields['data'])
                got_user = int(beat.fields.get('user', 0))
                got_last = int(beat.fields.get('last', 0))
                e_last = 1 if i == n - 1 else 0
                e_user = e_header if i == 0 else 0
                if got_data != e_data or got_user != e_user \
                        or got_last != e_last:
                    raise AssertionError(
                        f"{tag}: beat mismatch (0x{got_data:x}/"
                        f"0x{got_user:x}/{got_last}) vs expected "
                        f"(0x{e_data:x}/0x{e_user:x}/{e_last})")
        await self.wait_clocks('aclk', 10)
        if int(self.dut.err_drop_cnt.value) != 1:
            raise AssertionError(
                f"{tag}: err_drop_cnt {int(self.dut.err_drop_cnt.value)}, "
                f"expected 1 (VC0 traffic must not count)")
        self._check_idle_ports({'xpos'}, tag)
        self.log.info("delta mesh tables: cross-VC drop drain passed")


# Pinned control-plane magics (Task 6). The mode-switch command is a
# config-format packet whose payload beat carries the magic in TDATA[15:0]
# (the config table_index field) and the mode id in TDATA[19:16] (the
# config entry field's low nibble). The ack is a one-beat control packet
# (qos 1, mcast 0, sr_ptr[0] = 1) with the ack magic in TDATA[15:0].
# NOTE: the controller's "16'hM0DE" spelling is not a legal SystemVerilog
# hex literal (M is not a hex digit); 16'hC0DE ("config opcode") is the
# nearest legal stand-in. 16'hACED ("ACKED") is legal as pinned.
MSW_MAGIC = 0xC0DE
ACK_MAGIC = 0xACED


class DeltaMeshModesTB(DeltaMeshFabricTB):
    """TB for the broadcast mode-switch + ack barrier + standard modes
    (Task 6), on the 2x2x1 fabric harness.

    Control-plane contract under test (controller-pinned):

    - Mode-switch broadcast: a config-format packet (dst == self, qos 0,
      mcast 1, sr_ptr[0] = 1 write, single beat) with payload
      ``{mode_id[3:0], magic[15:0]}`` injected at any cell's local port.
      Every cell recognizes it (the flooded copies carry each receiving
      cell's own coordinate as dst), switches ``r_mode``, re-emits copies
      on all its neighbor ports (flooding; a cell already in the target
      mode suppresses re-emission, which terminates the flood), and
      returns a one-beat ack to the origin.  Mode id 0 returns to the
      custom RAM tables.
    - The origin counts received acks in ``o_mode_acks``; the barrier for
      an N-cell fabric completes at N acks.  Acks are one-beat control
      packets (qos 1, mcast 0, sr_ptr[0] = 1) whose header src coordinate
      identifies the acking cell.
    - Control traffic (sr_ptr[0] = 1) always routes DOR, independent of
      the current mode, so the switch/ack machinery works under any mode.

    Mode images (all validated offline by tables.check_acyclic):
    mode 1 = pure DOR; mode 2 = systolic-1D (+X when dst_x > pos_x else
    P_LOCAL -- the pinned minimal image, no torus wrap until Task 9);
    mode 5 = broadcast placeholder (DOR; multicast replication is
    Task 8); mode 6 = convergecast (every dst routes toward root
    0,0,0); modes 3/4/7/8 = minimal DOR images.  DV selects and
    delivers under modes 0/1/2/3/5/6; modes 4/7/8 are covered by the
    offline image suite (bin/tests/test_delta_mesh_modes.py) this
    task.  Mode 0 = custom RAM tables, power-on default.

    Congestion corner (scenario d): fan-out/ack control beats are
    injected into the local VC0 input FIFO only while it can accept
    (``gen_take`` gated by ``w_fifo_wr_ready[P_LOCAL][0]``); a full
    FIFO stalls the drain of the control-generator FIFO, never drops
    a beat (the house FIFO commits writes only on
    wr_valid && wr_ready, and the gen FIFO pops on rd_ready alone).
    """

    def __init__(self, dut):
        super().__init__(dut)
        self._pid = 0x6000

    # ------------------------------------------------------------------
    # Mode-switch / ack-barrier helpers
    # ------------------------------------------------------------------
    def _next_pid(self):
        self._pid += 1
        return self._pid

    def _mode_acks(self, bidx):
        return int(getattr(self.dut, f'b{bidx}_mode_acks').value)

    async def _wait_mode_acks(self, bidx, count, tag):
        for _ in range(6000):
            if self._mode_acks(bidx) >= count:
                return
            await RisingEdge(self.aclk)
        raise AssertionError(
            f"{tag}: o_mode_acks[b{bidx}] == {self._mode_acks(bidx)}, "
            f"expected {count} (ack barrier never completed)")

    async def _issue_mode_switch(self, bidx, mode_id, tag):
        """Inject one broadcast mode-switch at boundary bidx."""
        coord = self.BOUNDARY_COORDS[bidx]
        header = self.build_header(dst=coord, src=coord, qos=0, mcast=1,
                                   sr_ptr=1, packet_id=self._next_pid())
        payload = (mode_id << 16) | MSW_MAGIC
        await self._send_packet(f'b{bidx}', header, [payload])

    async def _switch_and_wait(self, bidx, mode_id, cum_acks, tag):
        await self._issue_mode_switch(bidx, mode_id, tag)
        await self._wait_mode_acks(bidx, cum_acks, tag)
        self._check_acks(bidx, cum_acks, tag)

    def _is_ack_frame(self, frame):
        """One-beat control packet with the ack magic (see class note)."""
        if len(frame) != 1:
            return False
        head = int(frame[0].fields.get('user', 0))
        data = int(frame[0].fields['data'])
        qos_lo, qos_w = self.hdr_offsets['qos']
        sr_lo = self.hdr_offsets['sr_ptr'][0]
        mcast_lo = self.hdr_offsets['mcast'][0]
        return ((head >> qos_lo) & ((1 << qos_w) - 1)) == 1 and \
            ((head >> mcast_lo) & 1) == 0 and \
            ((head >> sr_lo) & 1) == 1 and \
            (data & 0xFFFF) == ACK_MAGIC

    def _group_frames(self, port, tag):
        # The modes scoreboards see only data frames: the ack frames the
        # origin accumulates are control traffic, not deliveries. Strict:
        # a trailing beat without tlast raises -- for FINAL scoreboards
        # after the traffic has settled only.
        frames, trailing = self._group_frames_lenient(self.slaves[port])
        if trailing:
            raise AssertionError(
                f"{tag}: boundary '{port}' ended mid-packet "
                f"({len(trailing)} trailing beats without tlast)")
        return [f for f in frames if not self._is_ack_frame(f)]

    @staticmethod
    def _group_frames_lenient(port):
        """Group a slave's beats into frames, keeping any trailing
        partial packet instead of raising (for mid-flight polling)."""
        frames = []
        current = []
        for beat in port.get_observed_packets():
            current.append(beat)
            if int(beat.fields.get('last', 0)):
                frames.append(current)
                current = []
        return frames, current

    def _data_frame_count(self, port):
        """Complete data frames at a boundary (acks filtered, partial
        packets not counted) -- the polling-safe counter."""
        frames, _trailing = self._group_frames_lenient(self.slaves[port])
        return sum(1 for f in frames if not self._is_ack_frame(f))

    async def _wait_frames(self, port, n):
        """Wait until a boundary holds `n` complete DATA frames."""
        for _ in range(6000):
            if self._data_frame_count(port) >= n:
                return
            await RisingEdge(self.aclk)
        raise AssertionError(
            f"modes: boundary '{port}' saw {self._data_frame_count(port)} "
            f"complete data frames, expected {n}")

    def _check_acks(self, origin, n, tag):
        """Exactly n ack frames at the origin, one per cell, count exact."""
        frames = super()._group_frames(f'b{origin}', tag)
        acks = [f for f in frames if self._is_ack_frame(f)]
        if len(acks) != n:
            raise AssertionError(
                f"{tag}: origin b{origin} received {len(acks)} ack frames, "
                f"expected {n}")
        srcs = set()
        for frame in acks:
            head = int(frame[0].fields.get('user', 0))
            data = int(frame[0].fields['data'])
            if (data & 0xFFFF) != ACK_MAGIC:
                raise AssertionError(
                    f"{tag}: ack payload 0x{data:x}, magic 0x{ACK_MAGIC:04x} "
                    f"expected")
            sx_lo, sx_w = self.hdr_offsets['src_x']
            sy_lo, sy_w = self.hdr_offsets['src_y']
            sz_lo, sz_w = self.hdr_offsets['src_z']
            srcs.add(((head >> sx_lo) & ((1 << sx_w) - 1),
                      (head >> sy_lo) & ((1 << sy_w) - 1),
                      (head >> sz_lo) & ((1 << sz_w) - 1)))
        if srcs != set(self.BOUNDARY_COORDS):
            raise AssertionError(
                f"{tag}: acks received from {sorted(srcs)}, expected one "
                f"per cell {sorted(self.BOUNDARY_COORDS)}")
        if self._mode_acks(origin) != n:
            raise AssertionError(
                f"{tag}: o_mode_acks[b{origin}] == "
                f"{self._mode_acks(origin)}, expected exactly {n}")

    def _err(self, bidx):
        return int(getattr(self.dut, f'b{bidx}_err').value)

    def _check_zero_err(self, tag):
        for bidx in range(len(self.BOUNDARY_COORDS)):
            if self._err(bidx) != 0:
                raise AssertionError(
                    f"{tag}: b{bidx}_err == {self._err(bidx)}, expected 0")

    def _data_frame_counts(self):
        return {bidx: self._data_frame_count(f'b{bidx}')
                for bidx in range(len(self.BOUNDARY_COORDS))}

    def _check_no_new_frames(self, since, allowed, tag):
        """Every boundary NOT in `allowed` must show the same data-frame
        count as `since` (no misdelivery/leak at the other locals)."""
        now = self._data_frame_counts()
        for bidx, count in now.items():
            if bidx in allowed:
                continue
            if count != since[bidx]:
                raise AssertionError(
                    f"{tag}: boundary b{bidx} gained "
                    f"{count - since[bidx]} unexpected data frames "
                    f"(misdelivery/leak)")

    # ------------------------------------------------------------------
    # Delivery helper
    # ------------------------------------------------------------------
    async def _expect_delivery(self, src_bidx, dst_coord, to_bidx, tag):
        """Inject one data packet at src_bidx for dst_coord; the new last
        data frame at to_bidx must match it exactly. Polling is lenient
        (complete frames only) so concurrent deliveries elsewhere cannot
        trip the mid-packet guard."""
        port = f'b{to_bidx}'
        before = self._data_frame_count(port)
        header = self.build_header(dst=dst_coord,
                                   src=self.BOUNDARY_COORDS[src_bidx],
                                   qos=1, packet_id=self._next_pid())
        payload = self._random_payload()
        await self._send_packet(f'b{src_bidx}', header, payload)
        frames = []
        for _ in range(6000):
            all_frames, _trailing = self._group_frames_lenient(self.slaves[port])
            frames = [f for f in all_frames if not self._is_ack_frame(f)]
            if len(frames) >= before + 1:
                break
            await RisingEdge(self.aclk)
        else:
            raise AssertionError(
                f"{tag}: b{src_bidx}->dst{dst_coord} never delivered to "
                f"b{to_bidx}")
        self._match_expected_frames(port, to_bidx,
                                    {(src_bidx, to_bidx): (header, payload)},
                                    frames[before:], tag)

    # ------------------------------------------------------------------
    # Config helpers (Task 5 protocol, applied at any boundary cell)
    # ------------------------------------------------------------------
    def build_config_header(self, is_write, packet_id, coord):
        return self.build_header(dst=coord, src=coord, qos=0,
                                 packet_id=packet_id,
                                 sr_ptr=1 if is_write else 0)

    async def _config_op(self, bidx, is_write, index, entry, tag):
        """One config transaction at boundary bidx; verifies the response
        beat carries the {table_index, entry} echo/value."""
        coord = self.BOUNDARY_COORDS[bidx]
        header = self.build_config_header(is_write, self._next_pid(), coord)
        payload = (entry << 16) | index
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
            raise AssertionError(f"{tag}: no config response at b{bidx}")
        beat = frames[-1][0]
        got_data = int(beat.fields['data'])
        got_last = int(beat.fields.get('last', 0))
        got_user = int(beat.fields.get('user', 0))
        # the caller passes the expected entry: the written entry echoes
        # on a write, the table value on a read
        exp_data = (entry << 16) | index
        if got_data != exp_data:
            raise AssertionError(
                f"{tag}: b{bidx} config response 0x{got_data:x}, expected "
                f"0x{exp_data:x} (index {index}, entry 0x{entry:02x})")
        if got_last != 1 or got_user != 0:
            raise AssertionError(
                f"{tag}: b{bidx} config response tlast/tuser "
                f"({got_last}/{got_user:x}), expected 1/0")

    # ------------------------------------------------------------------
    # Scenario (a): broadcast switch to mode 1 + barrier + all-pairs
    # ------------------------------------------------------------------
    async def run_mode_switch_barrier(self):
        tag = "msw-barrier"
        # Broadcast switch to mode 1 from b0; the barrier completes when
        # all four cells' acks are in.
        await self._issue_mode_switch(0, 1, tag)
        await self._wait_mode_acks(0, 4, tag)
        self._check_acks(0, 4, tag)
        # Traffic still all-pairs correct under mode 1 (image == DOR).
        # The base scoreboard routes through this class's ack-filtered
        # _group_frames / _wait_frames, so b0's four ack frames are
        # ignored by the packet accounting.
        await self.run_all_pairs()
        self._check_zero_err(tag)
        self.log.info(
            "delta mesh modes (a): broadcast switch to mode 1, ack "
            "barrier at 4, all-pairs intact")

    # ------------------------------------------------------------------
    # Multicast helper used by mode-5 validation (Task 8) and by the
    # dedicated multicast test class below.
    # ------------------------------------------------------------------
    def build_mcast_header(self, src, packet_id, qos=1, vc=0):
        """Header for a multicast packet; dst is rewritten to the source
        coordinate so it is not mistaken for an ordinary unicast."""
        return self.build_header(dst=src, src=src, qos=qos, vc=vc,
                                 packet_id=packet_id, mcast=1)

    # ------------------------------------------------------------------
    # Scenario (b): mode images 2/5/6 + RAM-intact across switches
    # ------------------------------------------------------------------
    async def run_mode_images(self):
        tag = "mode-images"

        # --- mode 2: systolic-1D pinned minimal image ---
        await self._switch_and_wait(0, 2, 4, tag)
        counts = self._data_frame_counts()
        # left -> right delivers across the +X link
        await self._expect_delivery(0, (1, 0, 0), 1, f"{tag}:m2-xpos")
        # same-column dst: P_LOCAL at the left edge (no wrap yet: Task 9)
        await self._expect_delivery(0, (0, 1, 0), 0, f"{tag}:m2-local")
        # right-edge cell: every dst delivers locally (degenerate ring)
        await self._expect_delivery(1, (0, 0, 0), 1, f"{tag}:m2-degenerate")
        self._check_no_new_frames(counts, allowed={0, 1}, tag=f"{tag}:m2")

        # --- mode 5: broadcast placeholder -- with Task 8 replication,
        #     a multicast packet reaches every local output exactly once.
        #     The mcast path ignores the mode image (VC0-only, runtime
        #     BFS-tree flood), so this validates mode 5 selection and the
        #     full-fabric delivery contract.
        await self._switch_and_wait(0, 5, 8, tag)
        counts = self._data_frame_counts()
        nb = len(self.BOUNDARY_COORDS)
        await DeltaMeshMulticastTB.run_mcast_full_fabric(self, src_bidx=0)
        self._check_no_new_frames(counts, allowed=set(range(nb)),
                                  tag=f"{tag}:m5")

        # --- mode 3: wavefront-2D -- minimal DOR image; select + deliver:
        #     x-first leg from the y row, y-leg from the x column ---
        await self._switch_and_wait(0, 3, 12, tag)
        counts = self._data_frame_counts()
        # b2=(0,1,0) -> (1,0,0): +X to (1,1,0), then -Y to b1
        await self._expect_delivery(2, (1, 0, 0), 1, f"{tag}:m3-xpos")
        # b0=(0,0,0) -> (0,1,0): straight +Y to b2
        await self._expect_delivery(0, (0, 1, 0), 2, f"{tag}:m3-ypos")
        self._check_no_new_frames(counts, allowed={1, 2}, tag=f"{tag}:m3")

        # --- mode 6: convergecast -- everything routes to root b0 ---
        await self._switch_and_wait(0, 6, 16, tag)
        counts = self._data_frame_counts()

        # All three cells inject concurrently (convergecast contention at
        # the root); scoreboard as a set once all three are in -- a
        # per-packet wait would race on the shared frame counter.
        async def send_to_root(src_bidx):
            header = self.build_header(dst=self.BOUNDARY_COORDS[src_bidx],
                                       src=self.BOUNDARY_COORDS[src_bidx],
                                       qos=1,
                                       packet_id=self._next_pid())
            payload = self._random_payload()
            await self._send_packet(f'b{src_bidx}', header, payload)
            return src_bidx, (header, payload)

        senders = [cocotb.start_soon(send_to_root(b)) for b in (1, 2, 3)]
        expected6 = {}
        for sender in senders:
            src_bidx, hp = await sender
            expected6[(src_bidx, 0)] = hp
        await self._wait_frames('b0', counts[0] + 3)
        all_frames, _trailing = self._group_frames_lenient(self.slaves['b0'])
        data_frames = [f for f in all_frames if not self._is_ack_frame(f)]
        self._match_expected_frames('b0', 0, expected6,
                                    data_frames[counts[0]:],
                                    f"{tag}:m6")
        await self.wait_clocks('aclk', 10)
        self._check_no_new_frames(counts, allowed={0}, tag=f"{tag}:m6")

        # --- RAM intact across switches (mode mux, not RAM rewrite) ---
        # mode 0 restores the custom tables; config writes/reads work in
        # every mode and the switch never touches the RAM contents.
        await self._switch_and_wait(0, 0, 20, f"{tag}:to0")
        # data rides qos 1: the custom key is the qos-1 region
        idx_d00 = table_index((0, 0, 0), 1, self.COORD_W)
        local_entry = 1 << P_LOCAL  # deliver dst(0,0,0) locally at b1
        # b1 = (1,0,0): DOR would say P_X_NEG; P_LOCAL is unambiguous.
        # The data plane rides qos 1, so the custom entry must be written
        # to the qos-1 region of the table (the key is {qos, dst}).
        await self._config_op(1, True, idx_d00, local_entry,
                              f"{tag}:ram-write")
        await self._config_op(1, False, idx_d00, local_entry,
                              f"{tag}:ram-readback")
        counts = self._data_frame_counts()
        await self._expect_delivery(1, (0, 0, 0), 1, f"{tag}:ram-custom")
        self._check_no_new_frames(counts, allowed={1}, tag=f"{tag}:ram-custom")

        await self._switch_and_wait(0, 1, 24, f"{tag}:to1")
        # the custom entry survives the broadcast switch untouched
        await self._config_op(1, False, idx_d00, local_entry,
                              f"{tag}:ram-during-mode1")
        counts = self._data_frame_counts()
        # mode 1 image == DOR: the same packet now crosses to b0
        await self._expect_delivery(1, (0, 0, 0), 0, f"{tag}:mode1-dor")
        self._check_no_new_frames(counts, allowed={0}, tag=f"{tag}:mode1-dor")

        await self._switch_and_wait(0, 0, 28, f"{tag}:to0-again")
        await self._config_op(1, False, idx_d00, local_entry,
                              f"{tag}:ram-restored")
        counts = self._data_frame_counts()
        await self._expect_delivery(1, (0, 0, 0), 1, f"{tag}:ram-custom2")
        self._check_no_new_frames(counts, allowed={1}, tag=f"{tag}:ram-custom2")

        # final accounting: b0 = 6 deliveries + 28 acks (seven switches);
        # b1 = 6 deliveries + 4 config responses; b2 = 2; b3 = 1.
        await self.wait_clocks('aclk', 10)
        exp_counts = {0: 6, 1: 10, 2: 2, 3: 1}
        got_counts = self._data_frame_counts()
        if got_counts != exp_counts:
            raise AssertionError(
                f"{tag}: final data-frame counts {got_counts}, expected "
                f"{exp_counts}")
        self._check_zero_err(tag)
        self.log.info(
            "delta mesh modes (b): mode 2/3/5/6 images + RAM intact "
            "across switches")

    # ------------------------------------------------------------------
    # Scenario (c): Review Focus #4 -- switch broadcast mid-flight
    # ------------------------------------------------------------------
    async def run_mode_switch_in_flight(self):
        """8 packets in flight when the mode-switch broadcast lands:
        every packet delivers exactly once, the ack barrier reaches 4,
        zero drops.  The switch targets mode 1 (image == DOR): a
        routing-CHANGING mode would by design misroute in-flight
        packets (the spec's 'no packet straddles two modes' rule is
        enforced by waiting for the barrier before new traffic)."""
        tag = "msw-inflight"
        pairs = ((0, 1), (0, 2),
                 (1, 0), (1, 3),
                 (2, 0), (2, 3),
                 (3, 1), (3, 2))
        expected = {}
        for a, b in pairs:
            payload = [self._pair_payload(a, b, j)
                       for j in range(self.BEATS_PER_PKT)]
            header = self.build_header(dst=self.BOUNDARY_COORDS[b],
                                       src=self.BOUNDARY_COORDS[a],
                                       qos=1,
                                       packet_id=self._next_pid())
            expected[(a, b)] = (header, payload)

        async def send_slow(src_idx):
            sent = [p for p in pairs if p[0] == src_idx]
            for _a, dst_idx in sent:
                await self._send_packet(f'b{src_idx}',
                                        expected[(src_idx, dst_idx)][0],
                                        expected[(src_idx, dst_idx)][1])

        async def send_burst(src_idx):
            master = self.masters[f'b{src_idx}']
            beats = []
            for _a, dst_idx in [p for p in pairs if p[0] == src_idx]:
                header, payload = expected[(src_idx, dst_idx)]
                n = len(payload)
                for i, data in enumerate(payload):
                    beat = AXISPacket(field_config=master.field_config)
                    beat.data = data
                    beat.last = 1 if i == n - 1 else 0
                    beat.user = header if i == 0 else 0
                    if 'strb' in master.field_config:
                        beat.strb = (1 << master.field_config['strb'].bits) - 1
                    beats.append(beat)
            await master.send_burst(beats)

        # b0 streams its two packets contiguously; b1..b3 send per-beat
        # (slower), so eight packets are mid-fabric when the switch
        # lands at b0 right after b0's burst is accepted.
        senders = [cocotb.start_soon(send_burst(0))]
        senders += [cocotb.start_soon(send_slow(a)) for a in (1, 2, 3)]
        await senders[0]
        await self._issue_mode_switch(0, 1, tag)
        for sender in senders[1:]:
            await sender

        for dst_idx in range(len(self.BOUNDARY_COORDS)):
            await self._wait_frames(f'b{dst_idx}', 2)
        await self.wait_clocks('aclk', 10)
        for dst_idx in range(len(self.BOUNDARY_COORDS)):
            frames = self._group_frames(f'b{dst_idx}', tag)
            exp = {k: v for k, v in expected.items() if k[1] == dst_idx}
            if len(frames) != len(exp):
                heads = sorted(
                    int(f[0].fields.get('user', 0)) for f in frames)
                raise AssertionError(
                    f"{tag}: boundary b{dst_idx} received {len(frames)} "
                    f"data frames, expected {len(exp)}; heads: "
                    + ", ".join(f"0x{h:x}" for h in heads))
            self._match_expected_frames(f'b{dst_idx}', dst_idx, exp, frames,
                                        tag)
        await self._wait_mode_acks(0, 4, tag)
        self._check_acks(0, 4, tag)
        self._check_zero_err(tag)
        self.log.info(
            "delta mesh modes (c): switch mid-flight -- 8 packets exactly "
            "once, ack barrier at 4, zero drops")

    # ------------------------------------------------------------------
    # Scenario (d): congestion corner -- fan/ack beats must not drop
    # when the local VC0 FIFO is full (gen_take wr_ready guard)
    # ------------------------------------------------------------------
    async def run_mode_switch_congested(self):
        """b0's local output is stalled (deterministic consumer-stall
        policy on the boundary slave) and its local VC0 input FIFO is
        filled with four self-dstined single-beat packets when the
        mode-switch broadcast lands: b0 consumes a flooded copy, and its
        fan-out (ack + copies to b1/b2) must wait in the control
        generator FIFO -- NOT drop -- until the stuck packets drain.
        Pre-guard RTL popped the gen FIFO on ``gen_take`` regardless of
        the full FIFO (house FIFO commits writes only on
        wr_valid && wr_ready), silently losing the beats: the barrier
        hung below 4 with no error tally.  Post-guard the barrier
        completes with acks == 4 exactly and zero err drops.
        """
        tag = "msw-congested"
        stuck_n = 4  # local VC0 input FIFO depth: fill it exactly

        # Deterministic full stall of b0's local output (the harness
        # slave's ready-policy API; set_ready_policy('stall') deasserts
        # ready immediately and holds it low).
        self.slaves['b0'].set_ready_policy('stall')

        # Fill b0's local VC0 input FIFO: single-beat qos-1 packets
        # destined to b0 itself (DOR delivers local).  The head packet
        # holds the output grant while the slave stalls; the rest queue
        # behind it until the FIFO reads full.
        stuck = {}
        for i in range(stuck_n):
            payload = [0x5C00 + i]
            header = self.build_header(dst=self.BOUNDARY_COORDS[0],
                                       src=self.BOUNDARY_COORDS[0],
                                       qos=1, packet_id=self._next_pid())
            await self._send_packet('b0', header, payload)
            stuck[i] = (header, payload)

        # Issue the switch at b1; the flooded copy reaches b0 through
        # b0's neighbor-port input FIFOs (uncongested), b0 consumes it
        # and its fan-out pushes into the FULL local VC0 FIFO.
        await self._issue_mode_switch(1, 1, tag)
        # Let the flood propagate and b0 attempt its fan-out while the
        # FIFO is still full: pre-guard RTL drops the gen beats here.
        await self.wait_clocks('aclk', 200)
        self._check_zero_err(f"{tag}:stalled")
        if self._data_frame_count('b0') != 0:
            raise AssertionError(
                f"{tag}: b0 delivered {self._data_frame_count('b0')} frames "
                f"while its output was stalled")
        # Pre-release the barrier must hold at exactly 3: b1's self-ack,
        # b3's ack, and b2's ack (b2 is reached unimpeded via b3's
        # fan-out) all ride uncongested paths -- only b0's ack is stuck
        # behind the full local FIFO.  Pre-guard RTL would have DROPPED
        # b0's gen beats, so the count freezes at 3 forever and the
        # post-release wait times out below 4.
        if self._mode_acks(1) != 3:
            raise AssertionError(
                f"{tag}: o_mode_acks[b1] == {self._mode_acks(1)} before "
                f"release, expected 3 (b1/b2/b3 via uncongested paths); "
                f"only b0's ack may still be blocked")

        # Release: the stuck packets drain, then the waiting fan/ack
        # beats enter and the barrier completes with exactly 4.
        self.slaves['b0'].set_ready_policy('valid_first')
        await self._wait_mode_acks(1, 4, tag)
        self._check_acks(1, 4, tag)
        # the stuck packets deliver at b0, exactly as sent (each a
        # distinct single beat; match the whole set)
        await self._wait_frames('b0', stuck_n)
        frames = self._group_frames('b0', tag)
        if len(frames) != stuck_n:
            raise AssertionError(
                f"{tag}: b0 delivered {len(frames)} frames after release, "
                f"expected {stuck_n}")
        want = {h: p[0] for h, p in stuck.values()}
        for frame in frames:
            head = int(frame[0].fields.get('user', 0))
            if head not in want:
                raise AssertionError(
                    f"{tag}: unexpected frame head 0x{head:x} at b0")
            if len(frame) != 1 or int(frame[0].fields['data']) != want.pop(head):
                raise AssertionError(
                    f"{tag}: stuck packet payload mismatch (head 0x{head:x})")
        if want:
            raise AssertionError(
                f"{tag}: {len(want)} stuck packets never delivered at b0")
        await self.wait_clocks('aclk', 10)
        self._check_zero_err(tag)
        self.log.info(
            "delta mesh modes (d): congested fan-out -- gen beats wait "
            "on the full local FIFO, barrier at 4, zero drops")


class DeltaMeshTetradTB(DeltaMeshModesTB):
    """TB for mode 9 (tetrad all-to-all K4) + the P_DIA diagonal link
    (Task 6b), on the 2x2x1 fabric harness -- a single tetrad:
    b0=(0,0,0), b1=(1,0,0), b2=(0,1,0), b3=(1,1,0). Edge mates: b0<->b1,
    b2<->b3 (+X), b0<->b2, b1<->b3 (+Y); diagonal mates: b0<->b3, b1<->b2.

    The single-hop property is proven by injection->ejection LATENCY,
    measured cycle-exactly with raw signal drive (the BFM pipeline
    turnaround would smear the stamps): every cell traversal (input
    buffer -> grant -> link -> output) adds a fixed latency, so a 2-hop
    detour through an intermediate cell adds a multiple of it and can
    never masquerade as 1 hop. Calibration, measured live on the same
    RTL/harness: in the power-on DOR mode the diagonal pair b0->b3 IS 2
    hops (dx then dy via an intermediate cell) while the edge pair
    b0->b1 is 1 hop; under mode 9 the diagonal pair must drop to exactly
    the 1-hop latency and every intra-tetrad pair (edge + diagonal mates,
    both parities) must measure the identical latency. In the bandwidth
    scenario a witness coroutine samples the fabric's inter-cell
    axis-port tvalids every cycle: any hidden 2-hop detour would toggle
    an axis port of an intermediate cell -- the direct diagonal link is
    the only inter-cell link allowed to carry traffic.
    """

    # The fabric's inter-cell port indices (pinned in delta_mesh_cell and
    # mirrored by fabric.py): 0..5 axis, 6 = P_DIA, 7 = P_DIA2, 8 = P_LOCAL.
    P_DIA_IDX = P_DIA
    AXIS_IDXS = (0, 1, 2, 3, 4, 5)

    # ------------------------------------------------------------------
    # Signal access helpers (raw drive / raw observe)
    # ------------------------------------------------------------------
    def _sig(self, prefix, suffix):
        return getattr(self.dut, f'{prefix}_{suffix}')

    # ------------------------------------------------------------------
    # Scenario (a): all 16 ordered intra-tetrad pairs, exactly 1 hop
    # ------------------------------------------------------------------
    async def _pair_latency(self, src_bidx, dst_bidx, pid, tag):
        """Raw-drive one single-beat packet b{src}->b{dst}; return
        (header, data, latency) with the ejected beat verified exact.
        Latency = ejection_cycle - injection_cycle in aclk edges."""
        s = f'b{src_bidx}'
        d = f'b{dst_bidx}'
        sv = self._sig(s, 's_axis_tvalid')
        sr = self._sig(s, 's_axis_tready')
        sd = self._sig(s, 's_axis_tdata')
        su = self._sig(s, 's_axis_tuser')
        sl = self._sig(s, 's_axis_tlast')
        dv = self._sig(d, 'm_axis_tvalid')
        dr = self._sig(d, 'm_axis_tready')
        dd = self._sig(d, 'm_axis_tdata')
        du = self._sig(d, 'm_axis_tuser')
        dl = self._sig(d, 'm_axis_tlast')

        header = self.build_header(
            dst=self.BOUNDARY_COORDS[dst_bidx],
            src=self.BOUNDARY_COORDS[src_bidx],
            qos=1, packet_id=pid)
        data = ((0x7E7 << 48) | (src_bidx << 44) | (dst_bidx << 40)
                | (pid & 0xFFFFF))
        sv.value = 1
        sd.value = data
        su.value = header
        sl.value = 1
        in_cyc = None
        out_cyc = None
        got_d = got_u = None
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
                got_d = int(dd.value)
                got_u = int(du.value)
            if cyc > 2000:
                raise AssertionError(
                    f"{tag}: b{src_bidx}->b{dst_bidx} never ejected "
                    f"(in_cyc={in_cyc})")
        if got_d != data or got_u != header:
            raise AssertionError(
                f"{tag}: b{src_bidx}->b{dst_bidx} ejected beat "
                f"0x{got_d:x}/0x{got_u:x}, expected 0x{data:x}/0x{header:x} "
                "(misdelivery or corruption)")
        return header, data, out_cyc - in_cyc

    async def run_tetrad_k4_one_hop(self):
        """All 12 ordered intra-tetrad pairs deliver in exactly 1 hop.

        Calibration first, in the power-on DOR mode (no switch): the
        edge pair b0->b1 is 1 hop, the diagonal pair b0->b3 is 2 hops.
        Then broadcast-switch to mode 9 (ack barrier), re-measure every
        ordered pair, and assert all 12 non-self latencies equal the
        mode-0 1-hop calibration exactly; the diagonal pairs must drop
        from the 2-hop calibration to the same 1-hop latency. A full
        boundary scoreboard proves exactly-once delivery."""
        tag = "tetrad-k4"
        nb = len(self.BOUNDARY_COORDS)
        expected = {}

        # --- calibration in power-on mode 0 (pure DOR image); the two
        # calibration packets are scoreboarded as their own pairs at the
        # end (they share the BFM records with the traffic) ---
        cal = {}
        h, d, edge_1hop = await self._pair_latency(0, 1, self._next_pid(),
                                                   f"{tag}:cal-edge")
        cal[(0, 1)] = (h, [d])
        h, d, diag_2hop = await self._pair_latency(0, 3, self._next_pid(),
                                                   f"{tag}:cal-diag")
        cal[(0, 3)] = (h, [d])
        if diag_2hop <= edge_1hop:
            raise AssertionError(
                f"{tag}: calibration cannot resolve hops: diagonal DOR "
                f"latency {diag_2hop} <= edge latency {edge_1hop} "
                "(expected 2 hops > 1 hop; latency method broken)")

        # --- switch to mode 9; the tetrad K4 image is live everywhere ---
        await self._switch_and_wait(0, 9, 4, tag)

        lat = {}
        for a in range(nb):
            for b in range(nb):
                header, data, l = await self._pair_latency(
                    a, b, self._next_pid(), f"{tag}:{a}->{b}")
                lat[(a, b)] = l
                payload = [data]
                expected[(a, b)] = (header, payload)

        # every non-self pair (edge mates AND diagonal mates, both
        # parities) is exactly the 1-hop latency; the diagonal pairs no
        # longer pay the 2-hop DOR calibration.
        for a in range(nb):
            for b in range(nb):
                if a == b:
                    continue
                if lat[(a, b)] != edge_1hop:
                    raise AssertionError(
                        f"{tag}: b{a}->b{b} latency {lat[(a,b)]} cycles, "
                        f"expected exactly the 1-hop latency {edge_1hop} "
                        f"(2-hop DOR would be {diag_2hop})")
        if lat[(0, 3)] != edge_1hop or lat[(3, 0)] != edge_1hop or \
                lat[(1, 2)] != edge_1hop or lat[(2, 1)] != edge_1hop:
            raise AssertionError(
                f"{tag}: diagonal pairs did not drop to 1 hop under mode 9")

        # exactly-once scoreboard at every boundary (self pairs deliver
        # on the cell's own local port). The two calibration packets and
        # the mode-switch acks at b0 ride in the same BFM records; the
        # acks are filtered by the modes class's _group_frames override
        # and the calibration frames are matched as their own pairs.
        await self.wait_clocks('aclk', 10)
        for dst_idx in range(nb):
            frames = self._group_frames(f'b{dst_idx}', tag)
            exp = {(a, dst_idx): hp for (a, b), hp in expected.items()
                   if b == dst_idx}
            # calibration frames are distinct packets (unique headers);
            # scoreboard them under a pseudo-source index (nb+a) so the
            # key neither collides with the traffic pair (a, dst) nor
            # breaks the (src, dst) 2-tuple unpack in the matcher
            exp.update({(nb + a, dst_idx): hp
                        for (a, b), hp in cal.items() if b == dst_idx})
            if len(frames) != len(exp):
                raise AssertionError(
                    f"{tag}: boundary b{dst_idx} received {len(frames)} "
                    f"data frames, expected {len(exp)} (one per source "
                    "plus calibration)")
            self._match_expected_frames(f'b{dst_idx}', dst_idx, exp, frames,
                                        tag)
        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh tetrad (a): all 12 ordered pairs 1 hop "
            f"(edge={edge_1hop}c, DOR-diag={diag_2hop}c), exact-once "
            f"scoreboard clean")

    # ------------------------------------------------------------------
    # Scenario (b): diagonal-pair bandwidth, no hidden detour
    # ------------------------------------------------------------------
    async def _diag_stream_driver(self, src_bidx, dst_bidx, npkts, beats,
                                  base_pid, tag):
        """Raw-drive npkts x beats back-to-back at the producer's line
        rate (a beat every cycle the boundary accepts one); returns
        {pid: injection cycle of the packet's head beat}."""
        s = f'b{src_bidx}'
        sv = self._sig(s, 's_axis_tvalid')
        sr = self._sig(s, 's_axis_tready')
        sd = self._sig(s, 's_axis_tdata')
        su = self._sig(s, 's_axis_tuser')
        sl = self._sig(s, 's_axis_tlast')
        pkts = []
        for k in range(npkts):
            pid = base_pid + k
            header = self.build_header(
                dst=self.BOUNDARY_COORDS[dst_bidx],
                src=self.BOUNDARY_COORDS[src_bidx],
                qos=1, packet_id=pid)
            payload = [
                ((0xD1A << 48) | (src_bidx << 44) | (dst_bidx << 40)
                 | ((pid & 0x3FF) << 8) | j)
                for j in range(beats)]
            pkts.append((pid, header, payload))

        head_cycle = {}
        cyc = 0
        beat_q = [(pid, header, j, data, j == len(payload) - 1)
                  for pid, header, payload in pkts
                  for j, data in enumerate(payload)]
        sv.value = 1
        for pid, header, j, data, last in beat_q:
            sd.value = data
            su.value = header if j == 0 else 0
            sl.value = 1 if last else 0
            while True:
                await RisingEdge(self.aclk)
                cyc += 1
                if int(sv.value) and int(sr.value):
                    break
                if cyc > 20000:
                    raise AssertionError(
                        f"{tag}: b{src_bidx} producer stalled at "
                        f"packet {pid} beat {j}")
            if j == 0:
                head_cycle[pid] = cyc
        sv.value = 0
        sl.value = 0
        su.value = 0
        sd.value = 0
        return head_cycle

    async def _diag_stream_monitor(self, dst_bidx, exp_src, npkts, beats,
                                   tag):
        """Watch a boundary m_axis beat by beat; verify every beat exact
        against the driver's construction and return
        {pid: ejection cycle of the packet's last beat}."""
        d = f'b{dst_bidx}'
        dv = self._sig(d, 'm_axis_tvalid')
        dr = self._sig(d, 'm_axis_tready')
        dd = self._sig(d, 'm_axis_tdata')
        du = self._sig(d, 'm_axis_tuser')
        dl = self._sig(d, 'm_axis_tlast')
        last_cycle = {}
        seen = 0       # packets completed
        j = 0          # beat index within the current packet
        cyc = 0
        while seen < npkts:
            await RisingEdge(self.aclk)
            cyc += 1
            if not (int(dv.value) and int(dr.value)):
                if cyc > 20000:
                    raise AssertionError(
                        f"{tag}: b{dst_bidx} saw {seen}/{npkts} packets")
                continue
            data = int(dd.value)
            user = int(du.value)
            last = int(dl.value)
            pid = (data >> 8) & 0x3FF
            j = data & 0xFF
            exp_data = ((0xD1A << 48) | (exp_src << 44) | (dst_bidx << 40)
                        | (pid << 8) | j)
            exp_header = self.build_header(
                dst=self.BOUNDARY_COORDS[dst_bidx],
                src=self.BOUNDARY_COORDS[exp_src],
                qos=1, packet_id=pid)
            exp_user = exp_header if j == 0 else 0
            exp_last = 1 if j == beats - 1 else 0
            if data != exp_data or user != exp_user or last != exp_last:
                raise AssertionError(
                    f"{tag}: b{dst_bidx} beat 0x{data:x}/0x{user:x}/"
                    f"{last} != expected 0x{exp_data:x}/0x{exp_user:x}/"
                    f"{exp_last}")
            if last:
                seen += 1
                last_cycle[pid] = cyc
                j = 0
            else:
                j += 1
        return last_cycle

    async def _axis_idle_witness(self, first_cycle, stop_event, tag):
        """Sample every inter-cell axis-port m_tvalid each cycle from
        `first_cycle` until `stop_event`: any toggle is a detour (in
        isolation the only legal inter-cell traffic is P_DIA). Returns
        the observed P_DIA m_tvalid cycle counts per diagonal cell."""
        cell_m = self.dut.u_dut.cell_m_tvalid
        axis_hits = 0
        dia_cycles = {(0, 0): 0, (1, 1): 0}
        cyc = 0
        while not stop_event.is_set():
            await RisingEdge(self.aclk)
            cyc += 1
            if cyc < first_cycle:
                continue
            for x in (0, 1):
                for y in (0, 1):
                    for p in self.AXIS_IDXS:
                        if int(cell_m[x][y][0][p].value):
                            axis_hits += 1
            for xy in ((0, 0), (1, 1)):
                if int(cell_m[xy[0]][xy[1]][0][self.P_DIA_IDX].value):
                    dia_cycles[xy] += 1
        if axis_hits != 0:
            raise AssertionError(
                f"{tag}: inter-cell axis-port activity observed during "
                f"the isolated diagonal burst ({axis_hits} samples) -- "
                "a hidden multi-hop detour carried traffic")
        return dia_cycles

    async def run_tetrad_diag_bandwidth(self):
        """Sustained back-to-back b0<->b3 (diagonal mates) in both
        directions concurrently: every packet keeps the exact 1-hop
        injection->ejection latency (a detour adds a fixed hop latency
        per packet), the delivery window matches the full-rate pipeline
        arithmetic (1 flit/clk minus the documented per-packet grant
        bubble), the axis links stay completely idle (witness), and all
        beats deliver exactly."""
        tag = "tetrad-bw"
        npkts = {'gate': 4, 'func': 8, 'full': 16}[self.TEST_LEVEL]
        beats = 4  # == input FIFO DEPTH: maximal buffering pressure

        await self._switch_and_wait(0, 9, 4, tag)
        # fresh 1-hop baseline on the diagonal pair, post-switch
        _, _, base = await self._pair_latency(0, 3, self._next_pid(),
                                              f"{tag}:baseline")

        stop_witness = cocotb.triggers.Event()
        witness = cocotb.start_soon(self._axis_idle_witness(1, stop_witness,
                                                            tag))
        d0 = cocotb.start_soon(self._diag_stream_driver(
            0, 3, npkts, beats, 0x100, f"{tag}:b0"))
        d1 = cocotb.start_soon(self._diag_stream_driver(
            3, 0, npkts, beats, 0x200, f"{tag}:b3"))
        m0 = cocotb.start_soon(self._diag_stream_monitor(
            3, 0, npkts, beats, f"{tag}:b3"))
        m1 = cocotb.start_soon(self._diag_stream_monitor(
            0, 3, npkts, beats, f"{tag}:b0"))
        head0 = await d0
        head1 = await d1
        last0 = await m0   # b3's ejections: b0's packets
        last1 = await m1   # b0's ejections: b3's packets
        await self.wait_clocks('aclk', 5)
        stop_witness.set()
        dia_cycles = await witness

        # every beat of both streams presented on the diagonal link (one
        # tvalid cycle per beat; the credit-gated presentation never
        # raises tvalid on a blocked link) and none on any axis port
        # (the witness already raised on axis activity)
        for xy in ((0, 0), (1, 1)):
            if dia_cycles[xy] != npkts * beats:
                raise AssertionError(
                    f"{tag}: P_DIA m_tvalid cycles at cell {xy} == "
                    f"{dia_cycles[xy]}, expected {npkts * beats} (full "
                    "rate on the diagonal link; beats went elsewhere?)")

        # Per-packet latency: the 1-hop baseline plus this packet's
        # remaining beats transferring serially (1 flit/clk) plus a small
        # pipeline-fill offset -- the input FIFO is exactly one packet
        # deep (DEPTH == beats), so the queue fills by a cycle or two for
        # the first packets and then holds steady (measured: base+beats-1
        # + 0/1/2). The latency bound alone cannot exclude a detour at
        # single-hop granularity (one hop measures 2 cycles in scenario
        # (a)'s calibration), so the sharp no-detour instrument is the
        # axis-idle witness below plus the exact P_DIA activity counts:
        # every beat of both streams must present on the diagonal link
        # and none on any axis port.
        exp_min = base + beats - 1
        all_lat = ([last0[pid] - h for pid, h in head0.items()] +
                   [last1[pid] - h for pid, h in head1.items()])
        fill_margin = 2
        for label, lats in (("b0->b3",
                             [last0[pid] - h for pid, h in head0.items()]),
                            ("b3->b0",
                             [last1[pid] - h for pid, h in head1.items()])):
            for k, l in enumerate(lats):
                if not (exp_min <= l <= exp_min + fill_margin):
                    raise AssertionError(
                        f"{tag}: {label} packet {k} latency {l}, expected "
                        f"[{exp_min}, {exp_min + fill_margin}] (1 hop + "
                        f"serial beats; a 2-hop detour adds a full hop)")
        # the queue must not grow without bound: the last packet is no
        # slower than the steady-state region (fill completes by pkt 3)
        for label, lats in (("b0->b3",
                             [last0[pid] - h for pid, h in head0.items()]),
                            ("b3->b0",
                             [last1[pid] - h for pid, h in head1.items()])):
            if lats[-1] > lats[min(2, len(lats) - 1)]:
                raise AssertionError(
                    f"{tag}: {label} queue grew: last packet latency "
                    f"{lats[-1]} > steady {lats[min(2, len(lats)-1)]}")

        # sustained full rate per direction: the producer injects a beat
        # every acceptance cycle; the path adds the 1-cycle grant bubble
        # per packet boundary: window == (npkts-1)*(beats+1) + (beats-1)
        # + base, worst case a couple of cycles looser.
        for head, last, label in ((head0, last0, "b0->b3"),
                                  (head1, last1, "b3->b0")):
            first = min(head.values())
            fin = max(last.values())
            window = fin - first
            exp_window = (npkts - 1) * (beats + 1) + (beats - 1) + base
            if window > exp_window + 4:
                raise AssertionError(
                    f"{tag}: {label} delivery window {window}c, expected "
                    f"<= {exp_window + 4}c (full rate minus the documented "
                    f"per-packet bubble; {exp_window}c ideal)")

        self._check_zero_err(tag)
        # non-participating cells (b1, b2) saw no data traffic at all
        for bidx in (1, 2):
            if self._data_frame_count(f'b{bidx}') != 0:
                raise AssertionError(
                    f"{tag}: b{bidx} received "
                    f"{self._data_frame_count(f'b{bidx}')} data frames, "
                    "expected 0 (leak/detour into a non-participant)")
        self.log.info(
            f"delta mesh tetrad (b): diagonal pair full rate both "
            f"directions ({npkts}x{beats} each way, 1-hop latency {base}c "
            f"held per packet, P_DIA tvalid cycles {dia_cycles}, axis "
            f"links idle)")


class DeltaMeshQoSTB(DeltaMeshCellTB):
    """TB for the Task 7 QoS arbiter: strict priority (latency ahead of
    queued bulk), aging inversion, the bulk minimum reservation, and the
    class-0 data mapping / qos 2/3 routing coverage promised in the
    Task 5 review. Derived from the cell TB on the same harness
    (dv/tb/delta_mesh_cell_th.sv, POS (1,1,0) of 4x4x1, AGING_LIMIT=64
    and BULK_MIN_CREDITS=1 = the cell parameter defaults).

    Contention construction: 'xpos' is the output under test (dst
    (3,0,0) at POS (1,1,0) DOR-routes P_X_POS from every input port).
    A raw-drive latency stream on 'local' saturates the output with
    single-beat class-1 packets at the service rate (1 packet per
    grant+bubble pair of cycles); single-beat 'xneg' packets carry the
    challenger. Raw drive (precedent: the tetrad TB) gives cycle-exact
    acceptance/ejection stamps; the BFM producers' pipeline turnaround
    would smear them.

    QoS class decode under test (controller-pinned): header qos 1 =
    latency, qos 2 = bulk; qos 0 data on a non-local destination maps
    to the latency class (class 0 is reserved to the control plane);
    qos 3 is unassigned in the spec's 3-class table and decodes to the
    bulk class. Aging and the bulk reservation are both pinned to the
    AGING_LIMIT horizon, so scenarios (b) and (c) bracket the same
    trigger from two observables: a challenger must WAIT roughly
    AGING_LIMIT cycles under saturation (floor) yet never longer than
    AGING_LIMIT + grant latency (ceiling).
    """

    XPOS = 'xpos'
    AGING_LIMIT = 64   # cell parameter default; harness default matches
    CEIL_MARGIN = 4    # pick-phase + grant-registration slack

    # ------------------------------------------------------------------
    # Raw signal helpers (cycle-exact drive/observe)
    # ------------------------------------------------------------------
    def _s(self, port, field):
        return getattr(self.dut, f'{port}_s_axis_{field}')

    def _m(self, port, field):
        return getattr(self.dut, f'{port}_m_axis_{field}')

    def _qos(self, header):
        lo, w = self.hdr_offsets['qos']
        return (header >> lo) & ((1 << w) - 1)

    def _pid(self, header):
        lo, w = self.hdr_offsets['packet_id']
        return (header >> lo) & ((1 << w) - 1)

    def _bulk_starved_xpos(self):
        """The cell's o_bulk_starved bit for 'xpos' (port index 1), or
        None when the harness predates the Task 7 observability port."""
        sig = getattr(self.dut, 'bulk_starved', None)
        if sig is None:
            return None
        return (int(sig.value) >> 1) & 1

    # ------------------------------------------------------------------
    # Scenario (a): strict priority -- latency jumps the bulk queue
    # ------------------------------------------------------------------
    async def run_strict_priority(self):
        """Bulk-saturate 'xpos' from 'local'; inject ONE latency packet
        from 'xneg'. It must eject within 3 cycles of its head's
        acceptance and ahead of every bulk packet injected after it.
        Round-robin arbitration (the pre-Task-7 policy) rotates the
        grant and can hold the latency packet a full bulk grant longer
        (> 3 cycles); strict priority passes."""
        tag = "strict-priority"
        N_BULK = 8
        bulk = []
        for k in range(N_BULK):
            header = self.build_header(dst=(3, 0, 0), src=self.POS, qos=2,
                                       packet_id=0x100 + k)
            bulk.append((header, (0xB0 << 56) | (0xA5 << 48) | k))
        lat_header = self.build_header(dst=(3, 0, 0), src=(0, 1, 0), qos=1,
                                       packet_id=0x1FF)
        lat_data = (0x1A << 56) | (0x5A << 48) | 0xFF

        l_v = self._s('local', 'tvalid')
        l_r = self._s('local', 'tready')
        l_d = self._s('local', 'tdata')
        l_u = self._s('local', 'tuser')
        l_l = self._s('local', 'tlast')
        x_v = self._s('xneg', 'tvalid')
        x_r = self._s('xneg', 'tready')
        x_d = self._s('xneg', 'tdata')
        x_u = self._s('xneg', 'tuser')
        x_l = self._s('xneg', 'tlast')
        q_v = self._m(self.XPOS, 'tvalid')
        q_r = self._m(self.XPOS, 'tready')
        q_d = self._m(self.XPOS, 'tdata')
        q_u = self._m(self.XPOS, 'tuser')

        x_v.value = 0
        x_l.value = 0
        x_u.value = 0
        x_d.value = 0
        bulk_i = 0
        l_v.value = 1
        l_d.value = bulk[0][1]
        l_u.value = bulk[0][0]
        l_l.value = 1

        injected = False
        accept_cyc = None
        ejects = []
        lat_eject = None
        cyc = 0
        # Single loop to the last ejection: the producer must be
        # serviced for the WHOLE run -- the input FIFO (DEPTH=4)
        # throttles it to the output's service rate, so it is still
        # presenting beats long after the challenger ejects; a drain
        # loop that stops driving it would re-accept the held beat.
        while len(ejects) < N_BULK + 1:
            await RisingEdge(self.aclk)
            cyc += 1
            if cyc > 3000:
                raise AssertionError(
                    f"{tag}: only {len(ejects)} of {N_BULK + 1} frames "
                    "ejected")
            if int(q_v.value) and int(q_r.value):
                ejects.append((cyc, int(q_u.value), int(q_d.value)))
                if accept_cyc is not None and \
                        int(q_u.value) == lat_header and \
                        int(q_d.value) == lat_data:
                    lat_eject = cyc
            if int(l_v.value) and int(l_r.value):
                bulk_i += 1
                if bulk_i < N_BULK:
                    l_d.value = bulk[bulk_i][1]
                    l_u.value = bulk[bulk_i][0]
                    l_l.value = 1
                else:
                    l_v.value = 0
                    l_l.value = 0
                    l_u.value = 0
                    l_d.value = 0
            if injected and accept_cyc is None and \
                    int(x_v.value) and int(x_r.value):
                accept_cyc = cyc
                x_v.value = 0
                x_l.value = 0
                x_u.value = 0
                x_d.value = 0
            # arm AFTER the acceptance check so the just-deposited
            # tvalid is never mistaken for a presented beat
            if not injected and len(ejects) >= 2:
                x_v.value = 1
                x_d.value = lat_data
                x_u.value = lat_header
                x_l.value = 1
                injected = True

        latency = latency_gap = None
        for i, (c, u, d) in enumerate(ejects):
            if u == lat_header and d == lat_data:
                latency = (c, u, d)
                latency_gap = c - accept_cyc
                for (c2, u2, _d2) in ejects[i + 1:]:
                    if self._qos(u2) != 2:
                        raise AssertionError(
                            f"{tag}: a non-bulk frame ejected after the "
                            f"latency packet (head 0x{u2:x})")
                break
        if latency is None:
            raise AssertionError(f"{tag}: latency frame missing on 'xpos'")
        if latency_gap > 3:
            raise AssertionError(
                f"{tag}: latency ejected {latency_gap} cycles after "
                f"acceptance, expected <= 3 (strict priority under bulk "
                f"saturation)")
        # frames ejected between the latency acceptance and its ejection
        # must all be bulk that was already queued (never re-ordered
        # ahead of it by class)
        for (c, u, _d) in ejects:
            if accept_cyc < c < lat_eject and u == lat_header:
                raise AssertionError(
                    f"{tag}: latency frame ejected out of order")

        exp = {h: d for h, d in bulk}
        exp[lat_header] = lat_data
        seen_bulk = set()
        for (_c, u, d) in ejects:
            if u not in exp or exp[u] != d:
                raise AssertionError(
                    f"{tag}: ejected frame 0x{d:x}/0x{u:x} does not match "
                    "any injected packet (corruption/misdelivery)")
            if self._qos(u) == 2:
                if u in seen_bulk:
                    raise AssertionError(
                        f"{tag}: bulk frame 0x{u:x} ejected twice")
                seen_bulk.add(u)
        if len(seen_bulk) != N_BULK:
            raise AssertionError(
                f"{tag}: {len(seen_bulk)} distinct bulk frames ejected, "
                f"expected {N_BULK}")
        if int(self.dut.err_drop_cnt.value) != 0:
            raise AssertionError(
                f"{tag}: err_drop_cnt "
                f"{int(self.dut.err_drop_cnt.value)}, expected 0")
        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({self.XPOS}, tag)
        self.log.info(
            f"delta mesh qos (a): strict priority -- latency ejected "
            f"{latency_gap} cycles after acceptance (<= 3), ahead of the "
            f"queued bulk, {N_BULK} bulk intact")

    # ------------------------------------------------------------------
    # Scenario (b): aging inversion -- an aged bulk head wins the grant
    # ------------------------------------------------------------------
    async def run_aging_inversion(self):
        """Latency-saturate 'xpos' from 'local'; inject ONE bulk packet
        from 'xneg'. Under strict priority alone it would starve; with
        aging (and the same-horizon bulk reservation) it must WAIT at
        least ~AGING_LIMIT cycles and then win, ejecting no later than
        AGING_LIMIT + grant latency. Round-robin (pre-Task-7) ejects the
        challenger within a couple of grants, failing the wait floor."""
        tag = "aging"
        N_LAT = 48
        lat = []
        for k in range(N_LAT):
            header = self.build_header(dst=(3, 0, 0), src=self.POS, qos=1,
                                       packet_id=0x200 + k)
            lat.append((header, (0x11 << 56) | (0xA5 << 48) | k))
        blk_header = self.build_header(dst=(3, 0, 0), src=(0, 1, 0), qos=2,
                                       packet_id=0x2FF)
        blk_data = (0xB2 << 56) | (0x5A << 48) | 0xF0

        l_v = self._s('local', 'tvalid')
        l_r = self._s('local', 'tready')
        l_d = self._s('local', 'tdata')
        l_u = self._s('local', 'tuser')
        l_l = self._s('local', 'tlast')
        x_v = self._s('xneg', 'tvalid')
        x_r = self._s('xneg', 'tready')
        x_d = self._s('xneg', 'tdata')
        x_u = self._s('xneg', 'tuser')
        x_l = self._s('xneg', 'tlast')
        q_v = self._m(self.XPOS, 'tvalid')
        q_r = self._m(self.XPOS, 'tready')
        q_d = self._m(self.XPOS, 'tdata')
        q_u = self._m(self.XPOS, 'tuser')

        x_v.value = 0
        x_l.value = 0
        x_u.value = 0
        x_d.value = 0
        lat_i = 0
        l_v.value = 1
        l_d.value = lat[0][1]
        l_u.value = lat[0][0]
        l_l.value = 1

        injected = False
        accept_cyc = None
        bulk_eject = None
        ejects = []
        starved_seen = False
        cyc = 0
        # Single loop to the last ejection (see scenario (a)): the
        # latency producer is throttled by the input FIFO and is still
        # presenting beats after the bulk ejects.
        while len(ejects) < N_LAT + 1:
            await RisingEdge(self.aclk)
            cyc += 1
            if cyc > 6000:
                raise AssertionError(
                    f"{tag}: only {len(ejects)} of {N_LAT + 1} frames "
                    f"ejected after {cyc} cycles (bulk_eject="
                    f"{bulk_eject}) -- aging/reservation starved bulk "
                    "forever" if bulk_eject is None else
                    f"{tag}: only {len(ejects)} of {N_LAT + 1} frames "
                    "ejected after 6000 cycles")
            if int(q_v.value) and int(q_r.value):
                ejects.append((cyc, int(q_u.value), int(q_d.value)))
                if accept_cyc is not None and \
                        int(q_u.value) == blk_header and \
                        int(q_d.value) == blk_data:
                    bulk_eject = cyc
            if int(l_v.value) and int(l_r.value):
                lat_i += 1
                if lat_i < N_LAT:
                    l_d.value = lat[lat_i][1]
                    l_u.value = lat[lat_i][0]
                    l_l.value = 1
                else:
                    l_v.value = 0
                    l_l.value = 0
                    l_u.value = 0
                    l_d.value = 0
            if injected and accept_cyc is None and \
                    int(x_v.value) and int(x_r.value):
                accept_cyc = cyc
                x_v.value = 0
                x_l.value = 0
                x_u.value = 0
                x_d.value = 0
            # arm AFTER the acceptance check so the just-deposited
            # tvalid is never mistaken for a presented beat
            if not injected and \
                    sum(1 for (_c, u, _d) in ejects
                        if self._qos(u) == 1) >= 6:
                x_v.value = 1
                x_d.value = blk_data
                x_u.value = blk_header
                x_l.value = 1
                injected = True
            starved = self._bulk_starved_xpos()
            if starved:
                starved_seen = True

        if bulk_eject is None:
            raise AssertionError(
                f"{tag}: bulk packet never ejected under latency "
                "saturation -- aging/reservation starved it forever")
        present = accept_cyc + 1   # head requests from the cycle after
        waited = bulk_eject - present
        if waited < 8:
            raise AssertionError(
                f"{tag}: bulk ejected only {waited} cycles after becoming "
                f"eligible -- it never waited under saturation (expected "
                f"~{self.AGING_LIMIT}: aging/reservation not enforced)")
        if waited > self.AGING_LIMIT + self.CEIL_MARGIN:
            raise AssertionError(
                f"{tag}: bulk waited {waited} cycles, expected <= "
                f"{self.AGING_LIMIT + self.CEIL_MARGIN} (aging horizon + "
                "grant latency)")
        if self._bulk_starved_xpos() is not None and not starved_seen:
            raise AssertionError(
                f"{tag}: o_bulk_starved[xpos] never asserted before the "
                "bulk grant -- the starve counter is not counting")
        # every eject before the bulk grant is a latency frame, in order
        pre = [(c, u, d) for (c, u, d) in ejects if c < bulk_eject]
        for i, (_c, u, d) in enumerate(pre):
            if u != lat[i][0] or d != lat[i][1]:
                raise AssertionError(
                    f"{tag}: pre-bulk eject #{i} 0x{d:x}/0x{u:x} != "
                    f"expected latency frame (corruption/reorder)")

        # scoreboard by content: the bulk frame ejected mid-stream
        # (that is the point), so match the latency frames as an
        # ordered subsequence and require exactly one bulk eject, at
        # the recorded cycle
        lat_frames = [(c, u, d) for (c, u, d) in ejects
                      if self._qos(u) == 1]
        blk_frames = [(c, u, d) for (c, u, d) in ejects
                      if self._qos(u) == 2]
        if len(blk_frames) != 1 or blk_frames[0][0] != bulk_eject or \
                blk_frames[0][1] != blk_header or blk_frames[0][2] != blk_data:
            raise AssertionError(
                f"{tag}: expected exactly one bulk eject at cycle "
                f"{bulk_eject}, got {[(c, hex(u)) for (c, u, _d) in blk_frames]}")
        if len(lat_frames) != N_LAT:
            raise AssertionError(
                f"{tag}: {len(lat_frames)} latency frames ejected, "
                f"expected {N_LAT}")
        for i, (_c, u, d) in enumerate(lat_frames):
            if u != lat[i][0] or d != lat[i][1]:
                trace = ", ".join(
                    f"{_c}:{self._pid(u2):#x}" for (_c, u2, _d2) in ejects)
                raise AssertionError(
                    f"{tag}: latency eject #{i} 0x{d:x}/0x{u:x} != "
                    f"expected 0x{lat[i][1]:x}/0x{lat[i][0]:x} "
                    f"(corruption/reorder); ejects[cyc:pid] = {trace}")
        if int(self.dut.err_drop_cnt.value) != 0:
            raise AssertionError(
                f"{tag}: err_drop_cnt "
                f"{int(self.dut.err_drop_cnt.value)}, expected 0")
        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({self.XPOS}, tag)
        self.log.info(
            f"delta mesh qos (b): aging -- bulk waited {waited} cycles "
            f"(floor 8, ceiling {self.AGING_LIMIT + self.CEIL_MARGIN}), "
            f"then won the grant; {N_LAT} latency frames exact, one bulk")

    # ------------------------------------------------------------------
    # Scenario (c): bulk minimum reservation -- >= 1 grant per window
    # ------------------------------------------------------------------
    async def run_bulk_reservation(self):
        """Latency-saturate 'xpos' from 'local' for the whole run; a
        fresh single-beat bulk packet is re-armed on 'xneg' the cycle
        after the previous one ejects, keeping bulk eligible across
        several reservation periods. Consecutive bulk grants must be
        spaced at least a few cycles (strict priority still defers bulk
        -- round-robin would grant every other packet, failing the
        floor) and at most AGING_LIMIT + grant latency apart (the
        BULK_MIN_CREDITS=1 reservation: >= 1 bulk grant per AGING_LIMIT
        eligible cycles)."""
        tag = "reservation"
        LIMIT = self.AGING_LIMIT
        N_BULK = 5
        N_LAT = 260
        lat = []
        for k in range(N_LAT):
            header = self.build_header(dst=(3, 0, 0), src=self.POS, qos=1,
                                       packet_id=0x300 + k)
            lat.append((header, (0x22 << 56) | (0xA5 << 48) | k))

        l_v = self._s('local', 'tvalid')
        l_r = self._s('local', 'tready')
        l_d = self._s('local', 'tdata')
        l_u = self._s('local', 'tuser')
        l_l = self._s('local', 'tlast')
        x_v = self._s('xneg', 'tvalid')
        x_r = self._s('xneg', 'tready')
        x_d = self._s('xneg', 'tdata')
        x_u = self._s('xneg', 'tuser')
        x_l = self._s('xneg', 'tlast')
        q_v = self._m(self.XPOS, 'tvalid')
        q_r = self._m(self.XPOS, 'tready')
        q_d = self._m(self.XPOS, 'tdata')
        q_u = self._m(self.XPOS, 'tuser')

        def arm_bulk(k):
            header = self.build_header(dst=(3, 0, 0), src=(0, 1, 0), qos=2,
                                       packet_id=0x3E0 + k)
            data = (0xC3 << 56) | (0x5A << 48) | k
            x_v.value = 1
            x_d.value = data
            x_u.value = header
            x_l.value = 1
            return header, data

        x_v.value = 0
        x_l.value = 0
        x_u.value = 0
        x_d.value = 0
        lat_i = 0
        l_v.value = 1
        l_d.value = lat[0][1]
        l_u.value = lat[0][0]
        l_l.value = 1

        bulk_ejects = []
        blk = None
        starved_seen = False
        cyc = 0
        while len(bulk_ejects) < N_BULK:
            await RisingEdge(self.aclk)
            cyc += 1
            if cyc > 20000:
                raise AssertionError(
                    f"{tag}: only {len(bulk_ejects)} of {N_BULK} bulk "
                    "grants observed")
            if int(q_v.value) and int(q_r.value):
                u = int(q_u.value)
                d = int(q_d.value)
                if blk is not None and u == blk[0] and d == blk[1]:
                    bulk_ejects.append(cyc)
                    blk = None
            if int(l_v.value) and int(l_r.value):
                lat_i += 1
                if lat_i < N_LAT:
                    l_d.value = lat[lat_i][1]
                    l_u.value = lat[lat_i][0]
                    l_l.value = 1
                else:
                    l_v.value = 0
                    l_l.value = 0
                    l_u.value = 0
                    l_d.value = 0
            if int(x_v.value) and int(x_r.value):
                # a presented bulk beat was accepted at this edge
                x_v.value = 0
                x_l.value = 0
                x_u.value = 0
                x_d.value = 0
            # arm AFTER the acceptance check so the just-deposited
            # tvalid is never mistaken for a presented beat; re-arm the
            # cycle after the previous bulk ejected (blk cleared above)
            if blk is None and (len(bulk_ejects) > 0 or lat_i >= 6):
                blk = arm_bulk(len(bulk_ejects))
            starved = self._bulk_starved_xpos()
            if starved:
                starved_seen = True

        gaps = [bulk_ejects[i + 1] - bulk_ejects[i]
                for i in range(len(bulk_ejects) - 1)]
        for gap in gaps:
            if gap < 8:
                raise AssertionError(
                    f"{tag}: bulk grants {gap} cycles apart -- bulk is "
                    "not being deferred between reservations "
                    "(round-robin-like arbitration?)")
            if gap > LIMIT + self.CEIL_MARGIN:
                raise AssertionError(
                    f"{tag}: bulk grants {gap} cycles apart, expected "
                    f"<= {LIMIT + self.CEIL_MARGIN} (BULK_MIN_CREDITS=1: "
                    f">= 1 bulk grant per {LIMIT} eligible cycles)")
        if self._bulk_starved_xpos() is not None and not starved_seen:
            raise AssertionError(
                f"{tag}: o_bulk_starved[xpos] never asserted -- the "
                "starve counter is not counting")
        if int(self.dut.err_drop_cnt.value) != 0:
            raise AssertionError(
                f"{tag}: err_drop_cnt "
                f"{int(self.dut.err_drop_cnt.value)}, expected 0")
        self.log.info(
            f"delta mesh qos (c): bulk reservation -- {N_BULK} bulk "
            f"grants at gaps {gaps}, each within "
            f"[8, {LIMIT + self.CEIL_MARGIN}]")

    # ------------------------------------------------------------------
    # Scenario (d): qos 2/3 data routing + the class-0 data mapping
    # ------------------------------------------------------------------
    async def run_class_routes(self):
        """Task 5 review promised coverage: data packets at qos 2 and 3
        route identically to class 1 at power-on (the table image is DOR
        in every qos region). Also pins the Task 7 class-0 ruling: a
        class-0 packet whose dst is NOT this cell is data (the config
        plane only claims dst == self), maps to the latency class, and
        must eject normally -- no config response, no drop."""
        tag = "class-routes"

        # qos 2 (bulk class) to dst (3,0,0) -> P_X_POS
        header = self.build_header(dst=(3, 0, 0), src=self.POS, qos=2,
                                   packet_id=0x400)
        payload = [0xCAFE_0002_0000_0001]
        await self._send_packet('local', header, payload)
        await self._expect_packet('xpos', header, payload, 1,
                                  f"{tag}: qos2 dst(3,0,0)")

        # qos 3 (unassigned; decoded to the bulk class) to dst (1,0,0)
        # at POS (1,1,0): x equal, y differs -> P_Y_NEG
        header = self.build_header(dst=(1, 0, 0), src=self.POS, qos=3,
                                   packet_id=0x401)
        payload = [0xCAFE_0003_0000_0001, 0xCAFE_0003_0000_0002]
        await self._send_packet('local', header, payload)
        await self._expect_packet('yneg', header, payload, 1,
                                  f"{tag}: qos3 dst(1,0,0)")

        # qos 3 arriving on a neighbor port routes the same DOR answer
        header = self.build_header(dst=(3, 0, 0), src=(0, 1, 0), qos=3,
                                   packet_id=0x402)
        payload = [0xCAFE_0003_0000_0003]
        await self._send_packet('xneg', header, payload)
        await self._expect_packet('xpos', header, payload, 2,
                                  f"{tag}: qos3 from xneg")

        # class-0 DATA packet, dst != self: not a config transaction --
        # it maps to the latency class and ejects as ordinary data.
        if self.slaves['local'].frames_received != 0:
            raise AssertionError(
                f"{tag}: local master saw "
                f"{self.slaves['local'].frames_received} frames before "
                "the class-0 packet, expected 0")
        header = self.build_header(dst=(3, 0, 0), src=self.POS, qos=0,
                                   packet_id=0x403)
        payload = [0xCAFE_0000_0000_0001]
        await self._send_packet('local', header, payload)
        await self._expect_packet('xpos', header, payload, 3,
                                  f"{tag}: qos0 data dst(3,0,0)")
        if self.slaves['local'].frames_received != 0:
            raise AssertionError(
                f"{tag}: class-0 data packet produced a config "
                "response on the local master")
        if int(self.dut.err_drop_cnt.value) != 0:
            raise AssertionError(
                f"{tag}: err_drop_cnt "
                f"{int(self.dut.err_drop_cnt.value)}, expected 0 "
                "(class-0 data must not drop)")
        await self.wait_clocks('aclk', 10)
        self._check_idle_ports({'xpos', 'yneg'}, tag)
        self.log.info(
            "delta mesh qos (d): qos 2/3 route identically to class 1 "
            "at power-on; class-0 data (dst != self) rides the latency "
            "class -- no config response, no drop")


class DeltaMeshTileTB(DeltaMeshTetradTB):
    """TB for mode 10 (tile all-to-all K4 of tetrads) + the P_DIA2
    inter-tetrad diagonal link (Task 6c), on the 4x4x1 fabric harness --
    a single tile of four tetrads:

        b0=(0,0,0) b1=(1,0,0) b2=(2,0,0) b3=(3,0,0)
        b4=(0,1,0) b5=(1,1,0) b6=(2,1,0) b7=(3,1,0)
        b8=(0,2,0) b9=(1,2,0) b10=(2,2,0) b11=(3,2,0)
        b12=(0,3,0) b13=(1,3,0) b14=(2,3,0) b15=(3,3,0)

    Diagonal-tetrad corner pairs (P_DIA2, 1 hop in mode 10):
        b5=(1,1,0) <-> b10=(2,2,0)
        b9=(1,2,0) <-> b6=(2,1,0)

    Edge-adjacent tetrads use the axis ports (1 hop for the shared
    boundary, otherwise DOR within the tile). Inter-tile dsts route DOR.

    The single-hop property for the diagonal-tetrad pairs is proven by
    injection->ejection LATENCY (calibrated live against power-on DOR,
    where the diagonal-tetrad pair is 2 hops) and by the axis-idle
    witness during isolated P_DIA2 bursts.
    """

    BOUNDARY_COORDS = (
        (0, 0, 0), (1, 0, 0), (2, 0, 0), (3, 0, 0),
        (0, 1, 0), (1, 1, 0), (2, 1, 0), (3, 1, 0),
        (0, 2, 0), (1, 2, 0), (2, 2, 0), (3, 2, 0),
        (0, 3, 0), (1, 3, 0), (2, 3, 0), (3, 3, 0),
    )
    PORTS = tuple((f'b{i}', i) for i in range(len(BOUNDARY_COORDS)))

    P_DIA2_IDX = P_DIA2
    AXIS_IDXS = (0, 1, 2, 3, 4, 5)

    def __init__(self, dut):
        super().__init__(dut)
        # Coordinate width for the 4x4 tile is 2 bits; the harness default
        # matches, but make sure the header builder uses it.
        self.COORD_W = self.convert_to_int(os.environ.get('TEST_COORD_W', '2'))
        self.hdr_offsets = build_header_offsets(self.COORD_W)

    # ------------------------------------------------------------------
    # Scenario (a): diagonal-tetrad pairs drop from 2-hop DOR to 1 hop
    # ------------------------------------------------------------------
    async def run_tile_k4_one_hop(self):
        """Diagonal-tetrad corner pairs b5<->b10 and b6<->b9 deliver in
        exactly 1 hop under mode 10; every other intra-tile pair is
        reachable. Calibration in power-on DOR: b5->b6 (edge-adjacent
        tetrad) is 1 hop, b5->b10 (diagonal-tetrad) is 2 hops.
        """
        tag = "tile-k4"

        # Calibration in power-on mode 0: 1-hop edge-adjacent reference
        # and 2-hop diagonal-tetrad reference.
        cal = {}
        h, d, edge_1hop = await self._pair_latency(
            5, 6, self._next_pid(), f"{tag}:cal-edge")
        cal[(5, 6)] = (h, [d])
        h, d, diag_2hop = await self._pair_latency(
            5, 10, self._next_pid(), f"{tag}:cal-diag")
        cal[(5, 10)] = (h, [d])
        if diag_2hop <= edge_1hop:
            raise AssertionError(
                f"{tag}: calibration cannot resolve hops: diagonal DOR "
                f"latency {diag_2hop} <= edge latency {edge_1hop}")

        # Switch to mode 10.
        await self._switch_and_wait(0, 10, 16, tag)

        # Measure the two diagonal-tetrad pairs in both directions plus a
        # representative edge-adjacent pair.
        diag_pairs = ((5, 10), (10, 5), (6, 9), (9, 6))
        expected = {}
        lat = {}
        for a, b in diag_pairs:
            header, data, l = await self._pair_latency(
                a, b, self._next_pid(), f"{tag}:{a}->{b}")
            lat[(a, b)] = l
            expected[(a, b)] = (header, [data])

        for a, b in diag_pairs:
            if lat[(a, b)] != edge_1hop:
                raise AssertionError(
                    f"{tag}: b{a}->b{b} latency {lat[(a,b)]} cycles, "
                    f"expected exactly the 1-hop latency {edge_1hop} "
                    f"(2-hop DOR would be {diag_2hop})")

        # A representative cross-tile / edge-adjacent delivery still works
        # (b0->b15 is 6 hops DOR; just verify it arrives, not the count).
        await self._expect_delivery(0, (3, 3, 0), 15, f"{tag}:corner-dor")

        await self.wait_clocks('aclk', 10)
        for dst_idx in (5, 6, 9, 10, 15):
            frames = self._group_frames(f'b{dst_idx}', tag)
            exp = {(a, dst_idx): hp for (a, b), hp in expected.items()
                   if b == dst_idx}
            exp.update({(len(self.BOUNDARY_COORDS) + a, dst_idx): hp
                        for (a, b), hp in cal.items() if b == dst_idx})
            if dst_idx == 15:
                # b0->b15 is checked by _expect_delivery above; the cal
                # frames are the only other expected frames at b15.
                pass
            else:
                if len(frames) != len(exp):
                    raise AssertionError(
                        f"{tag}: boundary b{dst_idx} received {len(frames)} "
                        f"data frames, expected {len(exp)}")
                self._match_expected_frames(f'b{dst_idx}', dst_idx, exp,
                                            frames, tag)
        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh tile (a): diagonal-tetrad pairs 1 hop "
            f"(edge={edge_1hop}c, DOR-diag={diag_2hop}c), reachable clean")

    # ------------------------------------------------------------------
    # Scenario (b): P_DIA2 full-rate bandwidth, axis links idle
    # ------------------------------------------------------------------
    async def run_tile_diag2_bandwidth(self):
        """Sustained back-to-back b5<->b10 and b6<->b9 in both directions
        concurrently under mode 10: every packet keeps the 1-hop latency,
        the delivery window matches full-rate arithmetic, the axis links
        stay completely idle (witness), and all beats deliver exactly.
        """
        tag = "tile-bw"
        npkts = {'gate': 4, 'func': 8, 'full': 16}[self.TEST_LEVEL]
        beats = 4

        await self._switch_and_wait(0, 10, 16, tag)
        _, _, base = await self._pair_latency(
            5, 10, self._next_pid(), f"{tag}:baseline")

        stop_witness = cocotb.triggers.Event()
        witness = cocotb.start_soon(self._axis_idle_witness(1, stop_witness,
                                                            tag))
        d0 = cocotb.start_soon(self._diag_stream_driver(
            5, 10, npkts, beats, 0x000, f"{tag}:b5"))
        d1 = cocotb.start_soon(self._diag_stream_driver(
            10, 5, npkts, beats, 0x100, f"{tag}:b10"))
        d2 = cocotb.start_soon(self._diag_stream_driver(
            6, 9, npkts, beats, 0x200, f"{tag}:b6"))
        d3 = cocotb.start_soon(self._diag_stream_driver(
            9, 6, npkts, beats, 0x300, f"{tag}:b9"))
        m0 = cocotb.start_soon(self._diag_stream_monitor(
            10, 5, npkts, beats, f"{tag}:b10"))
        m1 = cocotb.start_soon(self._diag_stream_monitor(
            5, 10, npkts, beats, f"{tag}:b5"))
        m2 = cocotb.start_soon(self._diag_stream_monitor(
            9, 6, npkts, beats, f"{tag}:b9"))
        m3 = cocotb.start_soon(self._diag_stream_monitor(
            6, 9, npkts, beats, f"{tag}:b6"))
        head0 = await d0
        head1 = await d1
        head2 = await d2
        head3 = await d3
        last0 = await m0
        last1 = await m1
        last2 = await m2
        last3 = await m3
        await self.wait_clocks('aclk', 5)
        stop_witness.set()
        dia_cycles = await witness

        # every beat of the four streams presented on the two P_DIA2
        # links and none on any axis port (the witness already raised on
        # axis activity).
        for xy in ((1, 1), (2, 2), (2, 1), (1, 2)):
            if dia_cycles[xy] != npkts * beats:
                raise AssertionError(
                    f"{tag}: P_DIA2 m_tvalid cycles at cell {xy} == "
                    f"{dia_cycles[xy]}, expected {npkts * beats} (full "
                    "rate on the diagonal link; beats went elsewhere?)")

        exp_min = base + beats - 1
        fill_margin = 2
        streams = (
            ("b5->b10", head0, last0),
            ("b10->b5", head1, last1),
            ("b6->b9", head2, last2),
            ("b9->b6", head3, last3),
        )
        for label, head, last in streams:
            lats = [last[pid] - h for pid, h in head.items()]
            for k, l in enumerate(lats):
                if not (exp_min <= l <= exp_min + fill_margin):
                    raise AssertionError(
                        f"{tag}: {label} packet {k} latency {l}, expected "
                        f"[{exp_min}, {exp_min + fill_margin}] (1 hop + "
                        "serial beats; a 2-hop detour adds a full hop)")
            if lats[-1] > lats[min(2, len(lats) - 1)]:
                raise AssertionError(
                    f"{tag}: {label} queue grew: last packet latency "
                    f"{lats[-1]} > steady {lats[min(2, len(lats)-1)]}")
            first = min(head.values())
            fin = max(last.values())
            window = fin - first
            exp_window = (npkts - 1) * (beats + 1) + (beats - 1) + base
            if window > exp_window + 4:
                raise AssertionError(
                    f"{tag}: {label} delivery window {window}c, expected "
                    f"<= {exp_window + 4}c (full rate minus the documented "
                    f"per-packet bubble; {exp_window}c ideal)")

        self._check_zero_err(tag)
        # non-participating boundaries saw no data traffic at all
        for bidx in (0, 1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15):
            if self._data_frame_count(f'b{bidx}') != 0:
                raise AssertionError(
                    f"{tag}: b{bidx} received "
                    f"{self._data_frame_count(f'b{bidx}')} data frames, "
                    "expected 0 (leak/detour into a non-participant)")
        self.log.info(
            f"delta mesh tile (b): diagonal-tetrad pairs full rate both "
            f"directions ({npkts}x{beats} each of 4 streams, 1-hop latency "
            f"{base}c held per packet, P_DIA2 tvalid cycles {dia_cycles}, "
            f"axis links idle)")

    # ------------------------------------------------------------------
    # Witness helper overrides for the 4x4 grid
    # ------------------------------------------------------------------
    async def _axis_idle_witness(self, first_cycle, stop_event, tag):
        """Sample every inter-cell axis-port m_tvalid each cycle: any
        toggle is a detour. Returns observed P_DIA2 m_tvalid cycle counts
        per diagonal-tetrad cell."""
        cell_m = self.dut.u_dut.cell_m_tvalid
        axis_hits = 0
        dia_cycles = {(1, 1): 0, (2, 2): 0, (2, 1): 0, (1, 2): 0}
        cyc = 0
        while not stop_event.is_set():
            await RisingEdge(self.aclk)
            cyc += 1
            if cyc < first_cycle:
                continue
            for x in range(4):
                for y in range(4):
                    for p in self.AXIS_IDXS:
                        if int(cell_m[x][y][0][p].value):
                            axis_hits += 1
            for xy in ((1, 1), (2, 2), (2, 1), (1, 2)):
                if int(cell_m[xy[0]][xy[1]][0][self.P_DIA2_IDX].value):
                    dia_cycles[xy] += 1
        if axis_hits != 0:
            raise AssertionError(
                f"{tag}: inter-cell axis-port activity observed during "
                f"the isolated P_DIA2 burst ({axis_hits} samples) -- "
                "a hidden multi-hop detour carried traffic")
        return dia_cycles


class DeltaMeshMulticastTB(DeltaMeshModesTB):
    """TB for Task 8 multicast: VC0-only, BRCP-conformed BFS-tree flood,
    source-side replication per cell, no responses.

    Reuses the 2x2x1 fabric harness.  Multicast packets are single-beat
    (the RTL replication stage is single-beat in this task) with
    mcast=1, qos=1 (latency data class), vc=0, and src set to the
    multicast source coordinate.  dst is set equal to src (ignored by
    the datapath but keeps the header unambiguous).
    """

    async def run_mcast_full_fabric(self, src_bidx=0):
        """A single multicast from b{src_bidx} reaches every local output
        exactly once."""
        tag = "mcast-full-fabric"
        nb = len(self.BOUNDARY_COORDS)
        before = self._data_frame_counts()
        header = self.build_mcast_header(
            src=self.BOUNDARY_COORDS[src_bidx],
            packet_id=self._next_pid())
        payload = [0xCAFE_0000_0000_0000 | (src_bidx << 56)]
        await self._send_packet(f'b{src_bidx}', header, payload)

        expected_per_dst = {
            dst_idx: {(src_bidx, dst_idx): (header, payload)}
            for dst_idx in range(nb)
        }
        for dst_idx in range(nb):
            await self._wait_frames(f'b{dst_idx}', before[dst_idx] + 1)

        await self.wait_clocks('aclk', 10)
        for dst_idx in range(nb):
            frames = self._group_frames(f'b{dst_idx}', tag)
            if len(frames) != before[dst_idx] + 1:
                raise AssertionError(
                    f"{tag}: boundary b{dst_idx} received {len(frames)} "
                    f"data frames, expected {before[dst_idx] + 1}")
            self._match_expected_frames(f'b{dst_idx}', dst_idx,
                                        expected_per_dst[dst_idx],
                                        frames[before[dst_idx]:], tag)
        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh multicast (a): b{src_bidx} mcast reached all "
            f"{nb} locals exactly once")

    async def run_mcast_response_drop(self, src_bidx=0):
        """A response-shaped unicast (dst == multicast source, mcast=0)
        injected at a different boundary is dropped at injection and
        counted; the fabric does not deadlock."""
        tag = "mcast-response-drop"
        nb = len(self.BOUNDARY_COORDS)
        resp_src_bidx = (src_bidx + 1) % nb
        before = self._data_frame_counts()
        before_err = self._err(resp_src_bidx)

        # Response-shaped packet: claims to return to the multicast source
        # coordinate, with mcast clear, injected away from that source.
        src_coord = self.BOUNDARY_COORDS[src_bidx]
        header = self.build_header(dst=src_coord, src=src_coord,
                                   qos=1, packet_id=self._next_pid())
        payload = [0xBAD0_0000_0000_0000]
        await self._send_packet(f'b{resp_src_bidx}', header, payload)

        for _ in range(200):
            await RisingEdge(self.aclk)
            if self._err(resp_src_bidx) == before_err + 1:
                break
        else:
            raise AssertionError(
                f"{tag}: err_drop_cnt at b{resp_src_bidx} == "
                f"{self._err(resp_src_bidx)}, expected {before_err + 1}")

        await self.wait_clocks('aclk', 50)
        after = self._data_frame_counts()
        for bidx, count in after.items():
            if count != before[bidx]:
                raise AssertionError(
                    f"{tag}: boundary b{bidx} gained {count - before[bidx]} "
                    "unexpected data frames from the response-shaped packet")
        self.log.info(
            "delta mesh multicast (b): response-shaped packet dropped at "
            f"b{resp_src_bidx}, err_drop_cnt = {self._err(resp_src_bidx)}")

    async def run_mcast_deadlock_soak(self):
        """Random unicast background plus periodic multicast on the 2x2x1
        fabric: no deadlock/livelock and all expected frames deliver.
        Seed is locked via self.SEED so the run is reproducible."""
        tag = "mcast-deadlock-soak"
        nb = len(self.BOUNDARY_COORDS)
        bg_pkts = {'gate': 1000, 'func': 100000, 'full': 200000}[
            self.TEST_LEVEL]
        bg_per_src = bg_pkts // nb
        mcast_interval = max(1, bg_per_src // 10)

        before = self._data_frame_counts()
        expected_increase = {bidx: 0 for bidx in range(nb)}
        b0_mcasts = []

        async def sender(src_bidx):
            port = f'b{src_bidx}'
            src_coord = self.BOUNDARY_COORDS[src_bidx]
            for i in range(bg_per_src):
                # Self-dst is allowed; it is a local delivery, not a
                # response-shaped packet because src == pos of source.
                dst_bidx = self.rng.randrange(nb)
                dst_coord = self.BOUNDARY_COORDS[dst_bidx]
                header = self.build_header(
                    dst=dst_coord, src=src_coord, qos=1,
                    packet_id=self._next_pid())
                payload = [((0xB6 << 56) | (src_bidx << 48)
                            | (dst_bidx << 40) | i)]
                expected_increase[dst_bidx] += 1
                await self._send_packet(port, header, payload)
                # Periodic multicast from b0 only.
                if src_bidx == 0 and (i + 1) % mcast_interval == 0:
                    m_header = self.build_mcast_header(
                        src=src_coord, packet_id=self._next_pid())
                    m_payload = [((0xB7 << 56) | (len(b0_mcasts) << 32)
                                  | i)]
                    b0_mcasts.append((m_header, m_payload))
                    for dst in range(nb):
                        expected_increase[dst] += 1
                    await self._send_packet(port, m_header, m_payload)

        senders = [cocotb.start_soon(sender(b)) for b in range(nb)]
        for s in senders:
            await s

        for bidx in range(nb):
            await self._wait_frames(f'b{bidx}',
                                    before[bidx] + expected_increase[bidx])

        await self.wait_clocks('aclk', 50)
        for bidx in range(nb):
            got = self._data_frame_count(f'b{bidx}')
            exp = before[bidx] + expected_increase[bidx]
            if got != exp:
                raise AssertionError(
                    f"{tag}: boundary b{bidx} received {got} data frames, "
                    f"expected {exp}")
        self._check_zero_err(tag)
        self.log.info(
            f"delta mesh multicast (c): deadlock soak passed -- "
            f"{bg_pkts} background packets + {len(b0_mcasts)} multicasts "
            "delivered exactly")
