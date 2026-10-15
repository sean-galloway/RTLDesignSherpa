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
from delta_mesh.tables import P_X_POS, P_Y_POS, table_index
from TBClasses.shared.tbbase import TBBase


class DeltaMeshCellTB(TBBase):
    """TB for delta_mesh_cell (default DOR) via its harness."""

    # Harness port prefixes, index == cell port id:
    #   0 = P_X_NEG, 1 = P_X_POS, 2 = P_Y_NEG, 3 = P_Y_POS,
    #   4 = P_Z_NEG, 5 = P_Z_POS, 6 = P_LOCAL
    PORTS = (
        ('xneg', 0),
        ('xpos', 1),
        ('yneg', 2),
        ('ypos', 3),
        ('zneg', 4),
        ('zpos', 5),
        ('local', 6),
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
    def build_header(self, dst, src, qos=0, vc=0, packet_id=0, sr_ptr=0):
        """Pack a head-flit header int per delta_mesh.header layout."""
        hdr = 0
        for value, fields in ((dst, ('dst_x', 'dst_y', 'dst_z')),
                              (src, ('src_x', 'src_y', 'src_z'))):
            for coord, field in zip(value, fields):
                lo, width = self.hdr_offsets[field]
                hdr |= (coord & ((1 << width) - 1)) << lo
        for field, value in (('qos', qos), ('vc', vc), ('sr_ptr', sr_ptr),
                             ('packet_id', packet_id)):
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

    def _check_destination(self, port, dst_idx, expected):
        """Scoreboard one boundary output against the expected packets."""
        nb = len(self.BOUNDARY_COORDS)
        beats = self.slaves[port].get_observed_packets()

        # Group the flat beat stream into TLAST-delimited frames. Arrival
        # order between packets is arbitrary (output contention at interior
        # cells); order within a frame must be exactly as sent.
        frames = []
        current = []
        for beat in beats:
            current.append(beat)
            if int(beat.fields.get('last', 0)):
                frames.append(current)
                current = []
        if current:
            raise AssertionError(
                f"fabric all-pairs: boundary {dst_idx} ended mid-packet "
                f"({len(current)} trailing beats without tlast)")
        if len(frames) != nb:
            raise AssertionError(
                f"fabric all-pairs: boundary {dst_idx} received {len(frames)} "
                f"packets, expected {nb} (one per source)")

        # Match frames to expectations by the head-flit header in TUSER;
        # duplicate heads mean a packet was duplicated, not just reordered.
        by_head = {}
        for frame in frames:
            head_user = int(frame[0].fields.get('user', 0))
            if head_user in by_head:
                raise AssertionError(
                    f"fabric all-pairs: boundary {dst_idx} received two "
                    f"packets with header 0x{head_user:x} (duplicate)")
            by_head[head_user] = frame

        for src_idx in range(nb):
            header, payload = expected[(src_idx, dst_idx)]
            frame = by_head.get(header)
            tag = f"b{src_idx}->b{dst_idx}"
            if frame is None:
                raise AssertionError(
                    f"fabric all-pairs: packet {tag} never arrived at "
                    f"boundary {dst_idx}")
            if len(frame) != len(payload):
                raise AssertionError(
                    f"fabric all-pairs: {tag} delivered {len(frame)} beats, "
                    f"expected {len(payload)}")
            for i, (beat, exp_data) in enumerate(zip(frame, payload)):
                got_data = int(beat.fields['data'])
                got_user = int(beat.fields.get('user', 0))
                exp_last = 1 if i == len(payload) - 1 else 0
                got_last = int(beat.fields.get('last', 0))
                if got_data != exp_data:
                    raise AssertionError(
                        f"fabric all-pairs: {tag} beat {i} data mismatch: "
                        f"got 0x{got_data:x}, expected 0x{exp_data:x}")
                if got_last != exp_last:
                    raise AssertionError(
                        f"fabric all-pairs: {tag} beat {i} tlast mismatch: "
                        f"got {got_last}, expected {exp_last}")
                exp_user = header if i == 0 else 0
                if got_user != exp_user:
                    raise AssertionError(
                        f"fabric all-pairs: {tag} beat {i} tuser mismatch: "
                        f"got 0x{got_user:x}, expected 0x{exp_user:x}")

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
    ``{table_index[15:0], entry[7:0]}`` (entry = {port_mask[6:0], vc}).
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
