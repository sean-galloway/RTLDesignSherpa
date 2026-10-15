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
from delta_mesh.header import build_header_offsets
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
    def build_header(self, dst, src, qos=0, vc=0, packet_id=0):
        """Pack a head-flit header int per delta_mesh.header layout."""
        hdr = 0
        for value, fields in ((dst, ('dst_x', 'dst_y', 'dst_z')),
                              (src, ('src_x', 'src_y', 'src_z'))):
            for coord, field in zip(value, fields):
                lo, width = self.hdr_offsets[field]
                hdr |= (coord & ((1 << width) - 1)) << lo
        for field, value in (('qos', qos), ('vc', vc), ('packet_id', packet_id)):
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
