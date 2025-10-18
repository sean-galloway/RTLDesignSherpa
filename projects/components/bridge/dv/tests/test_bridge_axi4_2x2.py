# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/[your-org]/rtldesignsherpa
#
# Module: test_bridge_axi4_2x2
# Purpose: Comprehensive test for 2x2 AXI4 Bridge Crossbar
#
# Documentation: PRD.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-18

"""
Comprehensive Test for 2x2 AXI4 Bridge Crossbar

This test validates the complete functionality of bridge_axi4_flat_2x2 using
simple queue-based verification:
- Send transactions using GAXI masters
- Receive transactions using GAXI slaves/monitors
- Compare transmit queues with receive queues
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add CocoTB framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper


class Bridge2x2TB:
    """Testbench for 2x2 AXI4 Bridge Crossbar - Queue-based verification"""

    def __init__(self, dut, log):
        self.dut = dut
        self.log = log
        self.clock = dut.aclk

        # Bridge configuration
        self.num_masters = 2
        self.num_slaves = 2
        self.data_width = 32
        self.addr_width = 32
        self.id_width = 4

        # Address map
        self.slave_base_addrs = [0x00000000, 0x10000000]
        self.slave_addr_range = 0x10000000

        # Master-side transmitters (send AW, W from masters)
        self.aw_masters = []
        self.w_masters = []
        self.b_slaves = []  # Receive B responses
        self.ar_masters = []
        self.r_slaves = []  # Receive R responses

        for m in range(self.num_masters):
            # AW channel - master drives
            aw_master = GAXIMaster(
                dut=dut,
                title=f"AW_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_aw_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="aw",
                multi_sig=True,
                log=log
            )
            self.aw_masters.append(aw_master)

            # W channel - master drives
            w_master = GAXIMaster(
                dut=dut,
                title=f"W_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_w_field_config(
                    self.data_width, 1
                ),
                pkt_prefix="w",
                multi_sig=True,
                log=log
            )
            self.w_masters.append(w_master)

            # B channel - master receives responses
            b_slave = GAXISlave(
                dut=dut,
                title=f"B_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_b_field_config(
                    self.id_width, 1
                ),
                pkt_prefix="b",
                multi_sig=True,
                log=log
            )
            self.b_slaves.append(b_slave)

            # AR channel - master drives
            ar_master = GAXIMaster(
                dut=dut,
                title=f"AR_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_ar_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="ar",
                multi_sig=True,
                log=log
            )
            self.ar_masters.append(ar_master)

            # R channel - master receives responses
            r_slave = GAXISlave(
                dut=dut,
                title=f"R_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_r_field_config(
                    self.id_width, self.data_width, 1
                ),
                pkt_prefix="r",
                multi_sig=True,
                log=log
            )
            self.r_slaves.append(r_slave)

        # Slave-side receivers (receive AW, W on slaves, send B, R back)
        self.aw_slaves = []
        self.w_slaves = []
        self.b_masters = []  # Send B responses
        self.ar_slaves = []
        self.r_masters = []  # Send R responses

        for s in range(self.num_slaves):
            # AW channel - slave receives
            aw_slave = GAXISlave(
                dut=dut,
                title=f"AW_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_aw_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="aw",
                multi_sig=True,
                log=log
            )
            # Add callback to generate B response
            aw_slave.add_callback(self._create_b_responder(s))
            self.aw_slaves.append(aw_slave)

            # W channel - slave receives
            w_slave = GAXISlave(
                dut=dut,
                title=f"W_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_w_field_config(
                    self.data_width, 1
                ),
                pkt_prefix="w",
                multi_sig=True,
                log=log
            )
            self.w_slaves.append(w_slave)

            # B channel - slave sends responses
            b_master = GAXIMaster(
                dut=dut,
                title=f"B_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_b_field_config(
                    self.id_width, 1
                ),
                pkt_prefix="b",
                multi_sig=True,
                log=log
            )
            self.b_masters.append(b_master)

            # AR channel - slave receives
            ar_slave = GAXISlave(
                dut=dut,
                title=f"AR_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_ar_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="ar",
                multi_sig=True,
                log=log
            )
            # Add callback to generate R response
            ar_slave.add_callback(self._create_r_responder(s))
            self.ar_slaves.append(ar_slave)

            # R channel - slave sends responses
            r_master = GAXIMaster(
                dut=dut,
                title=f"R_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clock,
                field_config=AXI4FieldConfigHelper.create_r_field_config(
                    self.id_width, self.data_width, 1
                ),
                pkt_prefix="r",
                multi_sig=True,
                log=log
            )
            self.r_masters.append(r_master)

    def _create_b_responder(self, slave_idx):
        """Create callback to send B response when AW received"""
        def b_responder(aw_pkt):
            # Schedule B response
            cocotb.start_soon(self._send_b_response(slave_idx, aw_pkt))
        return b_responder

    async def _send_b_response(self, slave_idx, aw_pkt):
        """Send B response for received AW"""
        await RisingEdge(self.clock)
        b_pkt = self.b_masters[slave_idx].create_packet(
            id=aw_pkt.id,
            resp=0
        )
        await self.b_masters[slave_idx].send(b_pkt)

    def _create_r_responder(self, slave_idx):
        """Create callback to send R response when AR received"""
        def r_responder(ar_pkt):
            # Schedule R response
            cocotb.start_soon(self._send_r_response(slave_idx, ar_pkt))
        return r_responder

    async def _send_r_response(self, slave_idx, ar_pkt):
        """Send R response for received AR"""
        await RisingEdge(self.clock)
        burst_len = ar_pkt.len + 1
        for i in range(burst_len):
            # Echo address as data for easy verification
            data = ar_pkt.addr + (i * 4)
            r_pkt = self.r_masters[slave_idx].create_packet(
                id=ar_pkt.id,
                data=data,
                resp=0,
                last=1 if i == burst_len - 1 else 0
            )
            await self.r_masters[slave_idx].send(r_pkt)

    async def reset(self):
        """Perform bridge reset"""
        self.dut.aresetn.value = 0
        await Timer(100, units="ns")
        self.dut.aresetn.value = 1
        await RisingEdge(self.clock)
        self.log.info("Bridge reset complete")

    def get_slave_index(self, address):
        """Determine which slave based on address"""
        for s in range(self.num_slaves):
            if self.slave_base_addrs[s] <= address < (self.slave_base_addrs[s] + self.slave_addr_range):
                return s
        return 0

    async def write_transaction(self, master_idx, address, data, txn_id=0):
        """Send write transaction (AW + W)"""
        # Send AW
        aw_pkt = self.aw_masters[master_idx].create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await self.aw_masters[master_idx].send(aw_pkt)

        # Send W
        w_pkt = self.w_masters[master_idx].create_packet(
            data=data,
            last=1,
            strb=0xF
        )
        await self.w_masters[master_idx].send(w_pkt)

        return aw_pkt, w_pkt

    async def read_transaction(self, master_idx, address, txn_id=0):
        """Send read transaction (AR)"""
        ar_pkt = self.ar_masters[master_idx].create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await self.ar_masters[master_idx].send(ar_pkt)
        return ar_pkt


@cocotb.test(timeout_time=100, timeout_unit='us')
async def bridge_2x2_test(dut):
    """Comprehensive test for 2x2 AXI4 Bridge - Queue-based verification"""

    log = dut._log
    log.info("=" * 80)
    log.info("Starting 2x2 AXI4 Bridge Crossbar Test")
    log.info("=" * 80)

    # Start clock
    clock = Clock(dut.aclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Create testbench
    tb = Bridge2x2TB(dut, log)

    # Reset
    await tb.reset()
    await Timer(100, units="ns")

    # TEST 1: Basic write to each slave
    log.info("TEST 1: Basic Writes")
    await tb.write_transaction(master_idx=0, address=0x00001000, data=0xDEADBEEF, txn_id=1)
    await Timer(50, units="ns")
    await tb.write_transaction(master_idx=0, address=0x10001000, data=0xCAFEBABE, txn_id=2)
    await Timer(200, units="ns")

    # Verify AW arrived at correct slaves
    assert len(tb.aw_slaves[0]._recvQ) > 0, "Slave 0 should have received AW"
    assert len(tb.aw_slaves[1]._recvQ) > 0, "Slave 1 should have received AW"

    aw0 = tb.aw_slaves[0]._recvQ[0]
    aw1 = tb.aw_slaves[1]._recvQ[0]
    assert aw0.addr == 0x00001000, f"Slave 0 AW address mismatch"
    assert aw1.addr == 0x10001000, f"Slave 1 AW address mismatch"

    # Verify W data arrived
    assert len(tb.w_slaves[0]._recvQ) > 0, "Slave 0 should have received W"
    assert len(tb.w_slaves[1]._recvQ) > 0, "Slave 1 should have received W"

    w0 = tb.w_slaves[0]._recvQ[0]
    w1 = tb.w_slaves[1]._recvQ[0]
    assert w0.data == 0xDEADBEEF, f"Slave 0 W data mismatch"
    assert w1.data == 0xCAFEBABE, f"Slave 1 W data mismatch"

    # Verify B responses received by master
    assert len(tb.b_slaves[0]._recvQ) >= 2, f"Master 0 should have received 2 B responses, got {len(tb.b_slaves[0]._recvQ)}"

    log.info("✓ TEST 1 PASSED")
    await Timer(100, units="ns")

    # TEST 2: Basic reads
    log.info("TEST 2: Basic Reads")
    await tb.read_transaction(master_idx=0, address=0x00002000, txn_id=3)
    await tb.read_transaction(master_idx=0, address=0x10002000, txn_id=4)
    await Timer(200, units="ns")

    # Verify AR arrived
    assert len(tb.ar_slaves[0]._recvQ) > 0, "Slave 0 should have received AR"
    assert len(tb.ar_slaves[1]._recvQ) > 0, "Slave 1 should have received AR"

    # Verify R responses received
    assert len(tb.r_slaves[0]._recvQ) >= 2, f"Master 0 should have received 2 R responses"

    r0 = tb.r_slaves[0]._recvQ[0]
    r1 = tb.r_slaves[0]._recvQ[1]
    assert r0.data == 0x00002000, f"R data mismatch for slave 0"
    assert r1.data == 0x10002000, f"R data mismatch for slave 1"

    log.info("✓ TEST 2 PASSED")
    await Timer(100, units="ns")

    log.info("=" * 80)
    log.info("2x2 AXI4 Bridge Test PASSED")
    log.info("=" * 80)


# =============================================================================
# Pytest Wrapper
# =============================================================================

@pytest.mark.parametrize("num_masters,num_slaves,data_width,addr_width,id_width", [
    (2, 2, 32, 32, 4),
])
def test_bridge_axi4_2x2(request, num_masters, num_slaves, data_width, addr_width, id_width):
    """Pytest wrapper for 2x2 Bridge test"""

    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))

    verilog_sources = [
        os.path.join(repo_root, 'projects', 'components', 'bridge', 'rtl', 'bridge_axi4_flat_2x2.sv'),
    ]

    parameters = {
        'NUM_MASTERS': num_masters,
        'NUM_SLAVES': num_slaves,
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
        'ID_WIDTH': id_width,
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
        "-Wno-WIDTHEXPAND",
        "-Wno-UNUSEDSIGNAL",
        "-Wno-UNSIGNED",
        "-Wno-BLKSEQ",
    ]

    module = os.path.splitext(os.path.basename(__file__))[0]
    sim_build = os.path.join(repo_root, 'projects', 'components', 'bridge', 'dv',
                             'local_sim_build',
                             f'test_bridge_axi4_{num_masters}x{num_slaves}_'
                             f'dw{data_width:03d}_aw{addr_width:03d}_id{id_width:02d}')

    run(
        verilog_sources=verilog_sources,
        toplevel="bridge_axi4_flat_2x2",
        module=module,
        parameters=parameters,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
