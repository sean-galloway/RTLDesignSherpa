# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Testbench for `andesite_training_layer` (TASK-016 t4).

The layer owns the three training FUBs, the DFI training pin mux, the
maintenance-class command channel into the scheduler, and the clock-domain
crossing to the DFI PHY. This TB instantiates the layer as top, drives the
controller-domain training enables/CSRs, mocks the PHY handshakes, and
auto-acks the command channel one cycle after each registered request.

Sampling rule (carried from andesite_dfi_cmd_path_tb): registered outputs are
read at the accept edge plus Timer(1,'ps').
"""

import os
import subprocess
import sys

import cocotb
from cocotb.triggers import RisingEdge, Timer

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from TBClasses.shared.tbbase import TBBase    # noqa: E402

OP_MRS = 0xA
OP_MPC = 0x10

WL_OFF, WL_DQSEN, WL_MRD, WL_READY, WL_WAIT_WLO, WL_TIMEOUT = range(6)


class AndesiteTrainingLayerTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_CS = int(os.environ.get('NUM_CS', '1'))
        self.CSW = max(1, (self.NUM_CS - 1).bit_length())
        self.cmd_log = []      # (op, bank, addr) at each ack
        self.dfi_events = []   # sampled DFI pin events for debug
        self.cmd_ack_enable = True

    async def setup(self):
        await self.start_clock('mc_clk', freq=10, units='ns')
        await self.start_clock('dfi_clk', freq=10, units='ns')
        self._drive_idle()
        self.dut.mc_rst_n.value = 0
        self.dut.dfi_rstn.value = 0
        await self.wait_clocks('mc_clk', 6)
        await self.wait_clocks('dfi_clk', 6)
        self.dut.mc_rst_n.value = 1
        self.dut.dfi_rstn.value = 1
        await self.wait_clocks('mc_clk', 4)
        cocotb.start_soon(self._cmd_ack_model())

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0
        self.dut.dfi_rstn.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1
        self.dut.dfi_rstn.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    def _drive_idle(self):
        d = self.dut
        # wrlvl CSR side
        d.wrlvl_en_i.value = 0
        d.wrlvl_strobe_i.value = 0
        d.wrlvl_cs_sel_i.value = 0
        d.t_wldqsen_i.value = 4
        d.t_wlmrd_i.value = 4
        d.t_wlmrd_max_i.value = 0
        d.t_wlo_i.value = 4
        d.t_wloe_i.value = 4
        # rdlvl CSR side
        d.rdlvl_en_i.value = 0
        d.rdlvl_cs_sel_i.value = 0
        d.csr_mr3_mpr_enter_i.value = 0x3101
        d.csr_mr3_mpr_exit_i.value = 0x3001
        d.t_mpr_enter_i.value = 4
        d.t_mpr_exit_i.value = 4
        d.t_mpr_readout_i.value = 4
        d.tmod_i.value = 2
        d.t_rdlvl_timeout_i.value = 0
        # ca/wdq CSR side
        d.ca_train_en_i.value = 0
        d.wdq_cal_en_i.value = 0
        d.chan_sel_i.value = 0
        d.csr_mpc_ca_enter_i.value = 0x09
        d.csr_mpc_ca_exit_i.value = 0x19
        d.csr_mpc_wdq_enter_i.value = 0x0A
        d.csr_mpc_wdq_exit_i.value = 0x1A
        d.t_ca_train_i.value = 4
        d.t_wdq_cal_i.value = 3
        d.t_ca_timeout_i.value = 0
        # PHY observations (controller-domain samples)
        d.mpr_pattern_i.value = 0
        d.ca_sample_i.value = 0
        d.wdq_sample_i.value = 0
        d.wrlvl_prime_dq_i.value = 0
        # DFI inputs idle de-asserted (active-low = high)
        d.dfi_phylvl_ack_cs_n_i.value = (1 << self.NUM_CS) - 1
        d.dfi_phylvl_req_cs_n_i.value = (1 << self.NUM_CS) - 1
        # command channel (ack is driven by _cmd_ack_model)
        d.trn_cmd_ack_i.value = 0

    async def _cmd_ack_model(self):
        """Auto-ack the command channel one cycle after a registered request."""
        while True:
            await RisingEdge(self.dut.mc_clk)
            d = self.dut
            d.trn_cmd_ack_i.value = 0
            if self.cmd_ack_enable and int(d.trn_cmd_req_o.value):
                op = int(d.trn_cmd_op_o.value)
                bank = int(d.trn_cmd_bank_o.value)
                addr = int(d.trn_cmd_addr_o.value)
                self.cmd_log.append((op, bank, addr))
                await RisingEdge(d.mc_clk)
                d.trn_cmd_ack_i.value = 1
                await RisingEdge(d.mc_clk)
                d.trn_cmd_ack_i.value = 0

    async def pulse(self, sig_name, cycles=1):
        sig = getattr(self.dut, sig_name)
        sig.value = 1
        for _ in range(cycles):
            await RisingEdge(self.dut.mc_clk)
        sig.value = 0

    async def wait_rdlvl_done(self, limit=400):
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, 'ps')
            if int(self.dut.rdlvl_result_valid_o.value):
                return True
        return False

    async def wait_ca_done(self, limit=400):
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, 'ps')
            if int(self.dut.ca_train_result_valid_o.value):
                return True
        return False

    async def wait_wrlvl_ready(self, limit=200):
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, 'ps')
            if int(self.dut.wrlvl_state_o.value) == WL_READY:
                return True
        return False

    async def pulse_wrlvl_strobe(self):
        self.dut.wrlvl_strobe_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, 'ps')
        self.dut.wrlvl_strobe_i.value = 0

    async def issue_rdlvl(self, cs=0, pattern=1, timeout=False):
        """Pulse rdlvl_en_i and mock the PHY handshake. Returns success."""
        d = self.dut
        d.rdlvl_cs_sel_i.value = cs
        d.mpr_pattern_i.value = pattern
        await self.pulse('rdlvl_en_i')
        # Wait for cmd_req (MRS enter), auto-acked by _cmd_ack_model.
        for _ in range(300):
            await RisingEdge(d.mc_clk)
            await Timer(1, 'ps')
            # When rdlvl drives ack to PHY, PHY grants by dropping req.
            if int(d.dfi_phylvl_ack_cs_n_o.value) == ((1 << self.NUM_CS) - 1) & ~(1 << cs):
                if not timeout:
                    d.dfi_phylvl_req_cs_n_i.value = ((1 << self.NUM_CS) - 1) & ~(1 << cs)
                    await RisingEdge(d.mc_clk)
                    await Timer(1, 'ps')
                    d.dfi_phylvl_req_cs_n_i.value = (1 << self.NUM_CS) - 1
            if int(d.rdlvl_result_valid_o.value):
                return True
        return False

    async def issue_ca(self, flow='ca', chan=0, sample=1, timeout=False):
        """Pulse ca_train_en_i / wdq_cal_en_i. Returns success."""
        d = self.dut
        d.chan_sel_i.value = chan
        if flow == 'ca':
            await self.pulse('ca_train_en_i')
        else:
            await self.pulse('wdq_cal_en_i')
        presented = False
        for _ in range(300):
            await RisingEdge(d.mc_clk)
            await Timer(1, 'ps')
            # SAMPLE state is encoded 2 in ca_train_ifc.
            if (int(d.ca_train_state_o.value) == 2) and not presented and not timeout:
                if flow == 'ca':
                    d.ca_sample_i.value = sample
                else:
                    d.wdq_sample_i.value = sample
                presented = True
            if int(d.ca_train_result_valid_o.value):
                return True
        return False

    def sample_dfi(self):
        d = self.dut
        return {
            'req': int(d.dfi_phylvl_req_cs_n_o.value),
            'ack': int(d.dfi_phylvl_ack_cs_n_o.value),
            'wrlvl_cs': int(d.dfi_phy_wrlvl_cs_n_o.value),
            'rdlvl_cs': int(d.dfi_phy_rdlvl_cs_n_o.value),
            'strobe': int(d.dfi_wrlvl_strobe_o.value),
        }
