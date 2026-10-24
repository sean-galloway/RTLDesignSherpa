# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_g_seq_ports
# Purpose: the inputs a rapids-g gatling sequencer has beyond the product
#          scheduler's, driven by the TB at every level that exposes them:
#          seq_restart, the register mailbox's response side (seq_reg_*) and
#          the firmware load (fw_*, rapids TASK-038).
#
# Author: sean galloway
# Created: 2026-10-23

"""Drive rapids_seq_g's own inputs from a testbench.

Levels below the top base have no register block for the mailbox to reach
and no FW_* registers, so these ports are TB inputs there. `drive_idle` puts
every one at its quiescent value before reset (no restart, no load hold,
no mailbox response); `MailboxGuard` stands in for the register block: it
answers any mailbox command with an error response and then fails the
running test (its task raises) -- the
scheduler image never uses the mailbox, so a command here is a firmware
defect, not something to absorb silently.

Signal names are `<prefix>seq_restart`, `<prefix><reg>cmd_*` /
`<prefix><reg>rsp_*` and `<prefix>fw_*`; the two benches name them

    rapids_g_equiv_tb_top    prefix 'g_', reg 'reg_'      (g_reg_cmd_valid ...)
    scheduler_group_array_g  prefix '',   reg 'seq_reg_'  (seq_reg_cmd_valid ...)
"""

import cocotb
from cocotb.triggers import RisingEdge


def drive_idle(dut, prefix: str, reg: str) -> None:
    """Every sequencer input at its quiescent value."""
    def put(name, v):
        getattr(dut, prefix + name).value = v
    put('seq_restart', 0)
    put(f'{reg}cmd_ready', 0)
    put(f'{reg}rsp_valid', 0)
    put(f'{reg}rsp_prdata', 0)
    put(f'{reg}rsp_pslverr', 0)
    for name in ('fw_hold', 'fw_wr_en', 'fw_addr', 'fw_wr_data', 'fw_alg_max'):
        put(name, 0)


class MailboxGuard:
    """Answers the register mailbox with PSLVERR (there is no register block
    at this level) and records every command, one outstanding at a time as
    the real path is (rapids_g_reg_arb)."""

    def __init__(self, dut, clk, prefix: str, reg: str, log):
        self.dut, self.clk, self.log = dut, clk, log
        self.p = prefix + reg
        self.commands = []

    def _sig(self, name):
        return getattr(self.dut, self.p + name)

    def start(self):
        cocotb.start_soon(self._run())

    async def _run(self):
        self._sig('cmd_ready').value = 1
        while True:
            await RisingEdge(self.clk)
            if int(self._sig('cmd_valid').value) and int(self._sig('cmd_ready').value):
                cmd = {'write': int(self._sig('cmd_pwrite').value),
                       'paddr': int(self._sig('cmd_paddr').value),
                       'pwdata': int(self._sig('cmd_pwdata').value)}
                self.commands.append(cmd)
                self.log.error(f"register mailbox command with no register block at this level: {cmd}")
                self._sig('cmd_ready').value = 0
                self._sig('rsp_valid').value = 1
                self._sig('rsp_pslverr').value = 1
                while True:
                    await RisingEdge(self.clk)
                    if int(self._sig('rsp_ready').value):
                        break
                self._sig('rsp_valid').value = 0
                self._sig('rsp_pslverr').value = 0
                self._sig('cmd_ready').value = 1
                self.check()        # raising in this task fails the running test

    def check(self):
        assert not self.commands, f"the firmware posted {len(self.commands)} register-mailbox " \
                                  f"command(s) (first {self.commands[0]}); the scheduler image uses none"
