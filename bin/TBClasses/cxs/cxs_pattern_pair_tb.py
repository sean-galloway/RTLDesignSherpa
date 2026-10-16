# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: CxsPatternPairTB
# Purpose: Testbench for cxs_master_injector -> cxs_slave_pattern_check
# Subsystem: framework
#
# The scenarios and the CRC / beat-count / schedule scoreboard are
# Axis4PatternPairTB's, unchanged: tb_cxs_pattern_pair has the same control
# and observation ports as tb_axis4_pattern_pair. This class adds what a CXS
# link needs on top ([[tb-structure]]).

from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time

from CocoTBFramework.components.cxs import CXSConfig, create_cxs_monitor

from TBClasses.amba.axis4_pattern_pair_tb import Axis4PatternPairTB

AXIS_ID_WIDTH, AXIS_DEST_WIDTH, AXIS_USER_WIDTH = 8, 4, 1
LINK_RUN = 0b11


class CxsPatternPairTB(Axis4PatternPairTB):
    """CXS pattern pair: the AXIS pair's scoreboard plus the link.

    * A CXSMonitor on the link between the two (the harness's cxs_* wires)
      checks the credit model, the activation handshake and CXSCNTL
      placement on every cycle; any violation fails the test.
    * Both endpoints' sticky protocol_error and the receiver's sticky
      unsupported must stay low through every scenario.
    * The link must actually reach RUN (CXSACTIVEREQ and CXSACTIVEACK both
      high). A pair that moved no flits would also show no violations.
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.cxs_mon = None
        self._run_seen = False
        self._link_task = None

    def cxs_config(self):
        sw = self.DW // 8
        carry_tuser = sw + AXIS_USER_WIDTH <= 128
        return CXSConfig(issue='D', data_width=self.DW, max_pkt_per_flit=2, start_align=16,
                         srcid_width=AXIS_ID_WIDTH, tgtid_width=AXIS_DEST_WIDTH,
                         user_width=sw + (AXIS_USER_WIDTH if carry_tuser else 0),
                         max_credit=15, link_control=True, check=False).validate()

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        self.cxs_mon = create_cxs_monitor(self.dut, 'CXS Mon (pair link)', 'cxs_',
                                          self.dut.clk, self.cxs_config(),
                                          reset=self.dut.rst_n, log=self.log)

    async def _watch_link(self):
        while True:
            await RisingEdge(self.dut.clk)
            if int(self.dut.tx_link_state.value) == LINK_RUN:
                self._run_seen = True

    async def run_stream(self, **kw):
        if self._link_task is None:
            import cocotb
            self._link_task = cocotb.start_soon(self._watch_link())
        await super().run_stream(**kw)

    def check_results(self, *, label, **kw):
        super().check_results(label=label, **kw)
        flags = {name: int(getattr(self.dut, name).value)
                 for name in ('tx_protocol_error', 'rx_protocol_error', 'rx_unsupported')}
        for name, v in flags.items():
            if v:
                self.log.error(f"@ {get_sim_time('ns')}ns: [{label}] {name} set")
                self.errors += 1

    async def run_all(self):
        await super().run_all()     # asserts the CRC / schedule scoreboard
        problems = []
        if self.cxs_mon.total_violations():
            problems.append(f"CXS wire monitor violations: {self.cxs_mon.violations}")
        if not self._run_seen:
            problems.append("the CXS link never reached RUN")
        assert not problems, "; ".join(problems)
        self.log.info(f"@ {get_sim_time('ns')}ns: cxs pattern pair: link clean, "
                      f"{self.cxs_mon.stats if hasattr(self.cxs_mon, 'stats') else ''}")
