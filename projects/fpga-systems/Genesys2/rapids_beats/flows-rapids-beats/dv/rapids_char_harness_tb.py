# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_char_harness_tb
# Purpose: Drive rapids_char_harness over a simulated UART using the BOARD's own
#          host program, so sim and board are the same code, not two copies.
#
# Rewritten 2026-09-23. rapids_char_harness now owns the whole host path (UART ->
# AXIL -> region decode -> harness CSRs -> kick sequencer -> DUT), mirroring
# stream_genesys2_top -> stream_harness. Before that move the kick sequencer sat
# in rapids_char_top, ABOVE the sim toplevel, so verify-sim was structurally
# incapable of exercising the board's launch mechanism -- green gate, dead board.
# That was RAPIDS TASK-081.
#
# Consequences for this TB, and why it shrank from 738 lines to ~200:
#   * The 55 cfg_*/obs_*/gen_*/s_apb_* ports it used to poke are INTERNAL now.
#     There is nothing to poke; everything goes through CSRs over the UART.
#   * Which means the board's RapidsCharCampaign already does all of it --
#     configure, descriptor load, kick, golden-CRC scoreboard, bus meters. So
#     this TB reuses that class verbatim instead of maintaining a second
#     implementation that has to be kept in agreement with it. The old TB and
#     the host program had already drifted apart once; that is what TASK-081 was.
#
# Transport: RapidsCharIO's methods are SYNCHRONOUS (they block on byte I/O), so
# they must never be called bare from a coroutine -- they run on a worker thread
# via cocotb.external, which lets them block while the simulator advances. Whole
# sequences are wrapped per call, not individual registers: each external is a
# thread handoff, and the ddr2_char framework established the coarse-grained
# pattern.
#
# Subsystem: rapids_char_harness
# Author: sean galloway
# Created: 2026-07-03
# Rewritten: 2026-09-23 (UART transport; host-program reuse)

import os
import sys
import time

import cocotb

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase
from TBClasses.harness.harness import UartSimHarness

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

_HOST_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'host')
sys.path.insert(0, os.path.abspath(_HOST_DIR))

from rapids_char_io import RapidsCharIO, CSR_ID_EXPECTED  # noqa: E402
from run_characterization import RapidsCharCampaign       # noqa: E402

# Host-side timeout for the campaign's poll loops. This is WALL seconds, not sim
# time: each predicate() is a UART read that advances sim, so the loop is paced
# by the simulator rather than by the clock on the wall.
SIM_POLL_TIMEOUT_S = float(os.environ.get('TEST_POLL_TIMEOUT_S', '120'))


def _sim_poll(predicate, timeout_s: float, period_s: float = 0.0) -> bool:
    """Replacement for RapidsCharCampaign._poll under simulation.

    The board version sleeps 20 ms between polls. On a cocotb worker thread a
    bare sleep burns wall-clock and advances NO simulation time -- only the UART
    read inside predicate() advances sim -- so the sleep is pure waste and would
    make the sim take minutes to observe a transfer that completes in
    microseconds of sim time. Dropping the period leaves the read itself as the
    pacing mechanism.
    """
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        if predicate():
            return True
    return predicate()


class RapidsCharHarnessTB(TBBase):
    """Thin shim: UART bringup + the board's campaign, nothing of its own."""

    def __init__(self, dut):
        super().__init__(dut)

        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.NUM_ACTIVE   = self.convert_to_int(os.environ.get('TEST_NUM_ACTIVE', '4'))
        self.NUM_BEATS    = self.convert_to_int(os.environ.get('TEST_NUM_BEATS', '8'))
        self.CLK_PERIOD   = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        # MEASURED floor is 4 (ddr2_char: 3 and 2 fail -- uart_rx samples at
        # (CLKS_PER_BIT-1)/2). Passed to the RTL as UART_BAUD = FPGA_CLK_HZ /
        # CLKS_PER_BIT so the RTL divisor and this constant cannot drift apart.
        self.CLKS_PER_BIT = self.convert_to_int(os.environ.get('TEST_CLKS_PER_BIT', '4'))

        # The harness ports are stream-shaped, which is exactly what
        # UartSimHarness defaults to (aclk/aresetn/i_uart_rx/o_uart_tx).
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.h = None
        self.io = None
        self.campaign = None

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        self.h = UartSimHarness(self.dut, clk=self.clk_name,
                                clk_period_ns=self.CLK_PERIOD,
                                resetn='aresetn',
                                clks_per_bit=self.CLKS_PER_BIT)
        await self.h.start()          # clock + reset + traced byte channel

        self.io = RapidsCharIO(bridge=self.h.make_bridge())
        self.campaign = RapidsCharCampaign(self.io, self.NUM_CHANNELS)
        self.campaign._poll = _sim_poll

        # Prove the link before trusting anything downstream. A wrong baud or a
        # dead UART otherwise shows up much later as "the DMA moved no beats",
        # which is a far more expensive thing to debug than a bad ID read.
        ident = await cocotb.external(lambda: self.io.csr_read(0x000))()
        assert ident == CSR_ID_EXPECTED, (
            f"harness CSR ID read 0x{ident if ident is not None else 0:08X}, "
            f"expected 0x{CSR_ID_EXPECTED:08X} -- UART link is not up "
            f"(CLKS_PER_BIT={self.CLKS_PER_BIT})")
        self.log.info(f"UART link OK: rapids_char_harness ID = 0x{ident:08X}")

        await cocotb.external(self.campaign.configure)()

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # =========================================================================
    # SELF-CHECKS -- the board's own campaign, run on a worker thread
    # =========================================================================

    # =========================================================================
    # EVIDENCE
    # =========================================================================

    def _log_detail(self, label: str, ok: bool, detail: dict) -> None:
        """Mirror the campaign's findings into the COCOTB log.

        RapidsCharCampaign reports through logging.getLogger('rapids_char') and
        print(), both of which pytest captures and then DISCARDS on a pass. So
        after this TB moved onto the campaign, a green run stopped leaving any
        record of what it actually moved -- no CRCs, no beat counts, no meters.
        A pass you cannot inspect is trusted, not checked, which is the failure
        this repo keeps relearning. Re-emit the essentials where they survive.
        """
        self.log.info(f"{label}: {'PASS' if ok else 'FAIL'} "
                      f"beats={detail.get('beat_total')} "
                      f"golden_mismatch={detail.get('golden_mismatch')}")
        for ch, vals in (detail.get('results') or {}).items():
            # CRCs in hex: every other CRC in this flow (golden table, board
            # campaign output, RTL comments) is hex, and a lone decimal one is
            # a quiet trap when comparing a failing run against them.
            # The campaign emits a DICT here ({'golden','rd','chk'} on SOURCE,
            # {'golden','wr','gen'} on SINK) -- the old TB's (exp, act) tuple
            # shape does not occur, so handle the mapping first.
            if isinstance(vals, dict):
                shown = ' '.join(f"{k}=0x{v:08X}" if isinstance(v, int) else f"{k}={v}"
                                 for k, v in vals.items())
            elif isinstance(vals, (tuple, list)):
                shown = ' '.join(f"0x{v:08X}" if isinstance(v, int) else str(v)
                                 for v in vals)
            else:
                shown = vals
            self.log.info(f"  {label} ch{ch}: {shown}")
        # perf is {'ifaces': {key: rec}} or None (None when no interface was
        # engaged). The raw cycle buckets live in rec['buckets'], NOT in rec --
        # iterating perf directly yields one ('ifaces', {...}) pair and logs
        # prod=None for everything, which reads as "the meters counted nothing"
        # and is worse than logging nothing at all.
        for iface, rec in ((detail.get('perf') or {}).get('ifaces') or {}).items():
            b = rec.get('buckets') or {}
            extra = ''
            if 'bytes' in rec:      # AXIS interfaces carry exact byte/packet counts
                extra = (f" bytes={rec['bytes']} pkts={rec['packets']}"
                         f" byte_bw={rec.get('byte_bw_gb_s'):.2f}GB/s")
            util = rec.get('util'); eff = rec.get('eff_bw_gb_s')
            self.log.info(f"  {label} {iface} meter: prod={b.get('prod')} "
                          f"bp={b.get('bp')} starv={b.get('starv')} "
                          f"idle={b.get('idle')} "
                          f"util={util:.1%}" if isinstance(util, float) else
                          f"  {label} {iface} meter: prod={b.get('prod')} util={util}")
            self.log.info(f"  {label} {iface} eff={eff:.2f}GB/s{extra}"
                          if isinstance(eff, float) else
                          f"  {label} {iface} eff={eff}{extra}")
        for w in (detail.get('warnings') or []):
            self.log.warning(f"  {label}: {w}")
        for e in (detail.get('errors') or []):
            self.log.error(f"  {label} SCOREBOARD: {e}")

    async def run_sink_selfcheck(self, active_channels, beats):
        active = list(active_channels)

        def prog():
            # Stale scheduler/descriptor state wedges a second run (board-
            # confirmed: baseline 1/4, with reset 5/5), so reset first.
            self.campaign.reset_channels()
            return self.campaign.run_sink_selfcheck(active, beats,
                                                    SIM_POLL_TIMEOUT_S)
        ok, detail = await cocotb.external(prog)()
        self._log_detail('SINK', ok, detail)
        return ok, detail

    async def run_source_selfcheck(self, active_channels, beats,
                                   backpressure: bool = False):
        active = list(active_channels)

        def prog():
            self.campaign.reset_channels()
            return self.campaign.run_source_selfcheck(active, beats,
                                                      SIM_POLL_TIMEOUT_S,
                                                      backpressure=backpressure)
        ok, detail = await cocotb.external(prog)()
        self._log_detail('SOURCE', ok, detail)
        return ok, detail
