# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_tb_common
# Purpose: Shared pieces of the chi_rnf_port / chi_hnf_port testbenches
#
# Documentation: docs/markdown/rtl-amba/chi/README.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-29
"""Shared CHI link-layer testbench parts.

The DUT's property set travels from the pytest runner as environment
variables named exactly like the RTL parameters (``NODEID_WIDTH``,
``DATA_WIDTH``, ``LINK_CTRL`` ...); :func:`cfg_from_env` rebuilds the
framework :class:`CHIConfig` from them, so the BFMs bind exactly the flit
widths the DUT was built with.

Both DUTs are the LINK LAYER only. The link side is driven by the RDS-DV CHI
BFMs (a home for the RN-F port, a requester for the HN-F port) and watched by
a CHI monitor. The FUB side of each channel is a valid/ready flit port, driven
(TX channels) and drained (RX channels) by the framework GAXI BFMs through
:class:`FubTx` / :class:`FubRx`, never by poking the pins. What the Protocol
layer above the link would do (issue requests, answer with data, answer a
snoop) is done at flit level by the testbench subclasses, with the DV
transaction models (``RequesterTracker`` / ``CompleterTracker``) deciding what
each flit owes.

Verdicts carry counts: every claim a phase makes is a count in
:attr:`CHITBBase.counts`, and a required count of zero fails the run, so a
phase that silently did nothing cannot pass.
"""

import os
import random
from collections import Counter, deque

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge

from CocoTBFramework.components.chi import CHIConfig
from CocoTBFramework.components.chi.chi_flits import LAYOUTS
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.shared.tbbase import TBBase

# CHIConfig.rtl_parameters() names, then the RTL-only parameters
CFG_PARAM_NAMES = ('NODEID_WIDTH', 'ADDR_WIDTH', 'DATA_WIDTH', 'REQ_RSVDC_WIDTH', 'DAT_RSVDC_WIDTH',
                   'MPAM_WIDTH', 'PBHA_WIDTH', 'MECID_WIDTH', 'STREAMID_WIDTH', 'SECSID1_WIDTH',
                   'DATA_CHECK', 'POISON', 'MAX_LCREDIT')
RTL_ONLY_NAMES = ('LINK_CTRL', 'SKID_DEPTH', 'RX_FIFO_DEPTH', 'LINKACTIVE_SYNC_STAGES')
PARAM_NAMES = CFG_PARAM_NAMES + RTL_ONLY_NAMES

RN_ID = 1       # the RN node id the TB uses
HN_ID = 0       # the home node id

# link_state encoding of the DUT status pins {REQ, ACK}
ST_STOP, ST_DEACT, ST_ACT, ST_RUN = 0, 1, 2, 3

# Link-side timing profiles for the BFM that plays the partner. They set the
# randomizer keys CHIPort reads: how fast it grants credits (lcrd_gap), how
# long its receive buffer holds a flit (drain_gap, a slow consumer), how long
# it sits on LINKACTIVEREQ (ack_delay) and its own TX flit spacing.
LINK_PROFILES = {
    'fast':   {'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
               'drain_gap': ([(0, 0)], [1]), 'ack_delay': ([(0, 0)], [1])},
    # sparse LCRDV, slow ACK, uneven flit spacing
    'gappy':  {'flit_gap': ([(0, 0), (1, 3)], [3, 1]), 'lcrd_gap': ([(0, 0), (2, 6)], [2, 1]),
               'drain_gap': ([(0, 0), (1, 2)], [3, 1]), 'ack_delay': ([(1, 6)], [1])},
    # slow drain: with a small rx_buffer_depth the credit pool empties, so the
    # transmitter must stall with flits queued -- the credit gate's only real test
    'starve': {'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
               'drain_gap': ([(4, 12)], [1]), 'ack_delay': ([(0, 2)], [1])},
}


def env_params():
    return {n: int(os.environ[n]) for n in PARAM_NAMES if n in os.environ}


def cfg_from_env(node_type):
    """The framework config for ``node_type`` built from the DUT's parameters."""
    p = env_params()
    return CHIConfig(
        node_type=node_type,
        nodeid_width=p.get('NODEID_WIDTH', 7), addr_width=p.get('ADDR_WIDTH', 44),
        data_width=p.get('DATA_WIDTH', 128), req_rsvdc_width=p.get('REQ_RSVDC_WIDTH', 0),
        dat_rsvdc_width=p.get('DAT_RSVDC_WIDTH', 0), mpam_width=p.get('MPAM_WIDTH', 0),
        pbha_width=p.get('PBHA_WIDTH', 0), mecid_width=p.get('MECID_WIDTH', 0),
        streamid_width=p.get('STREAMID_WIDTH', 0), secsid1_width=p.get('SECSID1_WIDTH', 0),
        data_check=bool(p.get('DATA_CHECK', 0)), poison=bool(p.get('POISON', 0)),
        max_lcredit=p.get('MAX_LCREDIT', 15), link_control=bool(p.get('LINK_CTRL', 1)),
    ).validate()


def flit_field_config(width):
    """A FUB flit port is one field, the whole flit word."""
    fc = FieldConfig()
    fc.add_field(FieldDefinition(name='flit', bits=width, default=0, format='hex',
                                 display_width=(width + 3) // 4))
    return fc


def optional_bits(cfg, channel, names):
    """{field: bits} of the optional sideband fields this config's flit carries."""
    return {n: b for n, b in LAYOUTS[channel](cfg) if n in names and b > 0}


class FubTx:
    """A TX-channel FUB port: a queue pumped into a framework GAXI master.

    The Protocol layer (the testbench) calls :meth:`put` with flit words; the
    pump hands every queued word to the GAXI master as one burst, so the
    master's valid/ready behaviour, not this class, decides every pin. ``offered``
    is the in-order list of words handed over, the scoreboard's expectation for
    what appears on the link.
    """

    def __init__(self, tb, ch, width, pfx):
        self.tb, self.ch = tb, ch
        self.fc = flit_field_config(width)
        self.bfm = create_gaxi_master(
            tb.dut, f'FUB TX{ch.upper()}', '', tb.clk, field_config=self.fc, pkt_prefix=f'fub_tx{ch}',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=tb.log, multi_sig=True,
            # credit starvation is a test phase, not a hang: a FUB blocked for
            # thousands of cycles is expected (RDS-DV #93: a GAXI ready timeout
            # silently drops the beat rather than failing)
            timeout_cycles=200000)
        self.queue = deque()
        self.offered = []
        self.in_flight = 0
        cocotb.start_soon(self._pump())

    def put(self, word):
        self.queue.append(int(word))
        self.offered.append(int(word))

    def set_profile(self, name):
        self.bfm.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[name]['master']))

    @property
    def idle(self):
        return not self.queue and not self.in_flight

    async def _pump(self):
        while True:
            if not self.queue:
                await RisingEdge(self.tb.clk)
                continue
            batch = []
            while self.queue:
                pkt = GAXIPacket(self.fc)
                pkt.flit = self.queue.popleft()
                batch.append(pkt)
            self.in_flight = len(batch)
            await self.bfm.send_burst(batch)
            self.in_flight = 0


class FubRx:
    """An RX-channel FUB port: a framework GAXI slave; every word goes to ``words``
    and to ``handler`` (the Protocol layer above the link)."""

    def __init__(self, tb, ch, width, handler):
        self.tb, self.ch = tb, ch
        self.fc = flit_field_config(width)
        self.bfm = create_gaxi_slave(
            tb.dut, f'FUB RX{ch.upper()}', '', tb.clk, field_config=self.fc, pkt_prefix=f'fub_rx{ch}',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=tb.log, multi_sig=True)
        self.words = []
        self.handler = handler
        self.bfm.add_callback(self._got)

    def _got(self, pkt):
        word = int(pkt.flit)
        self.words.append(word)
        self.handler(word)

    def set_profile(self, name):
        self.bfm.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[name]['slave']))


class CHITBBase(TBBase):
    """Clock/reset, config, FUB ports, background watchers and the verdict."""

    PFX = ''                    # link pin prefix: 'm_chi_' (RN-F port) or 's_chi_' (HN-F port)
    TX_CHANNELS = ()            # the DUT's FUB TX channels (we drive)
    RX_CHANNELS = ()            # the DUT's FUB RX channels (we drain)

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.p = env_params()
        self.cfg_rn = cfg_from_env('RN-F')
        self.cfg_hn = cfg_from_env('HN-F')
        self.link_ctrl = bool(self.p.get('LINK_CTRL', 1))
        self.dw = self.cfg_rn.data_width
        self.seed = int(os.environ.get('SEED', '0'))
        self.rng = random.Random(self.seed)
        self.errors = []
        self.counts = Counter()
        self.phase = 'reset'
        self.outstanding = 0            # Protocol-layer transactions in progress
        self.fub_tx, self.fub_rx = {}, {}
        self.starved = Counter()        # cycles credit_starved was high, per phase
        self._busy_hi = 0
        self._quiet = 0
        self._cyc = 0
        self._prev_req = 0
        self._fell_at = None
        self.log.info(f"CHI {self.cfg_rn.short_name()} LINK_CTRL={int(self.link_ctrl)} "
                      f"SKID={self.p.get('SKID_DEPTH')} RXFIFO={self.p.get('RX_FIFO_DEPTH')} "
                      f"LC={self.cfg_rn.max_lcredit} seed={self.seed}")

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        self._pre_reset()
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        cocotb.start_soon(self.watch_status())

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _pre_reset(self):
        d = self.dut
        d.cfg_link_enable.value = 1
        d.cfg_link_hold.value = 0
        d.cfg_idle_cycles.value = 0         # phases choose their own
        d.cfg_rx_enable.value = 1
        d.fub_sactive.value = 0
        for ch in self.TX_CHANNELS:
            getattr(d, f'fub_tx{ch}_valid').value = 0

    # ---- FUB ports ----------------------------------------------------------
    def add_fub_tx(self, ch):
        self.fub_tx[ch] = FubTx(self, ch, self.cfg_rn.flit_width(ch), self.PFX)

    def add_fub_rx(self, ch, handler):
        self.fub_rx[ch] = FubRx(self, ch, self.cfg_rn.flit_width(ch), handler)

    def set_fub_profiles(self, tx_profile, rx_profile='fixed'):
        for f in self.fub_tx.values():
            f.set_profile(tx_profile)
        for f in self.fub_rx.values():
            f.set_profile(rx_profile)

    def random_optional(self, flit, channel, names):
        """Random values on the optional sideband fields this config carries:
        the link layer must carry them untouched."""
        for n, bits in optional_bits(self.cfg_rn, channel, names).items():
            flit.fields[n] = self.rng.getrandbits(bits)
        return flit

    # ---- DUT pin helpers --------------------------------------------------------
    def pin(self, name):
        return int(getattr(self.dut, name).value)

    def link_pin(self, name):
        return int(getattr(self.dut, f'{self.PFX}{name}').value)

    def set_sactive(self):
        self.dut.fub_sactive.value = int(self.outstanding > 0)

    async def wait_until(self, cond, timeout, what):
        for _ in range(timeout):
            if cond():
                return True
            await RisingEdge(self.clk)
        self.errors.append(f"timeout waiting for {what}")
        return False

    async def wait_cycles(self, n):
        for _ in range(n):
            await RisingEdge(self.clk)

    def check(self, cond, msg):
        if not cond:
            self.errors.append(msg)
        return cond

    # ---- background watchers ----------------------------------------------------------
    async def watch_status(self):
        """Per-cycle facts the DUT status pins give away:

        * credit_starved cycles per phase (the starve phase must see some)
        * TXSACTIVE high whenever a transaction is in progress (B14.7.2) and
          low once the port is quiet
        * with LINK_CTRL=0 the link pins stay tied low
        """
        while True:
            await FallingEdge(self.clk)
            if not int(self.rst_n.value):
                continue
            if self.pin('credit_starved'):
                self.starved[self.phase] += 1
            txs = self.link_pin('txsactive')
            if self.outstanding > 0:
                self._busy_hi += 1
                self._quiet = 0
                if self._busy_hi > 2:
                    self.counts['sactive_high_checks'] += 1
                    if not txs:
                        self.errors.append(f"{self.phase}: TXSACTIVE low with {self.outstanding} "
                                           f"transaction(s) in progress (B14.7.2)")
            else:
                self._busy_hi = 0
                self._quiet += 1
                if self._quiet > 8 and all(f.idle for f in self.fub_tx.values()):
                    self.counts['sactive_low_checks'] += 1
                    if txs:
                        self.errors.append(
                            f"{self.phase}: TXSACTIVE high with the port quiet (B14.7.2): fub_sactive="
                            f"{self.pin('fub_sactive')} valids="
                            f"{[self.pin(f'fub_tx{c}_valid') for c in self.TX_CHANNELS]} "
                            f"tx_state={self.pin('tx_link_state')} t={cocotb.utils.get_sim_time('ns')}")
            if self.link_ctrl:
                # evidence for B14 Table B14.3: how long after the partner's
                # LINKACTIVEREQ falls does this port still grant a credit?
                self._cyc += 1
                req = self.link_pin('rxlinkactivereq')
                if self._prev_req and not req:
                    self._fell_at = self._cyc
                self._prev_req = req
                if not req and self._fell_at is not None and any(
                        self.link_pin(f'rx{c}lcrdv') for c in self.RX_CHANNELS):
                    lag = self._cyc - self._fell_at
                    self.counts['grants_after_req_fall'] += 1
                    if lag > 1 and not self.counts['max_grant_lag_after_req_fall']:
                        self.log.warning(f"first LCRDV {lag} cycles after RXLINKACTIVEREQ fell, "
                                         f"t={cocotb.utils.get_sim_time('ns')}ns "
                                         f"(Table B14.3 allows the first DEACTIVATE cycle only)")
                    self.counts['max_grant_lag_after_req_fall'] = max(
                        self.counts['max_grant_lag_after_req_fall'], lag)
            partner = getattr(self, 'partner', None)
            if partner is not None:
                self.counts['rxsactive_checks'] += 1
                if self.pin('fub_rxsactive') != int(partner.txsactive):
                    self.errors.append(f"{self.phase}: fub_rxsactive {self.pin('fub_rxsactive')} != "
                                       f"partner TXSACTIVE {int(partner.txsactive)} (B14.7.3)")
            if not self.link_ctrl:
                self.counts['tied_checks'] += 1
                if self.link_pin('txlinkactivereq') or self.link_pin('rxlinkactiveack'):
                    self.errors.append("LINK_CTRL=0: a LINKACTIVE output is not tied low")

    # ---- link helpers --------------------------------------------------------------------
    def link_up(self):
        return self.pin('tx_link_state') == ST_RUN and self.pin('rx_link_state') == ST_RUN

    def link_down(self):
        return self.pin('tx_link_state') == ST_STOP and self.pin('rx_link_state') == ST_STOP

    # ---- link phases: the partner BFM (self.partner) is the other end ----------------
    async def run_hold(self):
        """cfg_link_hold keeps an idle link in RUN past the idle timeout."""
        self.phase = 'hold'
        self.dut.cfg_link_hold.value = 1
        self.dut.cfg_idle_cycles.value = 8
        await self.wait_cycles(80)
        ok = self.check(self.pin('tx_link_state') == ST_RUN, "cfg_link_hold: TX link left RUN while held")
        self.counts['hold_cycles'] += 80
        self.dut.cfg_link_hold.value = 0
        return ok

    async def run_idle_deactivate(self):
        """Idle RUN cycles take the link to STOP with every credit returned."""
        self.phase = 'idle'
        held = sum(self.pin(f'tx{c}_credits') for c in self.TX_CHANNELS)
        returns0 = sum(r.stats['lcrd_returns'] for r in self.partner.rx.values())
        self.dut.cfg_idle_cycles.value = 8
        ok = await self.wait_until(self.link_down, 3000, "idle deactivation (both directions STOP)")
        if ok:
            await self.wait_cycles(2)
            cred = [self.pin(f'tx{c}_credits') for c in self.TX_CHANNELS]
            outs = [self.pin(f'rx{c}_outstanding') for c in self.RX_CHANNELS]
            self.check(not any(cred) and not any(outs), f"STOP with credits: tx {cred} rx outstanding {outs}")
            ret = sum(r.stats['lcrd_returns'] for r in self.partner.rx.values()) - returns0
            self.check(ret >= held, f"deactivated holding {held} credits but returned {ret}")
            self.counts['credits_returned'] += ret
            self.counts['idle_deactivations'] += 1
        self.dut.cfg_idle_cycles.value = 0
        return ok

    async def bring_down(self):
        """From any link state to STOP: release the home's hold, idle the DUT out."""
        if self.link_down():
            return True
        self.partner.deactivate()
        self.dut.cfg_idle_cycles.value = 8
        ok = await self.wait_until(self.link_down, 3000, "bring_down")
        self.dut.cfg_idle_cycles.value = 0
        return ok

    async def run_remote_activation(self):
        """The home activates its own TX link while the DUT is idle (B14.6)."""
        self.phase = 'remote'
        ok = await self.bring_down()
        self.partner.activate()
        ok = ok and await self.wait_until(self.link_up, 1000, "remote activation (DUT TX and RX in RUN)")
        if ok:
            self.counts['remote_activations'] += 1
            self.check(self.pin('tx_link_state') == ST_RUN, "remote activation: DUT TX link not in RUN")
        self.partner.deactivate()
        self.dut.cfg_idle_cycles.value = 8
        ok = ok and await self.wait_until(self.link_down, 3000, "remote deactivation (both STOP)")
        self.dut.cfg_idle_cycles.value = 0
        return ok

    # ---- scoreboard ------------------------------------------------------------------------
    def compare_words(self, expected, got, where):
        """In-order, bit-exact: the same flit words, nothing lost, added or changed."""
        if len(got) != len(expected):
            self.errors.append(f"{where}: {len(got)} flits, expected {len(expected)}")
        for i, (e, g) in enumerate(zip(expected, got)):
            if e != g:
                self.errors.append(f"{where} flit {i}: 0x{g:X}, expected 0x{e:X} "
                                   f"(differs in bits 0x{e ^ g:X})")
                break
        self.counts[f'exact_{where.split()[0]}'] += min(len(got), len(expected))

    def check_violations(self, *bfms):
        for b in bfms:
            if b.total_violations():
                self.errors.append(f"{b.title}: violations {b.all_violations()}")

    def verdict(self, tag, required):
        """Log the counts; fail on any error or any required count of zero."""
        for k in required:
            if self.counts[k] <= 0:
                self.errors.append(f"count '{k}' is zero: that claim was never exercised")
        ok = not self.errors
        for e in self.errors[:20]:
            self.log.error(e)
        starved = dict(self.starved)
        self.log.info(f"CHI-VERDICT {tag} {'PASS' if ok else 'FAIL'} "
                      + ' '.join(f"{k}={v}" for k, v in sorted(self.counts.items()))
                      + f" starved_cycles={starved}")
        return ok
