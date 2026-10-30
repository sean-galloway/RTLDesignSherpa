# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_monlite_tb
# Purpose: Exact-packet testbenches for chi_rnf_port_monlite / chi_hnf_port_monlite
#
# Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-30
"""chi_monitor_lite, judged through the two port wrappers.

The traffic is the port testbenches' (CHIRnfPortTB / CHIHnfPortTB: GAXI BFMs on
the FUB side, the framework CHI home / requester BFM and a CHIMonitor on the
link). chi_monlite_common adds a MonbusSlave, a passive FUB sampler feeding
the spec-level model (chi_monlite_model) and the counted verdict. This file
holds the role-specific STIMULUS: the RN-F side issues requests and answers
snoops at flit level on the FUB, the HN-F side answers requests and sends
snoops; each role reaches the monitor's event classes (completion, retry,
snoop, orphan, table-full, RespErr, timeout, credit, backpressure, stream,
drop) through the BFM on the link or the FUB flits it owns.

Phases are windowed to at most MAX_TRANSACTIONS requests in flight, so the
exact phases can never fill the table; TABLE_FULL has its own phase built on
a held completion (margins of 100+ cycles, never a boundary).
"""

import os

import cocotb
from CocoTBFramework.components.chi import (
    CHIDatFlit,
    CHIReqFlit,
    CHIRspFlit,
    CHITransaction,
    DatOpcode,
    MemAttr,
    ReqOpcode,
    RspOpcode,
    Size,
    data_windows,
    resp_encode,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from TBClasses.chi.chi_hnf_port_tb import CHIHnfPortTB
from TBClasses.chi.chi_monlite_common import MonliteMixin
from TBClasses.chi.chi_monlite_model import PT_CHAN, PT_COMPL, PT_ERR, PT_STREAM
from TBClasses.chi.chi_rnf_port_tb import CHIRnfPortTB
from TBClasses.chi.chi_tb_common import HN_ID, LINK_PROFILES, RN_ID, CHITBBase
from TBClasses.monbus import PktType

COUNTS = {'gate': 10, 'func': 24, 'full': 60}
TIMEOUT_US = 1
STALL_T = 8
DERR, NDERR = 2, 3
RSP_UC = resp_encode('UC')
ORPH = 0xF00          # TxnIDs / DBIDs no request ever uses


def level():
    lv = os.environ.get('TEST_LEVEL', 'gate').lower()
    return lv if lv in COUNTS else 'gate'


class _RoleBase(MonliteMixin):
    """Phases both roles run, over role hooks (issue / snoop / inject)."""

    def _init_role(self):
        self._init_monlite()
        self.n_ops = COUNTS[level()]
        self.window = max(1, self.max_txn)
        self.orphan_ids = set()
        self.expected_end_errors = []

    def _pre_reset(self):
        super()._pre_reset()
        self._monlite_pins()

    def starve_ops(self):
        """Enough line transfers that their data flits outnumber the credits held."""
        pkts = max(1, 512 // self.dw)
        return [(self.STARVE_KIND, 0)] * ((self.cfg.max_lcredit + 6 + pkts - 1) // pkts)

    def mix(self, n, eca=0.0):
        ops = [('w' if i % 2 else 'r', int(self.rng.random() < eca)) for i in range(n)]
        self.rng.shuffle(ops)
        return ops

    async def settle(self, what):
        ok = await self.wait_idle(what)
        await self.drain()
        return ok

    async def mphase(self, name, ops, mark=None, **kw):
        mark = len(self.model.events) if mark is None else mark
        ok = await self.traffic(ops)
        await self.drain()
        self.verify(name, mark, **kw)
        return ok

    # ---- the suite ------------------------------------------------------------------
    async def run_monlite_suite(self):
        if os.environ.get('USE_MONITOR', '1') == '0':
            return await self.run_nomon_suite()
        n = self.n_ops
        await self.wait_cycles(40)
        ok = await self.mphase('basic', self.mix(n), mark=0)                       # includes the link bring-up
        ok = await self.mphase('expcompack', self.mix(n, 1.0)) and ok
        ok = await self.mphase('mixed-ack', self.mix(n, 0.5)) and ok
        ok = await self.phase_separate(n) and ok
        ok = await self.phase_retry(n) and ok
        ok = await self.phase_snoops() and ok
        if self.link_ctrl:
            ok = await self.phase_links(n) and ok
        ok = await self.phase_orphans() and ok
        ok = await self.phase_table_full() and ok
        ok = await self.phase_resp_err() and ok
        ok = await self.phase_credit(n) and ok
        ok = await self.phase_timeouts(n) and ok
        ok = await self.phase_mask(n) and ok
        ok = await self.phase_disable(n) and ok
        ok = await self.phase_clear(n) and ok
        ok = await self.phase_drop() and ok
        ok = await self.phase_protocol() and ok
        await self.wait_cycles(50)
        passed = self.check_end() and ok
        self.counts['end_checks'] += 1
        return self.final_verdict(self.VERDICT, self.monlite_required()) and passed

    async def run_nomon_suite(self):
        """USE_MONITOR = 0: the port is the port; the monbus stays low and every counter reads zero."""
        n = self.n_ops
        d = self.dut
        self.enabled = False
        await self.wait_cycles(40)
        ok = await self.traffic(self.mix(n))
        ok = await self.traffic(self.mix(n, 1.0)) and ok
        ok = await self.traffic(self.mix(n, 0.5)) and ok
        await self.drain()
        got = self.take()
        if got:
            self.mfail(f"nomon: {len(got)} packets with USE_MONITOR = 0")
        if int(d.monbus_valid.value):
            self.mfail("nomon: monbus_valid high with USE_MONITOR = 0")
        for k in ('txn_count', 'snoop_count', 'error_count', 'active_count', 'dropped_count'):
            if int(getattr(d, k).value):
                self.mfail(f"nomon: {k} = {int(getattr(d, k).value)}")
        self.counts['nomon_checks'] += int(not got)
        await self.wait_cycles(50)
        passed = self.check_end() and ok
        self.counts['end_checks'] += 1
        return self.final_verdict(self.VERDICT, ['nomon_checks', 'end_checks']) and passed

    def monlite_required(self):
        req = ['packets_checked', 'ev_TXN', 'ev_RETRY', 'ev_PCRD_GRANT', 'ev_SNP', 'ev_ORPHAN_RSP',
               'ev_ORPHAN_DAT', 'ev_ORPHAN_ACK', 'ev_ORPHAN_SNP_RSP', 'ev_TABLE_FULL', 'ev_SNP_TABLE_FULL',
               'ev_RESP_ERR', 'ev_STARVED', 'ev_BACKPRESSURE', 'ev_TMO_TXN', 'ev_TMO_SNP', 'ev_TMO_CREDIT',
               'ev_PCRD_RETURN', 'ev_READ_RECEIPT', 'drop_reports', 'dropped_reported', 'timestamp_checks',
               'pin_checks', 'txn_count_sequences', 'snoop_count_sequences', 'mask_checks', 'disable_checks',
               'clear_checks', 'active_full_checks', 'absorbed_violations', 'ev_PROTOCOL']
        if self.link_ctrl:
            req += ['stream_events', 'ev_TX_1', 'ev_TX_2', 'ev_RX_3', 'ev_TMO_LINK']
        return req

    # ---- phases shared by the roles ----------------------------------------------------
    async def phase_separate(self, n):
        self.set_flow(separate=True)
        ok = await self.mphase('separate', self.mix(n, 0.5))
        self.set_flow(separate=False)
        return ok

    async def phase_retry(self, n):
        self.set_flow(retry=True)
        ok = await self.mphase('retry', self.mix(n, 0.5))
        self.set_flow(retry=False)
        return ok

    async def phase_links(self, n):
        """Link teardown and bring-up in both directions: Stream events."""
        mark = len(self.model.events)
        ok = await self.run_hold()
        ok = await self.run_idle_deactivate() and ok
        ok = await self.run_remote_activation() and ok
        await self.drain()
        ok = await self.traffic(self.mix(4)) and ok
        ok = await self.run_idle_deactivate() and ok
        ok = await self.run_snoop_wake(2) and ok
        ok = await self.traffic(self.mix(4)) and ok
        await self.drain()
        self.counts['stream_events'] += sum(1 for e in self.model.events[mark:] if e.ptype == PT_STREAM)
        self.verify('links', mark)
        return ok

    async def phase_credit(self, n):
        """Credit/STARVED and Credit/BACKPRESSURE at an 8-cycle threshold."""
        d = self.dut
        d.cfg_stall_threshold.value = STALL_T
        d.cfg_credit_enable.value = 1
        start, mark = self.cyc, len(self.model.events)
        await self.starve_and_block(n)
        d.cfg_credit_enable.value = 0
        await self.drain()
        self.add_credit_events(start, STALL_T)
        self.verify('credit', mark)
        d.cfg_stall_threshold.value = 0
        return True

    async def phase_timeouts(self, n):
        d = self.dut
        d.cfg_timeout_cycles.value = TIMEOUT_US
        mark, start = len(self.model.events), self.cyc
        ok = await self.hold_completions()
        await self.drain()
        self.add_slot_timeouts(TIMEOUT_US, mark)
        self.add_timeout_events(start, TIMEOUT_US)
        # TXN timeout, credit timeout and a retiring slot can fall in one cycle: three candidates,
        # two slots, one counted drop. The accounting (missing <= reported) is the check.
        self.verify('timeouts', mark, drops_ok=True)
        d.cfg_timeout_cycles.value = 0
        return ok

    async def phase_mask(self, n):
        d = self.dut
        d.cfg_chi_pkt_mask.value = 1 << int(PktType.PktTypeCompletion)
        mark = len(self.model.events)
        ok = await self.traffic(self.mix(6))
        await self.drain()
        got = self.verify('mask-completion', mark, mask=1 << int(PktType.PktTypeCompletion))
        self.counts['mask_checks'] += sum(1 for p, _ in got if int(p.packet_type) == PT_COMPL) == 0
        d.cfg_chi_pkt_mask.value = (1 << int(PktType.PktTypeError)) | (1 << int(PktType.PktTypeChannel))
        mark = len(self.model.events)
        ok = await self.inject_error_and_channel() and ok
        await self.drain()
        got = self.verify('mask-error-channel', mark,
                          mask=(1 << int(PktType.PktTypeError)) | (1 << int(PktType.PktTypeChannel)))
        self.counts['mask_checks'] += sum(1 for p, _ in got if int(p.packet_type) in (PT_ERR, PT_CHAN)) == 0
        d.cfg_chi_pkt_mask.value = 0
        return ok

    async def phase_disable(self, n):
        """cfg_monitor_enable = 0: traffic flows, nothing is said, nothing counted."""
        d = self.dut
        await self.drain()
        self.take()
        d.cfg_monitor_enable.value = 0
        self.enabled = False
        await self.wait_cycles(4)
        ok = await self.traffic(self.mix(6, 0.5))
        await self.drain()
        got = self.take()
        self.counts['disable_checks'] += int(not got)
        if got:
            self.mfail(f"disable: {len(got)} packets with cfg_monitor_enable = 0")
        for k in ('txn_count', 'snoop_count', 'error_count', 'active_count', 'dropped_count'):
            if int(getattr(d, k).value):
                self.mfail(f"disable: {k} = {int(getattr(d, k).value)}")
        d.cfg_monitor_enable.value = 1
        await self.wait_cycles(4)
        self.enabled = True
        self.model_clear()
        return ok

    async def phase_clear(self, n):
        d = self.dut
        mark = len(self.model.events)
        ok = await self.traffic(self.mix(4))
        await self.drain()
        self.verify('before-clear', mark)
        d.cam_clear.value = 1
        await self.wait_cycles(1)
        d.cam_clear.value = 0
        await self.wait_cycles(4)
        self.model_clear()
        for k in ('txn_count', 'snoop_count', 'error_count', 'active_count', 'dropped_count'):
            if int(getattr(d, k).value):
                self.mfail(f"clear: {k} = {int(getattr(d, k).value)}")
        self.counts['clear_checks'] += 1
        mark = len(self.model.events)
        ok = await self.traffic(self.mix(4)) and ok
        await self.drain()
        self.verify('after-clear', mark)
        return ok

    async def phase_drop(self):
        """monbus_ready held low through a burst: queue fills, the rest is
        counted and reported as EVENT_DROPPED once the queue drains."""
        d = self.dut
        await self.drain()
        mark = len(self.model.events)
        self.set_monbus_ready(2000)
        ok = await self.traffic(self.mix(max(12, 3 * self.max_txn)))
        await self.wait_cycles(20)
        self.counts['drop_pending_checks'] += int(int(d.dropped_count.value) > 0)
        if not int(d.dropped_count.value):
            self.mfail("drop: dropped_count stayed 0 with the bus held")
        self.set_monbus_ready(0)
        await self.drain(1500)
        self.verify('drop', mark, drops_ok=True)
        return ok

    def check_end(self):
        """The port testbench's end checks, less the findings the protocol
        injection is MEANT to cause (each must be present: the port set
        protocol_error and dropped the one flit that had no credit)."""
        import re
        super().check_end()
        for pat, required in self.expected_end_errors:
            hit = next((e for e in self.errors if re.fullmatch(pat, e)), None)
            if hit is None:
                if required:
                    self.mfail(f"end: expected port finding /{pat}/ did not occur")
            else:
                self.errors.remove(hit)
                self.counts['expected_port_findings'] += 1
        return not self.errors and not self.mon_errors


def _be_all(dw):
    return (1 << (dw // 8)) - 1


class CHIRnfMonliteTB(_RoleBase, CHIRnfPortTB):
    """chi_rnf_port_monlite: the TB is the Protocol layer on the FUB, the
    framework CHI home BFM is on the link."""

    VERDICT = 'chi_rnf_port_monlite'
    STARVE_KIND = 'w'
    TAP = {'req': 'fub_txreq', 'cpl_rsp': 'fub_rxrsp', 'cpl_dat': 'fub_rxdat',
           'rq_rsp': 'fub_txrsp', 'rq_dat': 'fub_txdat', 'snp': 'fub_rxsnp'}
    BP_CHANNELS = ('cpl_rsp', 'cpl_dat', 'snp')

    def __init__(self, dut):
        super().__init__(dut)
        self._init_role()
        self.snp_hold = False
        self.snp_data = False
        self.pending_snp = []
        self.resperr_dat = False
        self.resperr_rsp = False
        orig_send = self.hn.send

        def send(channel, flit, _orig=orig_send):
            # RespErr injection on the home BFM's own flits (the BFM builds
            # and times them; only the field changes)
            if self.resperr_dat and channel == 'dat' and int(flit.opcode) == int(DatOpcode.CompData):
                flit.resperr = DERR if flit.txnid % 2 else NDERR
            if self.resperr_rsp and channel == 'rsp' and int(flit.opcode) == int(RspOpcode.CompDBIDResp):
                flit.resperr = DERR if flit.txnid % 2 else NDERR
            _orig(channel, flit)

        self.hn.send = send

    async def setup_clocks_and_reset(self):
        await CHITBBase.setup_clocks_and_reset(self)     # not CHIRnfPortTB's: its write watcher assumes no retry

    # ---- flow knobs ---------------------------------------------------------------------
    def set_flow(self, separate=None, retry=None):
        opt = self.hn.home.opt
        if separate is not None:
            opt.read_separate = opt.write_separate = 1.0 if separate else 0.0
        if retry is not None:
            opt.retry_rate = 1.0 if retry else 0.0

    # ---- issue ---------------------------------------------------------------------------------
    def req_flit(self, txn):
        f = CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=txn.txnid, opcode=int(txn.opcode),
                       size=int(txn.size), addr=txn.addr, allowretry=txn.allowretry, pcrdtype=txn.pcrdtype,
                       memattr=txn.memattr, snpattr=0, expcompack=txn.expcompack, order=txn.order)
        self.random_optional(f, 'req', ('rsvdc', 'mpam', 'pbha', 'mecid', 'secsid1'))
        return f

    def issue_ex(self, kind, addr, data=None, eca=0, order=0):
        opcode = ReqOpcode.ReadNoSnp if kind == 'r' else ReqOpcode.WriteNoSnpFull
        txn = CHITransaction(opcode=opcode, addr=addr, size=Size.B64, srcid=RN_ID, tgtid=HN_ID,
                             memattr=int(MemAttr.EWA), snpattr=0, expcompack=eca, order=order, data=data)
        if kind == 'r':
            self.expect[id(txn)] = ('r', addr, self.ref[addr])
        else:
            self.ref[addr] = data
            self.expect[id(txn)] = ('w', addr, data)
        self.tracker.issue(txn)
        self.outstanding += 1
        self.set_sactive()
        self.fub_tx['req'].put(self.req_flit(txn).pack())
        return txn

    def _complete(self, txn):
        kind = self.expect[id(txn)][0]
        if kind == 'r' and txn.expcompack:
            self.outstanding += 1          # the base retires the read on its last data flit; the CompAck is still to go
        super()._complete(txn)
        if kind == 'w' or txn.expcompack:
            cocotb.start_soon(self._retire_write(txn))

    async def _retire_write(self, txn):
        """A transaction is in progress until the home has received the last
        flit the port owed it (write data, CompAck): TXSACTIVE may fall in the
        cycle that flit leaves (B14.7.2). The home's own events are the
        earliest the TB can see that; the open-table pop comes a cycle later."""
        key = (RN_ID, txn.txnid)

        def last_flit_in():
            e = self.hn.open.get(key)
            if e is None:
                return True
            data_ok = txn.opcode != ReqOpcode.WriteNoSnpFull or e.data_event.is_set()
            ack_ok = (not txn.expcompack) or e.compack_event.is_set()
            return data_ok and ack_ok

        await self.wait_until(last_flit_in, 20000, 'home to receive the last flit of a transaction')
        self.outstanding -= 1
        self.set_sactive()

    def _act(self, txn, actions, what):
        rest = []
        for a in actions:
            if a.kind == 'send_compack':
                r = CHIRspFlit(self.cfg, tgtid=a.tgtid, srcid=RN_ID, txnid=a.txnid, opcode=int(RspOpcode.CompAck))
                self.fub_tx['rsp'].put(r.pack())
                self.counts['compack_sent'] += 1
            elif a.kind == 'retry':
                self.fub_tx['req'].put(self.req_flit(txn).pack())
                self.counts['retry_resent'] += 1
            else:
                rest.append(a)
        super()._act(txn, rest, what)

    # ---- FUB RX handlers: skip what the TB injected on purpose ------------------------------
    def on_fub_rsp(self, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        if f.txnid in self.orphan_ids and int(f.opcode) != int(RspOpcode.PCrdGrant):
            self.counts['orphan_rsp_delivered'] += 1
            return
        super().on_fub_rsp(word)

    def on_fub_dat(self, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        if f.txnid in self.orphan_ids:
            self.counts['orphan_dat_delivered'] += 1
            return
        super().on_fub_dat(word)

    def on_fub_snp(self, word):
        from CocoTBFramework.components.chi import CHISnpFlit
        f = CHISnpFlit.from_word(self.cfg, word)
        self.counts['rx_snp'] += 1
        self.snp_seen[f.txnid] = (f.opcode, f.byte_addr, f.srcid)
        self.outstanding += 1
        self.set_sactive()
        self.pending_snp.append(f)
        if not self.snp_hold:
            self.release_snoops()

    def release_snoops(self):
        pend, self.pending_snp = self.pending_snp, []
        for f in pend:
            if self.snp_data:
                for did, lo in data_windows(f.byte_addr & ~63, 64, self.dw):
                    d = CHIDatFlit(self.cfg, tgtid=f.srcid, srcid=RN_ID, txnid=f.txnid,
                                   opcode=int(DatOpcode.SnpRespData), resp=resp_encode('I'), dataid=did,
                                   be=_be_all(self.dw))
                    self.fub_tx['dat'].put(d.pack())
                self.counts['snp_resp_data_sent'] += 1
            else:
                r = CHIRspFlit(self.cfg, tgtid=f.srcid, srcid=RN_ID, txnid=f.txnid,
                               opcode=int(RspOpcode.SnpResp), resp=resp_encode('I'))
                self.fub_tx['rsp'].put(r.pack())
                self.counts['snp_resp_sent'] += 1

    # ---- traffic ------------------------------------------------------------------------------------
    def idle_now(self):
        return (self.tracker.outstanding == 0 and all(f.idle for f in self.fub_tx.values())
                and not self.hn.open and not self.hn.home.open_snoops and not self.pending_snp
                and not self.hn.have_work())

    async def wait_idle(self, what, extra=40):
        ok = await self.wait_until(self.idle_now, 80000, what)
        await self.wait_cycles(extra)
        return ok

    async def traffic(self, ops, order=0):
        ok = True
        for i in range(0, len(ops), self.window):
            for kind, eca in ops[i:i + self.window]:
                if kind == 'r':
                    self.issue_ex('r', self.new_seeded_line(), eca=eca, order=order)
                else:
                    self.issue_ex('w', self.alloc_line(), bytes(self.rng.getrandbits(8) for _ in range(64)), eca)
            ok = await self.wait_idle('windowed traffic') and ok
        return ok

    # ---- snoops ------------------------------------------------------------------------------------------
    async def snoops_batch(self, k, data=False, hold_cycles=0):
        self.snp_data = data
        self.snp_hold = hold_cycles > 0
        tasks = [cocotb.start_soon(self.snoop_one(self.new_seeded_line())) for _ in range(k)]
        if hold_cycles:
            await self.wait_cycles(hold_cycles)
            self.snp_hold = False
            self.release_snoops()
        for t in tasks:
            await t
        self.check_snoops()
        self.snp_data = False
        return await self.wait_idle('snoop batch')

    async def phase_snoops(self):
        mark = len(self.model.events)
        k = min(3, self.max_snp)
        ok = await self.snoops_batch(k)
        ok = await self.snoops_batch(k, data=True) and ok
        # more snoops than snoop slots, responses held: SNP_TABLE_FULL, then the orphans' responses
        ok = await self.snoops_batch(self.max_snp + 2, hold_cycles=150) and ok
        self.counts['snp_resp_total'] += self.counts['snp_resp_sent'] + self.counts['snp_resp_data_sent']
        await self.drain()
        self.verify('snoops', mark)
        return ok

    # ---- hold / starve / block --------------------------------------------------------------------------------
    async def starve_and_block(self, n):
        self.hn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                                 'drain_gap': ([(14, 20)], [1]), 'ack_delay': ([(0, 0)], [1])}))
        for r in self.hn.rx.values():
            r.credit.buffer_depth = 1
        ok = await self.traffic(self.starve_ops() + self.mix(n))
        self.hn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        for r in self.hn.rx.values():
            r.credit.buffer_depth = self.cfg.max_lcredit
        slow = FlexRandomizer({'ready_delay': ([(20, 30)], [1])})
        for f in self.fub_rx.values():
            f.bfm.set_randomizer(slow)
        ok = await self.traffic(self.mix(n // 2 + 2)) and ok
        for f in self.fub_rx.values():
            f.set_profile('fixed')
        return ok

    # ---- error stimulus ------------------------------------------------------------------------------------------
    def rsp_to_rn(self, op, txnid, **kw):
        return CHIRspFlit(self.cfg, tgtid=RN_ID, srcid=HN_ID, txnid=txnid, opcode=int(op), **kw)

    def dat_to_rn(self, op, txnid, **kw):
        return CHIDatFlit(self.cfg, tgtid=RN_ID, srcid=HN_ID, txnid=txnid, opcode=int(op), dataid=0,
                          homenid=HN_ID, be=_be_all(self.dw), **kw)

    async def inject_orphans(self):
        """One of each orphan class, from the home BFM (toward the RN) and
        from the FUB (the RN's own CompAck / write data / snoop responses),
        spaced so the 4-deep event queue never overflows."""
        hn, fx = self.hn, self.fub_tx
        self.outstanding += 1          # the injected FUB flits are work in progress (B14.7.2)
        self.set_sactive()
        ids = [ORPH + i for i in range(10)]
        self.orphan_ids |= set(ids)
        pr = CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[8], opcode=int(ReqOpcode.PCrdReturn),
                        allowretry=0, pcrdtype=2, size=int(Size.B1))
        steps = [
            lambda: hn.send('rsp', self.rsp_to_rn(RspOpcode.Comp, ids[0])),
            lambda: hn.send('rsp', self.rsp_to_rn(RspOpcode.RetryAck, ids[1], pcrdtype=3)),
            lambda: hn.send('dat', self.dat_to_rn(DatOpcode.CompData, ids[2])),
            lambda: hn.send('dat', self.dat_to_rn(DatOpcode.DataSepResp, ids[3])),
            lambda: fx['rsp'].put(CHIRspFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[4],
                                             opcode=int(RspOpcode.CompAck)).pack()),
            lambda: fx['dat'].put(CHIDatFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[5],
                                             opcode=int(DatOpcode.NonCopyBackWriteData), dataid=0,
                                             be=_be_all(self.dw)).pack()),
            lambda: fx['rsp'].put(CHIRspFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[6],
                                             opcode=int(RspOpcode.SnpResp), resp=resp_encode('I')).pack()),
            lambda: fx['dat'].put(CHIDatFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[7],
                                             opcode=int(DatOpcode.SnpRespData), dataid=0, resp=resp_encode('I'),
                                             be=_be_all(self.dw)).pack()),
            lambda: hn.send('rsp', self.rsp_to_rn(RspOpcode.ReadReceipt, ids[9])),   # a Channel event even unmatched
            lambda: fx['req'].put(pr.pack()),     # PCrdReturn: a request-channel No-Op, a Channel event
        ]
        for step in steps:
            step()
            await self.wait_cycles(12)
        await self.wait_cycles(20)
        self.outstanding -= 1
        self.set_sactive()
        return len(steps)

    async def phase_orphans(self):
        mark, snap = len(self.model.events), self.viol_snapshot(self.hn, self.mon)
        self.hn.home.opt.comp_delay = (150, 150)
        # a live ordered read gets a ReadReceipt while its slot is open
        txn = self.issue_ex('r', self.new_seeded_line(), order=2)
        await self.wait_cycles(30)
        self.hn.send('rsp', self.rsp_to_rn(RspOpcode.ReadReceipt, txn.txnid))
        n = await self.inject_orphans()
        ok = await self.wait_idle('orphans')
        self.hn.home.opt.comp_delay = (0, 0)
        await self.drain()
        self.verify('orphans', mark)
        self.absorb(snap, expect_min=n, what='orphans')
        return ok

    async def phase_table_full(self):
        mark = len(self.model.events)
        self.hn.home.opt.comp_delay = (150, 150)
        count = self.max_txn + 3
        for _ in range(count):
            self.issue_ex('r', self.new_seeded_line())
        await self.wait_cycles(80)
        full = int(self.dut.active_count.value)
        if full != self.max_txn:
            self.mfail(f"table-full: active_count {full}, expected {self.max_txn} with {count} requests held")
        self.counts['active_full_checks'] += int(full == self.max_txn)
        ok = await self.wait_idle('table full')
        self.hn.home.opt.comp_delay = (0, 0)
        await self.drain()
        self.verify('table-full', mark)
        return ok

    async def phase_resp_err(self):
        mark = len(self.model.events)
        self.resperr_dat = self.resperr_rsp = True
        w, self.window = self.window, 1        # one read at a time: 4 RESP_ERR events per read stay under the queue's drain rate
        ok = await self.traffic(self.mix(8, 0.5))
        self.window = w
        self.resperr_dat = self.resperr_rsp = False
        await self.drain()
        self.verify('resp-err', mark)
        return ok

    async def inject_error_and_channel(self):
        """For the mask phase: an orphan response (Error) and a PCrdReturn (Channel)."""
        snap = self.viol_snapshot(self.hn, self.mon)
        self.outstanding += 1
        self.set_sactive()
        ids = [ORPH + 0x20, ORPH + 0x21]
        self.orphan_ids |= set(ids)
        self.hn.send('rsp', self.rsp_to_rn(RspOpcode.Comp, ids[0]))
        pr = CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[1], opcode=int(ReqOpcode.PCrdReturn),
                        allowretry=0, pcrdtype=1, size=int(Size.B1))
        self.fub_tx['req'].put(pr.pack())
        ok = await self.wait_idle('masked injection')
        self.outstanding -= 1
        self.set_sactive()
        self.absorb(snap, expect_min=1, what='mask injection')
        return ok

    async def hold_completions(self):
        """Withheld completions: Timeout/TXN, /SNP, /CREDIT, /LINK at 1 us."""
        opt = self.hn.home.opt
        opt.comp_delay = (260, 260)
        ok = await self.traffic(self.mix(min(4, self.max_txn), 0.5))
        opt.comp_delay = (0, 0)
        ok = await self.snoops_batch(min(2, self.max_snp), hold_cycles=260) and ok
        # credit: a drain slower than 1 us per flit on a one-slot pool
        self.hn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                               'drain_gap': ([(300, 300)], [1]), 'ack_delay': ([(0, 0)], [1])}))
        for r in self.hn.rx.values():
            r.credit.buffer_depth = 1
        ok = await self.traffic(self.starve_ops()) and ok     # more data flits than credits held
        self.hn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        for r in self.hn.rx.values():
            r.credit.buffer_depth = self.cfg.max_lcredit
        # link: the home sits on LINKACTIVEREQ for 3 us
        if self.link_ctrl:
            ok = await self.bring_down() and ok
            self.hn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                                   'drain_gap': ([(0, 0)], [1]), 'ack_delay': ([(300, 300)], [1])}))
            ok = await self.traffic(self.mix(1)) and ok
            self.hn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        return ok

    async def protocol_overflow(self):
        mark, snap = len(self.model.events), self.viol_snapshot(self.hn, self.mon)
        n = min(int(os.environ.get('RX_FIFO_DEPTH', self.cfg.max_lcredit)), self.cfg.max_lcredit) + 1
        ids = [ORPH + 0x40 + i for i in range(n)]
        self.orphan_ids |= set(ids)
        await self.traffic(self.mix(2))
        self.fub_rx['rsp'].bfm.set_randomizer(FlexRandomizer({'ready_delay': ([(14, 14)], [1])}))
        self.hn.tx['rsp'].credit.credits += 1               # the tamper: one credit the DUT never granted
        for i in ids:
            self.hn.send('rsp', self.rsp_to_rn(RspOpcode.ReadReceipt, i))
        await self.wait_cycles(20 * n + 300)
        self.fub_rx['rsp'].set_profile('fixed')
        await self.drain()
        self.counts['protocol_error_pin'] += int(self.dut.protocol_error.value)
        self.verify('protocol', mark, idle=False)
        self.absorb(snap, expect_min=1, what='protocol')
        fub = len(self.fub_rx['rsp'].words)
        self.expected_end_errors = [(r'DUT protocol_error set', True),
                                    (rf'rsp fub: {fub} flits, expected {fub + 1}', False)]   # the port may or may not drop the flit
        return True

    async def phase_protocol(self):
        """Error/PROTOCOL: the port's sticky protocol_error. Fault injection
        on the BFM's credit state: it is handed one L-Credit more than the DUT
        granted and sends one flit too many on a channel whose FUB side is slow,
        so the DUT sees a flit with no credit outstanding. Last: the flag is
        sticky until reset."""
        return await self.protocol_overflow()


class CHIHnfMonliteTB(_RoleBase, CHIHnfPortTB):
    """chi_hnf_port_monlite: the TB is the completer on the FUB (answers
    requests, sends snoops), the framework CHI requester BFM is on the link."""

    VERDICT = 'chi_hnf_port_monlite'
    STARVE_KIND = 'r'
    UNIT_ID = 0x0C
    AGENT_ID = 0x00D1
    TAP = {'req': 'fub_rxreq', 'cpl_rsp': 'fub_txrsp', 'cpl_dat': 'fub_txdat',
           'rq_rsp': 'fub_rxrsp', 'rq_dat': 'fub_rxdat', 'snp': 'fub_txsnp'}
    BP_CHANNELS = ('req', 'rq_rsp', 'rq_dat')
    PCRD_TYPE = 2

    def __init__(self, dut):
        super().__init__(dut)
        self._init_role()
        self.sep = False
        self.retry = False
        self.comp_delay = 0
        self.resperr_dat = False
        self.resperr_rsp = False
        self.snp_dbl = {}               # snoop TxnID -> data packets seen
        self.snp_data_ok = 0

    # ---- flow knobs ----------------------------------------------------------------------------
    def set_flow(self, separate=None, retry=None):
        if separate is not None:
            self.sep = separate
        if retry is not None:
            self.retry = retry

    def _err(self):
        return None

    # ---- completer: FUB RX handlers --------------------------------------------------------------
    def on_fub_req(self, word):
        f = CHIReqFlit.from_word(self.cfg, word)
        self.counts['rx_req'] += 1
        op = int(f.opcode)
        if op == int(ReqOpcode.PCrdReturn):
            self.counts['rx_pcrdreturn'] += 1
            return
        resend = (not f.allowretry) and f.pcrdtype
        if not resend:
            self.outstanding += 1
            self.set_sactive()
        if self.retry and f.allowretry:
            self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=f.srcid, srcid=HN_ID, txnid=f.txnid,
                                              opcode=int(RspOpcode.RetryAck), pcrdtype=self.PCRD_TYPE).pack())
            cocotb.start_soon(self._grant_later(f.srcid))
            self.counts['retry_sent'] += 1
            return
        try:
            e = self.tracker.accept(f)
        except ValueError as err:
            self.errors.append(f"REQ {f.opcode_name}: {err}")
            return
        if op == int(ReqOpcode.ReadNoSnp):
            cocotb.start_soon(self.serve_read(e, int(f.order)))
        elif op == int(ReqOpcode.WriteNoSnpFull):
            cocotb.start_soon(self.serve_write(e))
        else:
            self.errors.append(f"unexpected REQ opcode {f.opcode_name}")

    async def _grant_later(self, srcid):
        await self.wait_cycles(8)
        self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=srcid, srcid=HN_ID, txnid=0,
                                          opcode=int(RspOpcode.PCrdGrant), pcrdtype=self.PCRD_TYPE).pack())

    def _errval(self, e):
        return (DERR if e.txnid % 2 else NDERR)

    async def serve_read(self, e, order):
        await self.wait_cycles(self.comp_delay + self.rng.randint(*self.read_delay))
        line = e.addr & ~63
        data = bytes(self.mem[line])
        eca = bool(e.expcompack)
        dbid = self.tracker.allocate_dbid(e) if eca else 0
        err = self._errval(e) if self.resperr_dat else 0
        if order:
            self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid,
                                              opcode=int(RspOpcode.ReadReceipt)).pack())
        if self.sep:
            self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid,
                                              opcode=int(RspOpcode.RespSepData), dbid=dbid).pack())
        op = DatOpcode.DataSepResp if self.sep else DatOpcode.CompData
        for did, wlo in data_windows(e.addr, e.nbytes, self.dw):
            f = CHIDatFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid, opcode=int(op), resp=RSP_UC,
                           dataid=did, homenid=HN_ID, dbid=dbid, resperr=err, ccid=(e.addr >> 4) & 3,
                           be=_be_all(self.dw))
            f.set_data_bytes(data[wlo - line: wlo - line + self.dw // 8])
            self.random_optional(f, 'dat', ('rsvdc', 'mecid', 'datacheck', 'poison'))
            self.fub_tx['dat'].put(f.pack())
            self.counts['comp_data_flits'] += 1
        if not eca:
            self.tracker.retire(e)

    async def serve_write(self, e):
        await self.wait_cycles(self.comp_delay)
        dbid = self.tracker.allocate_dbid(e)
        e.sep_write = self.sep
        err = self._errval(e) if self.resperr_rsp else 0
        op = RspOpcode.DBIDResp if self.sep else RspOpcode.CompDBIDResp
        self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid, opcode=int(op),
                                          dbid=dbid, resperr=err).pack())

    def on_fub_rsp(self, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        if f.txnid in self.orphan_ids:
            self.counts['orphan_rsp_delivered'] += 1
            return
        if int(f.opcode) == int(RspOpcode.CompAck):
            self.counts['rx_rsp'] += 1
            try:
                e = self.tracker.on_compack(f)
            except (LookupError, ValueError) as err:
                self.errors.append(f"CompAck TxnID {f.txnid:#x}: {err}")
                return
            self.counts['compack_seen'] += 1
            self._maybe_retire(e)
            return
        super().on_fub_rsp(word)

    def _maybe_retire(self, e):
        if e.opcode == ReqOpcode.ReadNoSnp:
            if getattr(e, 'compack_seen', False):
                self.tracker.retire(e)
        elif getattr(e, 'write_complete', False) and (not e.expcompack or getattr(e, 'compack_seen', False)):
            self.tracker.retire(e)

    def on_fub_dat(self, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        if f.txnid in self.orphan_ids:
            self.counts['orphan_dat_delivered'] += 1
            return
        self.counts['rx_dat'] += 1
        if int(f.opcode) in (int(DatOpcode.SnpRespData), int(DatOpcode.SnpRespDataPtl)):
            n = self.snp_dbl.get(f.txnid, 0) + 1
            self.snp_dbl[f.txnid] = n
            if n >= len(data_windows(self.snoops_open.get(f.txnid, 0) & ~63, 64, self.dw)):
                self.snoops_open.pop(f.txnid, None)
                self.snp_dbl.pop(f.txnid, None)
                self.counts['snoops_ok'] += 1
                self.counts['snp_resp_data_seen'] += 1
                self.outstanding -= 1
                self.set_sactive()
            return
        try:
            e = self.tracker.on_write_data(f)
        except (LookupError, ValueError) as err:
            self.errors.append(f"DAT {f.opcode_name} TxnID {f.txnid:#x}: {err}")
            return
        if not e.write_complete:
            return
        line = e.addr & ~63
        buf = self.mem.setdefault(line, bytearray(64))
        step = self.dw // 8
        from CocoTBFramework.components.chi import data_window_lo
        for did, (data_int, be, _resp) in sorted(e.data_chunks.items()):
            off = data_window_lo(line, did, self.dw) - line
            chunk = data_int.to_bytes(step, 'little')
            for i in range(step):
                if (be >> i) & 1:
                    buf[off + i] = chunk[i]
        if bytes(buf) != self.ref.get(line):
            self.errors.append(f"write of {e.addr:#x} TxnID {e.txnid:#x}: memory differs from what the requester wrote")
        else:
            self.counts['writes_ok'] += 1
            self.counts['write_data_flits'] += len(e.data_chunks)
        if getattr(e, 'sep_write', False):
            self.fub_tx['rsp'].put(CHIRspFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid,
                                              opcode=int(RspOpcode.Comp), dbid=e.dbid).pack())
        self._maybe_retire(e)

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self.watch_writes_done())

    async def watch_writes_done(self):
        """A write is in progress until the requester BFM has completed it (data and
        every response sent back): TXSACTIVE may fall only then (B14.7.2)."""
        seen = 0
        while True:
            await self.wait_cycles(1)
            n = sum(1 for t in self.rn.completed if t.opcode == ReqOpcode.WriteNoSnpFull)
            if n != seen:
                self.outstanding -= n - seen
                seen = n
                self.set_sactive()

    # ---- traffic ----------------------------------------------------------------------------------------
    def idle_now(self):
        return (self.rn.tracker.outstanding == 0 and self.tracker.outstanding == 0 and not self.snoops_open
                and all(f.idle for f in self.fub_tx.values()) and not self.rn.have_work())

    async def wait_idle(self, what, extra=40):
        ok = await self.wait_until(self.idle_now, 80000, what)
        await self.wait_cycles(extra)
        return ok

    async def traffic(self, ops, order=0):
        ok = True
        for i in range(0, len(ops), self.window):
            txns = []
            for kind, eca in ops[i:i + self.window]:
                if kind == 'w':
                    a, data = self.alloc_line(), bytes(self.rng.getrandbits(8) for _ in range(64))
                    self.ref[a] = data
                    t = self.rn.new_txn(ReqOpcode.WriteNoSnpFull, a, Size.B64, data=data, expcompack=eca)
                else:
                    a = self.new_seeded_line()
                    t = self.rn.new_txn(ReqOpcode.ReadNoSnp, a, Size.B64, expcompack=eca, order=order)
                txns.append((kind, a, self.rn.issue(t)))
            ok = await self.finish(txns, 'monlite traffic') and ok
            ok = await self.wait_idle('monlite chunk', extra=24) and ok      # past the monitor's retire slack
        return ok

    # ---- snoops ----------------------------------------------------------------------------------------------
    async def snoops_batch(self, k, data=False, hold_cycles=0):
        if hold_cycles:
            slow = FlexRandomizer({'ready_delay': ([(hold_cycles, hold_cycles)], [1])})
            self.fub_rx['rsp'].bfm.set_randomizer(slow)
            self.fub_rx['dat'].bfm.set_randomizer(slow)
        n0 = self.counts['snoops_ok']
        for _ in range(k):
            a = self.new_seeded_line()
            if data:
                self.rn.cache.set_state(a, 'UD', data=bytes(self.rng.getrandbits(8) for _ in range(64)))
            self.send_snoop(a)
        ok = await self.wait_until(lambda: self.counts['snoops_ok'] - n0 >= k and not self.snoops_open,
                                   6000 + 600 * k + 4 * hold_cycles * k, f"{k} snoop responses")
        if hold_cycles:
            self.fub_rx['rsp'].set_profile('fixed')
            self.fub_rx['dat'].set_profile('fixed')
        return await self.wait_idle('snoop batch') and ok

    async def phase_snoops(self):
        mark = len(self.model.events)
        k = min(3, self.max_snp)
        ok = await self.snoops_batch(k)
        ok = await self.snoops_batch(k, data=True) and ok
        ok = await self.snoops_batch(self.max_snp + 2, hold_cycles=150) and ok
        await self.drain()
        self.verify('snoops', mark)
        return ok

    def on_fub_rsp_snoop_note(self):
        pass

    # ---- hold / starve / block -------------------------------------------------------------------------------------
    async def starve_and_block(self, n):
        self.rn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                                 'drain_gap': ([(14, 20)], [1]), 'ack_delay': ([(0, 0)], [1])}))
        for r in self.rn.rx.values():
            r.credit.buffer_depth = 1
        ok = await self.traffic(self.starve_ops() + self.mix(n))
        self.rn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        for r in self.rn.rx.values():
            r.credit.buffer_depth = self.cfg.max_lcredit
        slow = FlexRandomizer({'ready_delay': ([(20, 30)], [1])})
        for ch in ('req', 'rsp', 'dat'):
            self.fub_rx[ch].bfm.set_randomizer(slow)
        ok = await self.traffic(self.mix(n // 2 + 2)) and ok
        for ch in ('req', 'rsp', 'dat'):
            self.fub_rx[ch].set_profile('fixed')
        return ok

    async def hold_completions(self):
        self.comp_delay = 260
        ok = await self.traffic(self.mix(min(4, self.max_txn), 0.5))
        self.comp_delay = 0
        ok = await self.snoops_batch(min(2, self.max_snp), hold_cycles=260) and ok
        self.rn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                               'drain_gap': ([(300, 300)], [1]), 'ack_delay': ([(0, 0)], [1])}))
        for r in self.rn.rx.values():
            r.credit.buffer_depth = 1
        ok = await self.traffic(self.starve_ops()) and ok
        self.rn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        for r in self.rn.rx.values():
            r.credit.buffer_depth = self.cfg.max_lcredit
        if self.link_ctrl:
            ok = await self.bring_down() and ok
            self.rn.set_randomizer(FlexRandomizer({'flit_gap': ([(0, 0)], [1]), 'lcrd_gap': ([(0, 0)], [1]),
                                                   'drain_gap': ([(0, 0)], [1]), 'ack_delay': ([(300, 300)], [1])}))
            ok = await self.traffic(self.mix(1)) and ok
            self.rn.set_randomizer(FlexRandomizer(LINK_PROFILES['fast']))
        return ok

    # ---- error stimulus -------------------------------------------------------------------------------------------------
    def rsp_to_rn(self, op, txnid, **kw):
        return CHIRspFlit(self.cfg, tgtid=RN_ID, srcid=HN_ID, txnid=txnid, opcode=int(op), **kw)

    async def inject_orphans(self):
        """Toward the requester through the FUB (the TB is the completer);
        from the requester through the BFM's link."""
        rn, fx = self.rn, self.fub_tx
        self.outstanding += 1
        self.set_sactive()
        ids = [ORPH + i for i in range(10)]
        self.orphan_ids |= set(ids)
        be = _be_all(self.dw)
        pr = CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[8], opcode=int(ReqOpcode.PCrdReturn),
                        allowretry=0, pcrdtype=2, size=int(Size.B1))
        steps = [
            lambda: fx['rsp'].put(self.rsp_to_rn(RspOpcode.Comp, ids[0]).pack()),
            lambda: fx['rsp'].put(self.rsp_to_rn(RspOpcode.RetryAck, ids[1], pcrdtype=3).pack()),
            lambda: fx['dat'].put(CHIDatFlit(self.cfg, tgtid=RN_ID, srcid=HN_ID, txnid=ids[2],
                                             opcode=int(DatOpcode.CompData), dataid=0, homenid=HN_ID,
                                             be=be).pack()),
            lambda: fx['dat'].put(CHIDatFlit(self.cfg, tgtid=RN_ID, srcid=HN_ID, txnid=ids[3],
                                             opcode=int(DatOpcode.DataSepResp), dataid=0, homenid=HN_ID,
                                             be=be).pack()),
            lambda: rn.send('rsp', CHIRspFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[4],
                                              opcode=int(RspOpcode.CompAck))),
            lambda: rn.send('dat', CHIDatFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[5],
                                              opcode=int(DatOpcode.NonCopyBackWriteData), dataid=0, be=be)),
            lambda: rn.send('rsp', CHIRspFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[6],
                                              opcode=int(RspOpcode.SnpResp), resp=resp_encode('I'))),
            lambda: rn.send('dat', CHIDatFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[7],
                                              opcode=int(DatOpcode.SnpRespData), dataid=0,
                                              resp=resp_encode('I'), be=be)),
            lambda: fx['rsp'].put(self.rsp_to_rn(RspOpcode.ReadReceipt, ids[9]).pack()),
            lambda: rn.send('req', pr),
        ]
        for step in steps:
            step()
            await self.wait_cycles(12)
        await self.wait_cycles(20)
        self.outstanding -= 1
        self.set_sactive()
        return len(steps)

    async def phase_orphans(self):
        mark, snap = len(self.model.events), self.viol_snapshot(self.rn, self.mon)
        self.comp_delay = 150
        t = self.rn.new_txn(ReqOpcode.ReadNoSnp, self.new_seeded_line(), Size.B64, order=2)
        self.rn.issue(t)                       # an ordered read: the completer sends a ReadReceipt
        n = await self.inject_orphans()
        ok = await self.wait_idle('orphans')
        self.comp_delay = 0
        await self.drain()
        self.verify('orphans', mark)
        self.absorb(snap, expect_min=n - 3, what='orphans')
        return ok

    async def phase_table_full(self):
        mark = len(self.model.events)
        self.comp_delay = 150
        count = self.max_txn + 3
        txns = [('r', 0, self.rn.issue(self.rn.new_txn(ReqOpcode.ReadNoSnp, self.new_seeded_line(), Size.B64)))
                for _ in range(count)]
        for k, (_, a, t) in enumerate(txns):
            self.ref.setdefault(t.addr, bytes(self.mem[t.addr & ~63]))
        await self.wait_cycles(80)
        full = int(self.dut.active_count.value)
        if full != self.max_txn:
            self.mfail(f"table-full: active_count {full}, expected {self.max_txn} with {count} requests held")
        self.counts['active_full_checks'] += int(full == self.max_txn)
        ok = await self.finish([('r', t.addr, t) for _, _, t in txns], 'table full')
        self.comp_delay = 0
        await self.drain()
        self.verify('table-full', mark)
        return ok

    async def phase_resp_err(self):
        mark = len(self.model.events)
        self.resperr_dat = self.resperr_rsp = True
        w, self.window = self.window, 1
        ok = await self.traffic(self.mix(8, 0.5))
        self.window = w
        self.resperr_dat = self.resperr_rsp = False
        await self.drain()
        self.verify('resp-err', mark)
        return ok

    async def inject_error_and_channel(self):
        snap = self.viol_snapshot(self.rn, self.mon)
        self.outstanding += 1
        self.set_sactive()
        ids = [ORPH + 0x20, ORPH + 0x21]
        self.orphan_ids |= set(ids)
        self.fub_tx['rsp'].put(self.rsp_to_rn(RspOpcode.Comp, ids[0]).pack())
        self.rn.send('req', CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ids[1],
                                       opcode=int(ReqOpcode.PCrdReturn), allowretry=0, pcrdtype=1,
                                       size=int(Size.B1)))
        ok = await self.wait_idle('masked injection')
        self.outstanding -= 1
        self.set_sactive()
        self.absorb(snap, expect_min=1, what='mask injection')
        return ok

    async def protocol_overflow(self):
        mark, snap = len(self.model.events), self.viol_snapshot(self.rn, self.mon)
        n = min(int(os.environ.get('RX_FIFO_DEPTH', self.cfg.max_lcredit)), self.cfg.max_lcredit) + 1
        await self.traffic(self.mix(2))
        self.fub_rx['req'].bfm.set_randomizer(FlexRandomizer({'ready_delay': ([(14, 14)], [1])}))
        self.rn.tx['req'].credit.credits += 1               # the tamper: one credit the DUT never granted
        for i in range(n):
            self.rn.send('req', CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=ORPH + 0x40 + i,
                                           opcode=int(ReqOpcode.PCrdReturn), allowretry=0, pcrdtype=1,
                                           size=int(Size.B1)))
        await self.wait_cycles(20 * n + 300)
        self.fub_rx['req'].set_profile('fixed')
        await self.drain()
        self.counts['protocol_error_pin'] += int(self.dut.protocol_error.value)
        self.verify('protocol', mark, idle=False)
        self.absorb(snap, expect_min=1, what='protocol')
        fub = len(self.fub_rx['req'].words)
        self.expected_end_errors = [(r'DUT protocol_error set', True),
                                    (rf'req fub: {fub} flits, expected {fub + 1}', False)]
        return True

    async def phase_protocol(self):
        """Error/PROTOCOL: the port's sticky protocol_error. Fault injection
        on the BFM's credit state: it is handed one L-Credit more than the DUT
        granted and sends one flit too many on a channel whose FUB side is slow,
        so the DUT sees a flit with no credit outstanding. Last: the flag is
        sticky until reset."""
        return await self.protocol_overflow()
