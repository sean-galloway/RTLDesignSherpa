# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_rnf_port_tb
# Purpose: Testbench for chi_rnf_port: GAXI BFMs on the FUB side, the RDS-DV
#          CHI home BFM on the link, and a CHI monitor checking the wires
#
# Documentation: docs/markdown/rtl-amba/chi/chi_rnf_port.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-29
"""
The DUT is the link layer of an RN-F. The testbench plays the minimal Protocol
layer above it, at flit level on the FUB side:

* issues ReadNoSnp (64 B) and WriteNoSnpFull requests on fub_txreq with unique
  TxnIDs (``RequesterTracker`` allocates them and decides what each response
  owes);
* reassembles CompData from fub_rxdat by DataID and checks every read against
  a reference memory the TB keeps;
* on CompDBIDResp sends NonCopyBackWriteData on fub_txdat with TxnID = DBID,
  chunked per DataID (``CHITransaction.write_chunks``);
* answers a home snoop (SnpShared from fub_rxsnp) with SnpResp_I on fub_txrsp;
* drives fub_sactive while any transaction is in progress.

The partner is a ``CHIHomeNode`` (``create_chi_home`` on ``m_chi_``) serving
from its own memory, and a ``CHIMonitor`` on the same pins is a third party
that judges the DUT, not the BFM driving it.

Phases, each with its own claim:
  fast       credits come straight back: the link streams
  starve     the home's receive pool is 3 and it drains slowly, so credits run
             out: the DUT must stall with flits queued, never send without one
  gappy      sparse LCRDV, slow LINKACTIVE ACK, snoops mixed into the traffic
  b2b        back-to-back FUB offering
  pool       link up and idle: every credit pool equals the partner's
  idle       (LINK_CTRL) idle cycles take the link to STOP, every credit returned
  snoop      (LINK_CTRL) a snoop arrives at a stopped link and wakes it
  remote     (LINK_CTRL) the home activates its own TX link; the DUT must bring
             its TX link up too (B14.6)
  churn      (LINK_CTRL) a short idle timeout bounces the link under traffic
With LINK_CTRL=0 none of the link phases run; the link pins must stay tied low.
"""

import os
import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.chi import (
    CHIDatFlit, CHIReqFlit, CHIRspFlit, CHISnpFlit, CHITransaction, DatOpcode, HomeOptions, MemAttr,
    ReqOpcode, RequesterTracker, RspOpcode, Size, SnpOpcode, create_chi_home, create_chi_monitor,
    line_addr, resp_encode)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.chi.chi_tb_common import (HN_ID, LINK_PROFILES, RN_ID, ST_RUN, ST_STOP, CHITBBase)

REQ_OPT = ('rsvdc', 'mpam', 'pbha', 'mecid', 'secsid1')
DAT_OPT = ('rsvdc', 'mecid', 'datacheck', 'poison')
NUM_LINES = 8192


class CHIRnfPortTB(CHITBBase):
    PFX = 'm_chi_'
    TX_CHANNELS = ('req', 'rsp', 'dat')
    RX_CHANNELS = ('rsp', 'dat', 'snp')

    def __init__(self, dut):
        super().__init__(dut)
        cfg = self.cfg_rn
        self.cfg = cfg
        for ch in self.TX_CHANNELS:
            self.add_fub_tx(ch)
        handlers = {'rsp': self.on_fub_rsp, 'dat': self.on_fub_dat, 'snp': self.on_fub_snp}
        for ch in self.RX_CHANNELS:
            self.add_fub_rx(ch, handlers[ch])
        # The BFM always drives the DUT's rx* pins and samples its tx*: the
        # partner of an RN-F port is a home (HN-F node), rn_id is the node id
        # this TB issues its requests under.
        self.hn = create_chi_home(
            dut, 'HN', 'm_chi_', self.clk, self.cfg_hn, rn_id=RN_ID, node_id=HN_ID,
            reset=self.rst_n, options=HomeOptions(), num_lines=NUM_LINES, seed=self.seed,
            randomizer=FlexRandomizer(LINK_PROFILES['fast']), rx_buffer_depth=cfg.max_lcredit,
            log=self.log)
        # Table B14.2: a receiver may still grant "when first entering"
        # DEACTIVATE; this DUT reacts after its LINKACTIVEREQ synchronizer
        # (LINKACTIVE_SYNC_STAGES flops) plus the registered LCRDV, so that
        # many late grants are legal and the monitor is told so.
        grace = int(os.environ.get('LINKACTIVE_SYNC_STAGES', '2')) + 1
        self.mon = create_chi_monitor(dut, 'Mon', 'm_chi_', self.clk, self.cfg_hn, reset=self.rst_n,
                                      log=self.log, deactivate_credit_grace=grace)
        # The monitor binds like a BFM does: it plays the node ACROSS from the
        # DUT (an HN-F against this RN-F port) and swaps tx/rx, so the DUT's TX
        # channels are the monitor's rx<ch> keys and vice versa.
        self.partner = self.hn
        self.tracker = RequesterTracker(RN_ID)
        self.ref = {}               # line address -> the 64 bytes the home must hold
        self.expect = {}            # id(txn) -> (kind, addr, expected bytes)
        self.next_line = 0
        self.issued = 0
        self.snp_seen = {}          # snoop TxnID -> (opcode, byte address, srcid)
        self.snoop_done = []

    # ---- addresses and reference memory ---------------------------------------
    def alloc_line(self):
        addr = self.next_line * 64
        self.next_line += 1
        assert self.next_line < NUM_LINES, "home memory exhausted"
        return addr

    def new_seeded_line(self):
        """A line the home already holds, never written during the run."""
        addr = self.alloc_line()
        data = bytes(self.rng.getrandbits(8) for _ in range(64))
        self.hn.home.memory.write(addr, bytearray(data))
        self.ref[addr] = data
        return addr

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self.watch_writes())

    # ---- Protocol layer: issue ---------------------------------------------------------
    def issue(self, kind, addr, data=None):
        if kind == 'r':
            txn = CHITransaction(opcode=ReqOpcode.ReadNoSnp, addr=addr, size=Size.B64, srcid=RN_ID,
                                 tgtid=HN_ID, memattr=int(MemAttr.EWA), snpattr=0, expcompack=0)
            self.expect[id(txn)] = ('r', addr, self.ref[addr])
        else:
            txn = CHITransaction(opcode=ReqOpcode.WriteNoSnpFull, addr=addr, size=Size.B64, srcid=RN_ID,
                                 tgtid=HN_ID, memattr=int(MemAttr.EWA), snpattr=0, expcompack=0,
                                 data=data)
            self.ref[addr] = data
            self.expect[id(txn)] = ('w', addr, data)
        self.tracker.issue(txn)
        f = CHIReqFlit(self.cfg, tgtid=HN_ID, srcid=RN_ID, txnid=txn.txnid, opcode=int(txn.opcode),
                       size=int(txn.size), addr=addr, allowretry=txn.allowretry, memattr=txn.memattr,
                       snpattr=0, expcompack=0)
        self.random_optional(f, 'req', REQ_OPT)
        self.outstanding += 1
        self.issued += 1
        self.set_sactive()
        self.fub_tx['req'].put(f.pack())
        return txn

    def _complete(self, txn):
        kind, addr, exp = self.expect.pop(id(txn))
        if kind == 'r':
            got = txn.read_data()
            if got != exp:
                self.errors.append(f"read of {addr:#x} TxnID {txn.txnid:#x}: data differs from the "
                                   f"reference memory ({None if got is None else got.hex()} vs {exp.hex()})")
            else:
                self.counts['reads_ok'] += 1
                self.counts['read_data_flits'] += len(txn.data_chunks)
        else:
            # The write is in progress until its data has left the DUT (the
            # home has applied it): watch_writes retires it, not this.
            self.counts['writes_done'] += 1
            return
        self.outstanding -= 1
        self.set_sactive()

    async def watch_writes(self):
        """Retire a write when the home has served it: every flit of it is
        on the link, so TXSACTIVE may fall (B14.7.2)."""
        seen = 0
        while True:
            await RisingEdge(self.clk)
            n = sum(1 for e in self.hn.served if e.opcode == ReqOpcode.WriteNoSnpFull)
            if n != seen:
                self.outstanding -= n - seen
                seen = n
                self.set_sactive()

    def _act(self, txn, actions, what):
        for a in actions:
            if a.kind == 'send_write_data':
                for did, data_int, be in txn.write_chunks(self.dw):
                    f = CHIDatFlit(self.cfg, tgtid=a.tgtid, srcid=RN_ID, txnid=a.txnid,
                                   opcode=int(a.opcode), dataid=did, be=be, ccid=(txn.addr >> 4) & 3)
                    f.fields['data'] = data_int
                    self.random_optional(f, 'dat', DAT_OPT)
                    self.fub_tx['dat'].put(f.pack())
                    self.counts['write_data_flits'] += 1
            elif a.kind == 'done':
                self._complete(txn)
            else:
                self.errors.append(f"{what}: unexpected {a.kind} {getattr(a, 'text', '')}")

    # ---- Protocol layer: the FUB RX handlers -------------------------------------------------
    def on_fub_rsp(self, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        self.counts['rx_rsp'] += 1
        try:
            txn, actions = self.tracker.route_rsp(f)
        except ValueError as e:
            self.errors.append(f"RSP {f.opcode_name}: {e}")
            return
        self._act(txn, actions, f"RSP {f.opcode_name} TxnID {f.txnid:#x}")

    def on_fub_dat(self, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        self.counts['rx_dat'] += 1
        try:
            txn, actions = self.tracker.route_dat(f)
        except ValueError as e:
            self.errors.append(f"DAT {f.opcode_name}: {e}")
            return
        self._act(txn, actions, f"DAT {f.opcode_name} TxnID {f.txnid:#x}")

    def on_fub_snp(self, word):
        """The RN holds no lines, so every snoop is answered SnpResp_I."""
        f = CHISnpFlit.from_word(self.cfg, word)
        self.counts['rx_snp'] += 1
        self.snp_seen[f.txnid] = (f.opcode, f.byte_addr, f.srcid)
        self.outstanding += 1
        self.set_sactive()
        r = CHIRspFlit(self.cfg, tgtid=f.srcid, srcid=RN_ID, txnid=f.txnid,
                       opcode=int(RspOpcode.SnpResp), resp=resp_encode('I'))
        self.fub_tx['rsp'].put(r.pack())
        self.counts['snp_resp_sent'] += 1

    # ---- traffic ---------------------------------------------------------------------------------
    def quiet(self):
        return (self.outstanding == 0 and len(self.hn.served) >= self.issued
                and all(f.idle for f in self.fub_tx.values()))

    async def wait_quiet(self, ops, what):
        return await self.wait_until(self.quiet, 800 * ops + 6000, what)

    async def snoop_one(self, addr):
        s = await self.hn.home.snoop(RN_ID, SnpOpcode.SnpShared, addr)
        self.outstanding -= 1
        self.set_sactive()
        self.snoop_done.append((s, addr))

    def check_snoops(self):
        """Each completed snoop reached fub_rxsnp as the right flit and came
        back as SnpResp_I carrying the snoop's TxnID."""
        for s, addr in self.snoop_done:
            seen = self.snp_seen.get(s.txnid)
            ok = (seen is not None and seen[0] == int(SnpOpcode.SnpShared)
                  and seen[1] == line_addr(addr) and s.resp_state == 'I')
            if not ok:
                self.errors.append(f"snoop TxnID {s.txnid:#x} {addr:#x}: seen={seen} resp={s.resp_state}")
            else:
                self.counts['snoops_ok'] += 1
        self.snoop_done.clear()

    async def run_snoops(self, k):
        tasks = [cocotb.start_soon(self.snoop_one(self.new_seeded_line())) for _ in range(k)]
        for t in tasks:
            await t
        self.check_snoops()
        return True

    async def run_phase(self, name, n, link='fast', fub='fixed', fub_rx='fixed', depth=None, snoops=0):
        self.phase = name
        self.hn.set_randomizer(FlexRandomizer(LINK_PROFILES[link]))
        for r in self.hn.rx.values():
            r.credit.buffer_depth = depth or self.cfg.max_lcredit
        self.set_fub_profiles(fub, fub_rx)
        starved0 = sum(self.starved.values())
        n_w = n // 2
        wr = [self.alloc_line() for _ in range(n_w)]
        rd = [self.new_seeded_line() for _ in range(n - n_w)]
        ops = [('w', a) for a in wr] + [('r', a) for a in rd]
        self.rng.shuffle(ops)
        tasks = [cocotb.start_soon(self.snoop_one(self.new_seeded_line())) for _ in range(snoops)]
        for kind, a in ops:
            self.issue(kind, a, bytes(self.rng.getrandbits(8) for _ in range(64)) if kind == 'w' else None)
        ok = await self.wait_quiet(len(ops), f"{name}: stage A")
        # stage B: read back everything stage A wrote
        for a in wr:
            self.issue('r', a)
        ok = ok and await self.wait_quiet(len(wr), f"{name}: stage B read-back")
        for t in tasks:
            await t
        self.check_snoops()
        for a in wr:
            held = bytes(self.hn.home.read_line(a))
            if not self.check(held == self.ref[a], f"{name}: home memory at {a:#x} differs from the "
                                                   f"data the DUT carried"):
                break
            self.counts['mem_lines_ok'] += 1
        self.log.info(f"phase {name}: {n} ops + {len(wr)} read-backs {'ok' if ok else 'FAILED'} "
                      f"starved={sum(self.starved.values()) - starved0} "
                      f"peak_credits={self.mon.max_credits}")
        return ok

    async def run_starve(self, n):
        depth = min(3, self.cfg.max_lcredit)
        before = self.hn.rx['req'].stats['grant_blocked'] + self.hn.rx['dat'].stats['grant_blocked']
        ok = await self.run_phase('starve', n, link='starve', depth=depth)
        blocked = (self.hn.rx['req'].stats['grant_blocked'] + self.hn.rx['dat'].stats['grant_blocked']
                   - before)
        self.counts['starve_grant_blocked'] += blocked
        self.counts['starve_cycles'] += self.starved['starve']
        return ok

    # ---- pool fill -------------------------------------------------------------------------------
    async def run_pool_fill(self):
        """Link up, nothing to send: each TX channel holds exactly the partner's
        pool, each RX channel has granted exactly its FIFO's worth."""
        self.phase = 'pool'
        cfg = self.cfg
        for r in self.hn.rx.values():
            r.credit.buffer_depth = cfg.max_lcredit
        pool_tx = cfg.max_lcredit
        pool_rx = min(self.p['RX_FIFO_DEPTH'], cfg.max_lcredit)
        await self.wait_cycles(8 * cfg.max_lcredit + 60)
        ok = True
        for ch in ('req', 'rsp', 'dat'):
            dut_c = self.pin(f'tx{ch}_credits')
            home_c = self.hn.rx[ch].credit.outstanding
            mon_c = self.mon.checker.credits[f'rx{ch}']
            mon_pk = self.mon.max_credits[f'rx{ch}']
            self.log.info(f"pool tx{ch}: DUT {dut_c} home {home_c} monitor {mon_c} peak {mon_pk} want {pool_tx}")
            if not (dut_c == home_c == mon_c == pool_tx == mon_pk):
                self.errors.append(f"pool tx{ch}: DUT {dut_c} / home {home_c} / monitor {mon_c} / "
                                   f"monitor peak {mon_pk}, expected {pool_tx}")
                ok = False
            self.counts['pool_tx_checks'] += 1
        for ch in ('rsp', 'dat', 'snp'):
            dut_o = self.pin(f'rx{ch}_outstanding')
            home_c = self.hn.tx[ch].credit.held
            mon_c = self.mon.checker.credits[f'tx{ch}']
            self.log.info(f"pool rx{ch}: DUT outstanding {dut_o} home holds {home_c} monitor {mon_c} want {pool_rx}")
            if not (dut_o == home_c == mon_c == pool_rx):
                self.errors.append(f"pool rx{ch}: DUT {dut_o} / home {home_c} / monitor {mon_c}, "
                                   f"expected {pool_rx}")
                ok = False
            self.counts['pool_rx_checks'] += 1
        return ok

    # ---- link phases (hold / idle / bring_down / remote: CHITBBase) -------------------
    async def run_snoop_wake(self, k):
        """A snoop arrives at a stopped link: the home activates, the DUT follows."""
        ok = await self.bring_down()
        act0 = self.mon.stats['activations']
        ok = ok and await self.run_snoops(k)
        self.check(self.mon.stats['activations'] > act0, "snoop at a stopped link raised no LINKACTIVEREQ")
        self.counts['snoop_wakeups'] += 1
        return ok

    async def run_churn(self, n):
        self.phase = 'churn'
        self.dut.cfg_idle_cycles.value = 3
        d0 = self.mon.stats['deactivations']
        ok = await self.run_phase('churn', n, link='gappy', fub='slow_producer')
        self.dut.cfg_idle_cycles.value = 0
        bounced = self.mon.stats['deactivations'] - d0
        self.check(bounced > 0, "churn: the link never went down under a 3-cycle idle timeout")
        self.counts['churn_bounces'] += bounced
        return ok

    # ---- verdict ------------------------------------------------------------------------------------------
    def check_end(self):
        self.compare_words(self.fub_tx['req'].offered, self.link_words('req', RN_ID), 'req link')
        for ch in ('rsp', 'dat'):
            self.compare_words(self.fub_tx[ch].offered, self.link_words(ch, RN_ID), f'{ch} link')
            self.compare_words(self.link_words(ch, HN_ID), self.fub_rx[ch].words, f'{ch} fub')
        self.compare_words(self.link_words('snp', HN_ID), self.fub_rx['snp'].words, 'snp fub')
        self.check_violations(self.hn, self.mon)
        if self.mon.total_violations():
            self.errors.append(f"monitor: {self.mon.all_violations()} first: "
                               f"{self.mon.checker.messages[:4]}")
        self.check(self.mon.unfinished() == [], f"monitor unfinished: {self.mon.unfinished()[:3]}")
        self.counts['mon_flits'] = self.mon.stats['flits']
        self.counts['lcrd_returns_seen'] = self.mon.stats['lcrd_returns']
        self.counts['activations'] = self.mon.stats['activations']
        self.check(self.pin('protocol_error') == 0, "DUT protocol_error set")
        self.counts['protocol_error_checks'] += 1
        return not self.errors

    def link_words(self, ch, srcid):
        return [f.pack() for f in self.mon._recvQ if f.channel == ch and int(f.srcid) == srcid]

    def required_counts(self):
        req = ['reads_ok', 'writes_done', 'read_data_flits', 'write_data_flits', 'mem_lines_ok',
               'snoops_ok', 'snp_resp_sent', 'starve_cycles', 'starve_grant_blocked', 'pool_tx_checks',
               'pool_rx_checks', 'sactive_high_checks', 'sactive_low_checks', 'mon_flits',
               'exact_req', 'exact_rsp', 'exact_dat', 'exact_snp', 'protocol_error_checks',
               'rxsactive_checks']
        if self.link_ctrl:
            req += ['idle_deactivations', 'credits_returned', 'remote_activations', 'snoop_wakeups',
                    'hold_cycles', 'churn_bounces', 'activations', 'lcrd_returns_seen']
        else:
            req += ['tied_checks']
        return req
