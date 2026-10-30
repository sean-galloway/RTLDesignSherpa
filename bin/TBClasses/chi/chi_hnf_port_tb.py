# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_hnf_port_tb
# Purpose: Testbench for chi_hnf_port: GAXI BFMs on the FUB side, the RDS-DV
#          CHI requester BFM on the link, and a CHI monitor checking the wires
#
# Documentation: docs/markdown/rtl-amba/chi/chi_hnf_port.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-29
"""
The mirror of chi_rnf_port_tb. The DUT is the link layer of an HN-F; the
testbench plays a minimal home above it, at flit level on the FUB side:

* pops REQ flits from fub_rxreq (``CompleterTracker`` accepts them);
* ReadNoSnp: CompData flits on fub_txdat, chunked per DataID, from a TB memory;
* WriteNoSnpFull: CompDBIDResp on fub_txrsp with a DBID, then collects
  NonCopyBackWriteData from fub_rxdat by (SrcID, TxnID = DBID), writes the
  memory and checks it against what the requester was told to write;
* sends a SnpShared on fub_txsnp and expects SnpResp_I back on fub_rxrsp;
* drives fub_sactive while any request or snoop is open.

The partner is a ``CHIRequestNode`` (``create_chi_requester`` on ``s_chi_``)
that checks its own completions: every read must return what the TB memory
holds, and a ``CHIMonitor`` on the same pins judges the DUT as a third party.
Phases and their claims are those of chi_rnf_port_tb, with the credit
pools evidenced by ``rx<ch>_outstanding`` and the requester's credit stats.
"""

import os
import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.chi import (
    CHIDatFlit, CHIReqFlit, CHIRspFlit, CHISnpFlit, CompleterTracker, DatOpcode, ReqOpcode,
    RspOpcode, Size, SnpOpcode, create_chi_monitor, create_chi_requester, data_window_lo, data_windows,
    resp_encode)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.chi.chi_tb_common import HN_ID, LINK_PROFILES, RN_ID, CHITBBase

DAT_OPT = ('rsvdc', 'mecid', 'datacheck', 'poison')
SNP_OPT = ('mpam', 'mecid')
RSP_I = resp_encode('I')
RSP_UC = resp_encode('UC')


class CHIHnfPortTB(CHITBBase):
    PFX = 's_chi_'
    TX_CHANNELS = ('rsp', 'dat', 'snp')
    RX_CHANNELS = ('req', 'rsp', 'dat')

    def __init__(self, dut):
        super().__init__(dut)
        cfg = self.cfg_hn
        self.cfg = cfg
        for ch in self.TX_CHANNELS:
            self.add_fub_tx(ch)
        handlers = {'req': self.on_fub_req, 'rsp': self.on_fub_rsp, 'dat': self.on_fub_dat}
        for ch in self.RX_CHANNELS:
            self.add_fub_rx(ch, handlers[ch])
        # The BFM always drives the DUT's rx* pins and samples its tx*: the
        # partner of an HN-F port is a requester (RN-F node) at node id RN_ID.
        self.rn = create_chi_requester(
            dut, 'RN', 's_chi_', self.clk, self.cfg_rn, node_id=RN_ID, home_id=HN_ID,
            reset=self.rst_n, seed=self.seed, randomizer=FlexRandomizer(LINK_PROFILES['fast']),
            rx_buffer_depth=cfg.max_lcredit, log=self.log)
        # same node as the BFM beside it (see chi_rnf_port_tb): an RN-F monitor
        # Table B14.2: a receiver may still grant "when first entering"
        # DEACTIVATE; this DUT reacts after its LINKACTIVEREQ synchronizer
        # (LINKACTIVE_SYNC_STAGES flops) plus the registered LCRDV, so that
        # many late grants are legal and the monitor is told so.
        grace = int(os.environ.get('LINKACTIVE_SYNC_STAGES', '2')) + 1
        self.mon = create_chi_monitor(dut, 'Mon', 's_chi_', self.clk, self.cfg_rn, reset=self.rst_n,
                                      log=self.log, deactivate_credit_grace=grace)
        self.partner = self.rn
        self.tracker = CompleterTracker(data_width=self.dw)
        self.ref = {}               # line -> bytes the line must hold (seeded or written)
        self.mem = {}               # the TB home's memory: line -> bytearray
        self.next_line = 0
        self.reqs_seen = 0
        self.dbid_of = {}
        self.snoops_open = {}       # snoop TxnID -> address
        self.snoop_txnid = 0
        self.snoops_ok_list = []
        self.read_delay = (0, 0)

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self.watch_reads())

    # ---- addresses and memory ---------------------------------------------------
    def alloc_line(self):
        addr = self.next_line * 64
        self.next_line += 1
        return addr

    def new_seeded_line(self):
        addr = self.alloc_line()
        data = bytes(self.rng.getrandbits(8) for _ in range(64))
        self.mem[addr] = bytearray(data)
        self.ref[addr] = data
        return addr

    # ---- Protocol layer: FUB RX handlers ----------------------------------------------------
    def on_fub_req(self, word):
        f = CHIReqFlit.from_word(self.cfg, word)
        self.counts['rx_req'] += 1
        self.reqs_seen += 1
        self.outstanding += 1
        self.set_sactive()
        try:
            e = self.tracker.accept(f)
        except ValueError as err:
            self.errors.append(f"REQ {f.opcode_name}: {err}")
            return
        if f.opcode == int(ReqOpcode.ReadNoSnp):
            cocotb.start_soon(self.serve_read(e))
        elif f.opcode == int(ReqOpcode.WriteNoSnpFull):
            dbid = self.tracker.allocate_dbid(e)
            r = CHIRspFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid,
                           opcode=int(RspOpcode.CompDBIDResp), dbid=dbid)
            self.fub_tx['rsp'].put(r.pack())
        else:
            self.errors.append(f"unexpected REQ opcode {f.opcode_name}")

    async def serve_read(self, e):
        lo, hi = self.read_delay
        for _ in range(self.rng.randint(lo, hi)):
            await RisingEdge(self.clk)
        line = line_of(e.addr)
        data = bytes(self.mem[line])
        for did, wlo in data_windows(e.addr, e.nbytes, self.dw):
            f = CHIDatFlit(self.cfg, tgtid=e.srcid, srcid=HN_ID, txnid=e.txnid,
                           opcode=int(DatOpcode.CompData), resp=RSP_UC, dataid=did, homenid=HN_ID,
                           ccid=(e.addr >> 4) & 3, be=(1 << (self.dw // 8)) - 1)
            f.set_data_bytes(data[wlo - line: wlo - line + self.dw // 8])
            self.random_optional(f, 'dat', DAT_OPT)
            self.fub_tx['dat'].put(f.pack())
            self.counts['comp_data_flits'] += 1
        self.tracker.retire(e)

    def on_fub_dat(self, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        self.counts['rx_dat'] += 1
        try:
            e = self.tracker.on_write_data(f)
        except (LookupError, ValueError) as err:
            self.errors.append(f"DAT {f.opcode_name} TxnID {f.txnid:#x}: {err}")
            return
        if not e.write_complete:
            return
        line = line_of(e.addr)
        buf = self.mem.setdefault(line, bytearray(64))
        step = self.dw // 8
        for did, (data_int, be, _resp) in sorted(e.data_chunks.items()):
            off = data_window_lo(line, did, self.dw) - line
            chunk = data_int.to_bytes(step, 'little')
            for i in range(step):
                if (be >> i) & 1:
                    buf[off + i] = chunk[i]
        if bytes(buf) != self.ref.get(line):
            self.errors.append(f"write of {e.addr:#x} TxnID {e.txnid:#x}: memory ends up "
                               f"{bytes(buf).hex()}, requester wrote {self.ref.get(line, b'').hex()}")
        else:
            self.counts['writes_ok'] += 1
            self.counts['write_data_flits'] += len(e.data_chunks)
        self.tracker.retire(e)
        self.outstanding -= 1
        self.set_sactive()

    def on_fub_rsp(self, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        self.counts['rx_rsp'] += 1
        if f.opcode != int(RspOpcode.SnpResp):
            self.errors.append(f"unexpected RSP {f.opcode_name}")
            return
        addr = self.snoops_open.pop(f.txnid, None)
        if addr is None or f.srcid != RN_ID or f.tgtid != HN_ID or f.resp != RSP_I:
            self.errors.append(f"SnpResp TxnID {f.txnid:#x}: open={addr} src={f.srcid} tgt={f.tgtid} "
                               f"resp={f.resp}")
            return
        self.counts['snoops_ok'] += 1
        self.outstanding -= 1
        self.set_sactive()

    async def watch_reads(self):
        """Retire a read when the requester BFM has all its data (the DUT's
        TX side has then drained, so TXSACTIVE may fall)."""
        seen = 0
        while True:
            await RisingEdge(self.clk)
            n = sum(1 for t in self.rn.completed if t.opcode == ReqOpcode.ReadNoSnp)
            if n != seen:
                self.outstanding -= n - seen
                seen = n
                self.set_sactive()

    # ---- snoops ----------------------------------------------------------------------------------
    def send_snoop(self, addr):
        self.snoop_txnid += 1
        txnid = self.snoop_txnid
        f = CHISnpFlit(self.cfg, srcid=HN_ID, txnid=txnid, opcode=int(SnpOpcode.SnpShared),
                       addr=addr >> 3)
        self.random_optional(f, 'snp', SNP_OPT)
        self.snoops_open[txnid] = addr
        self.outstanding += 1
        self.set_sactive()
        self.fub_tx['snp'].put(f.pack())
        self.counts['snoops_sent'] += 1

    async def run_snoops(self, k):
        n0 = self.counts['snoops_ok']
        for _ in range(k):
            self.send_snoop(self.new_seeded_line())
        ok = await self.wait_until(lambda: self.counts['snoops_ok'] - n0 >= k and not self.snoops_open,
                                   4000 + 400 * k, f"{k} SnpResp on fub_rxrsp")
        self.counts['rn_snoops_seen'] = self.rn.snoops_seen
        return ok

    # ---- traffic ---------------------------------------------------------------------------------------
    def quiet(self):
        return (self.outstanding == 0 and not self.snoops_open
                and all(f.idle for f in self.fub_tx.values()))

    async def wait_quiet(self, what, ops):
        return await self.wait_until(self.quiet, 800 * ops + 6000, what)

    async def run_phase(self, name, n, link='fast', fub='fixed', fub_rx='fixed', depth=None, snoops=0,
                        read_delay=(0, 0)):
        self.phase = name
        self.rn.set_randomizer(FlexRandomizer(LINK_PROFILES[link]))
        for r in self.rn.rx.values():
            r.credit.buffer_depth = depth or self.cfg.max_lcredit
        self.set_fub_profiles(fub, fub_rx)
        self.read_delay = read_delay
        starved0 = sum(self.starved.values())
        n_w = n // 2
        wr = [self.alloc_line() for _ in range(n_w)]
        rd = [self.new_seeded_line() for _ in range(n - n_w)]
        ops = [('w', a) for a in wr] + [('r', a) for a in rd]
        self.rng.shuffle(ops)
        txns = []
        for kind, a in ops:
            if kind == 'w':
                data = bytes(self.rng.getrandbits(8) for _ in range(64))
                self.ref[a] = data
                t = self.rn.new_txn(ReqOpcode.WriteNoSnpFull, a, Size.B64, data=data)
            else:
                t = self.rn.new_txn(ReqOpcode.ReadNoSnp, a, Size.B64)
            txns.append((kind, a, self.rn.issue(t)))
        for _ in range(snoops):
            self.send_snoop(self.new_seeded_line())
        ok = await self.finish(txns, name)
        txns = [('r', a, self.rn.issue(self.rn.new_txn(ReqOpcode.ReadNoSnp, a, Size.B64))) for a in wr]
        ok = ok and await self.finish(txns, f"{name} read-back")
        ok = ok and await self.wait_until(lambda: not self.snoops_open, 4000, f"{name}: snoop responses")
        self.log.info(f"phase {name}: {n} ops + {len(wr)} read-backs {'ok' if ok else 'FAILED'} "
                      f"starved={sum(self.starved.values()) - starved0} "
                      f"peak_credits={self.mon.max_credits}")
        return ok

    async def finish(self, txns, what):
        ok = True
        for kind, a, t in txns:
            try:
                await self.rn.wait(t, timeout_cycles=60000)
            except TimeoutError as e:
                self.errors.append(f"{what}: {e}")
                return False
            if kind == 'r':
                if t.read_data() != self.ref[a]:
                    self.errors.append(f"{what}: read of {a:#x} TxnID {t.txnid:#x} returned "
                                       f"{(t.read_data() or b'').hex()}, TB memory holds {self.ref[a].hex()}")
                    ok = False
                else:
                    self.counts['reads_ok'] += 1
                    self.counts['read_data_flits'] += len(t.data_chunks)
        ok = ok and await self.wait_quiet(what, len(txns))
        return ok

    async def run_starve(self, n):
        depth = min(3, self.cfg.max_lcredit)
        blocked = lambda: sum(r.stats['grant_blocked'] for r in self.rn.rx.values())
        b0 = blocked()
        ok = await self.run_phase('starve', n, link='starve', depth=depth)
        self.counts['starve_grant_blocked'] += blocked() - b0
        self.counts['starve_cycles'] += self.starved['starve']
        return ok

    # ---- pool fill -----------------------------------------------------------------------------------------
    async def run_pool_fill(self):
        """Link up, nothing to send: each TX channel holds exactly the
        requester's pool, each RX channel has granted its FIFO's worth."""
        self.phase = 'pool'
        cfg = self.cfg
        for r in self.rn.rx.values():
            r.credit.buffer_depth = cfg.max_lcredit
        pool_tx = cfg.max_lcredit
        pool_rx = min(self.p['RX_FIFO_DEPTH'], cfg.max_lcredit)
        await self.wait_cycles(8 * cfg.max_lcredit + 60)
        ok = True
        # the monitor is an RN-F: its rx<ch> are the DUT's TX, its tx<ch> the DUT's RX
        for ch in self.TX_CHANNELS:
            dut_c = self.pin(f'tx{ch}_credits')
            rn_c = self.rn.rx[ch].credit.outstanding
            mon_c = self.mon.checker.credits[f'rx{ch}']
            mon_pk = self.mon.max_credits[f'rx{ch}']
            self.log.info(f"pool tx{ch}: DUT {dut_c} requester {rn_c} monitor {mon_c} peak {mon_pk} want {pool_tx}")
            if not (dut_c == rn_c == mon_c == pool_tx == mon_pk):
                self.errors.append(f"pool tx{ch}: DUT {dut_c} / requester {rn_c} / monitor {mon_c} / "
                                   f"monitor peak {mon_pk}, expected {pool_tx}")
                ok = False
            self.counts['pool_tx_checks'] += 1
        for ch in self.RX_CHANNELS:
            dut_o = self.pin(f'rx{ch}_outstanding')
            rn_c = self.rn.tx[ch].credit.held
            mon_c = self.mon.checker.credits[f'tx{ch}']
            self.log.info(f"pool rx{ch}: DUT outstanding {dut_o} requester holds {rn_c} monitor {mon_c} want {pool_rx}")
            if not (dut_o == rn_c == mon_c == pool_rx):
                self.errors.append(f"pool rx{ch}: DUT {dut_o} / requester {rn_c} / monitor {mon_c}, "
                                   f"expected {pool_rx}")
                ok = False
            self.counts['pool_rx_checks'] += 1
        return ok

    # ---- link phases ----------------------------------------------------------------------------------------------
    async def run_snoop_wake(self, k):
        """A snoop is queued at a stopped link: the DUT raises LINKACTIVEREQ."""
        ok = await self.bring_down()
        act0 = self.mon.stats['activations'] + self.mon.stats['deactivations']
        req0 = self.link_pin('rxlinkactivereq')
        ok = ok and await self.run_snoops(k)
        self.check(self.mon.stats['activations'] + self.mon.stats['deactivations'] > act0 or req0,
                   "snoop at a stopped link raised no LINKACTIVEREQ")
        self.counts['snoop_wakeups'] += 1
        return ok

    async def run_churn(self, n):
        self.phase = 'churn'
        self.dut.cfg_idle_cycles.value = 3
        d0 = self.mon.stats['deactivations']
        ok = await self.run_phase('churn', n, link='gappy', fub='slow_producer', read_delay=(8, 20))
        self.dut.cfg_idle_cycles.value = 0
        bounced = self.mon.stats['deactivations'] + self.mon.stats['activations'] - d0
        # the DUT's own TXLINKACTIVEREQ is the monitor's rx direction
        self.check(bounced > 0, "churn: no link bounce under a 3-cycle idle timeout")
        self.counts['churn_bounces'] += bounced
        return ok

    # ---- verdict ----------------------------------------------------------------------------------------------------
    def link_words_of(self, ch, srcid):
        return [f.pack() for f in self.mon._recvQ if f.channel == ch and int(f.srcid) == srcid]

    def check_end(self):
        for ch in self.TX_CHANNELS:
            self.compare_words(self.fub_tx[ch].offered, self.link_words_of(ch, HN_ID), f'{ch} link')
        for ch in self.RX_CHANNELS:
            self.compare_words(self.link_words_of(ch, RN_ID), self.fub_rx[ch].words, f'{ch} fub')
        self.check_violations(self.rn, self.mon)
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

    def required_counts(self):
        req = ['reads_ok', 'writes_ok', 'read_data_flits', 'write_data_flits', 'comp_data_flits',
               'snoops_ok', 'snoops_sent', 'rn_snoops_seen', 'starve_cycles', 'starve_grant_blocked',
               'pool_tx_checks', 'pool_rx_checks', 'sactive_high_checks', 'sactive_low_checks',
               'mon_flits', 'exact_rsp', 'exact_dat', 'exact_snp', 'exact_req', 'protocol_error_checks',
               'rxsactive_checks']
        if self.link_ctrl:
            req += ['idle_deactivations', 'credits_returned', 'remote_activations', 'snoop_wakeups',
                    'hold_cycles', 'churn_bounces', 'activations', 'lcrd_returns_seen']
        else:
            req += ['tied_checks']
        return req


def line_of(addr):
    return addr & ~63
