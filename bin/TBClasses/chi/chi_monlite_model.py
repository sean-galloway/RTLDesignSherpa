# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: chi_monlite_model
# Purpose: Spec-level reference model of the events chi_monitor_lite must emit
#
# Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-30
"""What chi_monitor_lite must say, derived from the FUB handshakes alone.

The model is fed the handshakes a testbench SAW on the port's six FUB
channels (by message direction, the monitor's own view: ``req``, ``cpl_rsp``,
``cpl_dat``, ``rq_rsp``, ``rq_dat``, ``snp``) and the link-state pins, and
answers with the packets the ocelus owes: one :class:`Ev` each. It is built
from the CHI rules (IHI 0050 B2.3, B2.4.3, B2.7.3, B2.10) through the
framework's flit classes and opcode tables, NOT from chi_pkg.sv, so a wrong
field offset or opcode in the RTL is a disagreement and not an echo.

Exact where the stimulus decides it: which events, their channel_id, the
opcode / TxnID / PCrdType / RespErr payload fields, the running counters.
Windowed where the RTL's retire arbitration decides it: latency (the event
stage is registered and one slot retires a cycle) and occupancy. Optional
where a boundary is a coin toss (an episode a cycle or two either side of its
threshold): ``Ev.optional``, and the test counts how many were optional.

The model refuses to guess about slot reuse: a request arriving within
RETIRE_SLACK cycles of a slot's last owed message while the table would be
full without that slot is counted in ``ambiguous``, and a test asserts it is
zero. Stimulus is designed around the boundary, not tuned to the RTL.
"""

from dataclasses import dataclass, field

from CocoTBFramework.components.chi import (
    REQ_CLASS,
    CHIDatFlit,
    CHIReqFlit,
    CHIRspFlit,
    CHISnpFlit,
    DatOpcode,
    ReqClass,
    ReqOpcode,
    RspOpcode,
)

from TBClasses.monbus import (
    CHIChannelCode,
    CHICompletionCode,
    CHICreditCode,
    CHIErrorCode,
    CHITimeoutCode,
    PktType,
)

PT_ERR, PT_TMO, PT_COMPL = int(PktType.PktTypeError), int(PktType.PktTypeTimeout), int(PktType.PktTypeCompletion)
PT_CREDIT, PT_CHAN, PT_STREAM = int(PktType.PktTypeCredit), int(PktType.PktTypeChannel), int(PktType.PktTypeStream)

# payload layouts: field -> (lsb, width), from the cand_entry() table in
# rtl/amba/ocelus/chi_monitor_lite.sv (event_data, 64 bits)
_E = CHIErrorCode
_C = CHICompletionCode
_T = CHITimeoutCode
LAYOUT = {
    (PT_COMPL, int(_C.CHI_COMPL_TXN)):   dict(lat=(48, 16), opc=(40, 8), txnid=(24, 12), occ=(16, 8), txns=(0, 16)),
    (PT_COMPL, int(_C.CHI_COMPL_RETRY)): dict(pcrd=(40, 4), txnid=(24, 12), occ=(16, 8), txns=(0, 16)),
    (PT_COMPL, int(_C.CHI_COMPL_SNP)):   dict(lat=(48, 16), txnid=(24, 12), snps=(0, 16)),
    (PT_ERR, int(_E.CHI_ERR_PROTOCOL)):  dict(occ=(48, 16), tx_link=(40, 2), rx_link=(32, 2), txns=(0, 32)),
    (PT_ERR, int(_E.CHI_ERR_RESP_ERR)):  dict(opc=(56, 8), rerr=(48, 2), txnid=(32, 12), txns=(0, 32)),
    (PT_ERR, int(_E.CHI_ERR_ORPHAN_RSP)):     dict(opc=(56, 8), txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_ORPHAN_DAT)):     dict(opc=(56, 8), txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_ORPHAN_ACK)):     dict(opc=(56, 8), txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_ORPHAN_SNP_RSP)): dict(opc=(56, 8), txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_TABLE_FULL)):     dict(opc=(56, 8), txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_SNP_TABLE_FULL)): dict(txnid=(32, 12), occ=(16, 16)),
    (PT_ERR, int(_E.CHI_ERR_EVENT_DROPPED)):  dict(count=(0, 16)),
    (PT_TMO, int(_T.CHI_TIMEOUT_TXN)):    dict(opc=(56, 8), txnid=(40, 12), age=(16, 16), cfg=(0, 16)),
    (PT_TMO, int(_T.CHI_TIMEOUT_SNP)):    dict(txnid=(40, 12), age=(16, 16), cfg=(0, 16)),
    (PT_TMO, int(_T.CHI_TIMEOUT_CREDIT)): dict(starve=(32, 32), age=(16, 16), cfg=(0, 16)),
    (PT_TMO, int(_T.CHI_TIMEOUT_LINK)):   dict(occ=(48, 16), is_tx=(42, 1), tx_link=(40, 2), rx_link=(32, 2),
                                               age=(16, 16), cfg=(0, 16)),
    (PT_CREDIT, int(CHICreditCode.CHI_CREDIT_STARVED)):      dict(cycles=(32, 32), thresh=(0, 32)),
    (PT_CREDIT, int(CHICreditCode.CHI_CREDIT_BACKPRESSURE)): dict(cycles=(32, 32), thresh=(0, 32)),
    (PT_CHAN, int(CHIChannelCode.CHI_CHAN_PCRD_GRANT)):   dict(pcrd=(32, 4), txns=(0, 32)),
    (PT_CHAN, int(CHIChannelCode.CHI_CHAN_PCRD_RETURN)):  dict(txnid=(32, 12), txns=(0, 32)),
    (PT_CHAN, int(CHIChannelCode.CHI_CHAN_READ_RECEIPT)): dict(txnid=(32, 12), txns=(0, 32)),
}
_STREAM_LAYOUT = dict(occ=(48, 16), prev_tx=(40, 2), prev_rx=(32, 2), tx_link=(24, 2), rx_link=(16, 2),
                      txns=(0, 16))
for _c in range(8):
    LAYOUT[(PT_STREAM, _c)] = _STREAM_LAYOUT

RETIRE_SLACK = 12         # cycles a finished slot may still occupy the table (one retire a cycle + event stage)
CHANNEL_ORDER = ('cpl_rsp', 'cpl_dat', 'rq_rsp', 'rq_dat', 'req', 'snp')


def unpack(ptype: int, code: int, data: int) -> dict[str, int]:
    lay = LAYOUT.get((ptype, code))
    if lay is None:
        return {}
    return {n: (data >> lsb) & ((1 << w) - 1) for n, (lsb, w) in lay.items()}


def data_packets(size_enc: int, dw: int) -> int:
    """DAT packets a 2**size-byte transfer needs on a dw-bit bus (B2.9.4)."""
    return 1 if (1 << size_enc) * 8 <= dw else ((1 << size_enc) * 8) // dw


def chan_of(txnid: int) -> int:
    """channel_id is 9 bits: the 12-bit TxnID truncated."""
    return int(txnid) & 0x1FF


@dataclass
class Ev:
    """One packet the ocelus owes."""
    ptype: int
    code: int
    chan: int
    cyc: int
    exact: dict[str, int] = field(default_factory=dict)
    rng: dict[str, tuple[int, int]] = field(default_factory=dict)
    optional: bool = False
    tag: str = ''
    info: str = ''

    @property
    def key(self):
        return (self.ptype, self.code, self.chan)

    def accepts(self, fields: dict[str, int]) -> bool:
        for n, v in self.exact.items():
            if fields.get(n) != v:
                return False
        for n, (lo, hi) in self.rng.items():
            if not lo <= fields.get(n, -1) <= hi:
                return False
        return True

    def __repr__(self):
        return (f"Ev({self.tag or (self.ptype, self.code)} chan={self.chan:#x} cyc={self.cyc} "
                f"{self.exact} {self.rng}{' opt' if self.optional else ''} {self.info})")


@dataclass
class _Slot:
    txnid: int
    opcode: int
    eca: bool
    pkts: int
    alloc: int
    need_comp: bool = True
    need_ack: bool = False
    need_dbid: bool = False
    dat_rem: int = 0
    wdat_rem: int = 0
    dbid: int = 0
    dbid_ok: bool = False
    done: int | None = None
    instant: bool = False      # freed in the same cycle (RetryAck), no retire slack

    def awaiting_rsp(self):
        """Still owed a TxnID-addressed response (a reused TxnID lands on the new request)."""
        return self.need_comp or self.need_dbid or bool(self.dat_rem)

    def owes(self):
        return self.need_comp or self.need_ack or self.need_dbid or self.dat_rem or self.wdat_rem


@dataclass
class _Snoop:
    txnid: int
    alloc: int
    rem: int
    done: int | None = None


_COMP_OPS = (RspOpcode.Comp, RspOpcode.CompDBIDResp, RspOpcode.RespSepData, RspOpcode.CompPersist,
             RspOpcode.CompStashDone)
_DBID_OPS = (RspOpcode.CompDBIDResp, RspOpcode.DBIDResp, RspOpcode.DBIDRespOrd)
_TXN_RSP_OPS = _COMP_OPS + _DBID_OPS + (RspOpcode.RetryAck, RspOpcode.ReadReceipt)
_RDATA_OPS = (DatOpcode.CompData, DatOpcode.DataSepResp)
_WDATA_OPS = (DatOpcode.NonCopyBackWriteData, DatOpcode.CopyBackWriteData, DatOpcode.NonCopyBackWriteDataCompAck,
              DatOpcode.WriteDataCancel)
_SNPDATA_OPS = (DatOpcode.SnpRespData, DatOpcode.SnpRespDataPtl, DatOpcode.SnpRespDataFwded)


class ChiMonModel:
    """Feed handshakes and link states; read ``events`` and the counters."""

    def __init__(self, cfg, max_txn: int, max_snp: int):
        self.cfg = cfg
        self.dw = cfg.data_width
        self.n, self.m = max_txn, max_snp
        self.line_pkts = data_packets(6, self.dw)
        self.slots: list[_Slot] = []
        self.snoops: list[_Snoop] = []
        self.events: list[Ev] = []
        self.txns = 0
        self.snps = 0
        self.ambiguous = 0
        self.errors: list[str] = []
        self._tx = 0
        self._rx = 0
        self.counts = {}

    # ---- helpers -----------------------------------------------------------
    def count(self, k, n=1):
        self.counts[k] = self.counts.get(k, 0) + n

    def _emit(self, cyc, ptype, code, chan=0, exact=None, rng=None, optional=False, tag=''):
        self.events.append(Ev(ptype, int(code), chan & 0x1FF, cyc, exact or {}, rng or {}, optional, tag))

    def _live(self, cyc, loose):
        out = [s for s in self.slots if s.done is None]
        if loose:
            out += [s for s in self.slots if s.done is not None and not s.instant and cyc - s.done <= RETIRE_SLACK]
        return out

    def occupancy_now(self, cyc):
        return len(self._live(cyc, False))

    def _find_txn(self, txnid):
        for s in self.slots:
            if s.done is None and s.txnid == txnid and s.awaiting_rsp():
                return s
        return None

    def _find_dbid(self, dbid):
        return [s for s in self.slots if s.done is None and s.dbid_ok and s.dbid == dbid]

    def _find_snoop(self, txnid):
        for s in self.snoops:
            if s.done is None and s.txnid == txnid:
                return s
        return None

    def _settle(self, cyc, s):
        if s.done is None and not s.owes():
            s.done = cyc
            self.txns += 1
            self.count('txn_retired')
            lat0 = cyc - s.alloc
            self._emit(cyc, PT_COMPL, _C.CHI_COMPL_TXN, s.txnid,
                       exact=dict(opc=s.opcode, txnid=s.txnid),
                       rng=dict(lat=(lat0, lat0 + self.n + 6), occ=(0, self.n)), tag='TXN')

    # ---- the six channels ------------------------------------------------------
    def feed(self, cyc: int, msgs: dict[str, int]):
        """``msgs``: channel name -> flit word, for the channels that
        handshook this cycle."""
        for ch in CHANNEL_ORDER:
            if ch in msgs:
                getattr(self, f"_on_{ch}")(cyc, msgs[ch])
        # forget slots that can no longer matter
        self.slots = [s for s in self.slots if s.done is None or cyc - s.done <= RETIRE_SLACK]
        self.snoops = [s for s in self.snoops if s.done is None or cyc - s.done <= RETIRE_SLACK]

    def _on_req(self, cyc, word):
        f = CHIReqFlit.from_word(self.cfg, word)
        op = int(f.opcode)
        if op in (int(ReqOpcode.ReqLCrdReturn), 0x3A):      # LCrdReturn, PrefetchTgt: not tracked
            return
        if op == int(ReqOpcode.PCrdReturn):
            self.count('pcrd_return')
            self._emit(cyc, PT_CHAN, CHIChannelCode.CHI_CHAN_PCRD_RETURN, f.txnid, exact=dict(txnid=f.txnid),
                       tag='PCRD_RETURN')
            return
        strict = len(self._live(cyc, False))
        loose = len(self._live(cyc, True))
        if strict >= self.n:
            self.count('table_full')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_TABLE_FULL, f.txnid,
                       exact=dict(opc=op, txnid=f.txnid, occ=self.n), tag='TABLE_FULL')
            return
        if loose >= self.n:
            self.ambiguous += 1
            self.errors.append(f"cycle {cyc}: request TxnID {f.txnid:#x} arrived within {RETIRE_SLACK} cycles of a "
                               f"slot finishing with the table otherwise full (stimulus boundary)")
        cls = REQ_CLASS.get(ReqOpcode(op))
        pkts = data_packets(int(f.size), self.dw)
        is_read = cls in (ReqClass.READ_ALLOC, ReqClass.READ_NOALLOC)
        is_write = cls in (ReqClass.WRITE_IMM, ReqClass.WRITE_COPYBACK)
        self.slots.append(_Slot(need_dbid=is_write, txnid=int(f.txnid), opcode=op, eca=bool(f.expcompack), pkts=pkts, alloc=cyc,
                                need_ack=bool(f.expcompack), dat_rem=pkts if is_read else 0))
        self.count('txn_alloc')

    def _on_cpl_rsp(self, cyc, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        op = RspOpcode(int(f.opcode))
        if op == RspOpcode.PCrdGrant:
            self.count('pcrd_grant')
            self._emit(cyc, PT_CHAN, CHIChannelCode.CHI_CHAN_PCRD_GRANT, 0, exact=dict(pcrd=int(f.pcrdtype)),
                       tag='PCRD_GRANT')
            return
        if op == RspOpcode.ReadReceipt:
            self.count('read_receipt')
            self._emit(cyc, PT_CHAN, CHIChannelCode.CHI_CHAN_READ_RECEIPT, int(f.txnid),
                       exact=dict(txnid=int(f.txnid)), tag='READ_RECEIPT')
            return
        if op not in _TXN_RSP_OPS:
            return
        s = self._find_txn(int(f.txnid))
        if s is None:
            self.count('orphan_rsp')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_ORPHAN_RSP, int(f.txnid),
                       exact=dict(opc=int(op), txnid=int(f.txnid)), rng=dict(occ=(0, self.n)), tag='ORPHAN_RSP')
            return
        if int(f.resperr) & 2:
            self.count('resp_err')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_RESP_ERR, int(f.txnid),
                       exact=dict(opc=int(op), rerr=int(f.resperr), txnid=int(f.txnid)), tag='RESP_ERR')
        if op == RspOpcode.RetryAck:
            s.done = cyc
            s.instant = True
            self.txns += 1
            self.count('retry')
            self._emit(cyc, PT_COMPL, _C.CHI_COMPL_RETRY, s.txnid,
                       exact=dict(pcrd=int(f.pcrdtype), txnid=s.txnid), rng=dict(occ=(0, self.n)), tag='RETRY')
            return
        if op == RspOpcode.ReadReceipt:
            self.count('read_receipt')
            self._emit(cyc, PT_CHAN, CHIChannelCode.CHI_CHAN_READ_RECEIPT, s.txnid, exact=dict(txnid=s.txnid),
                       tag='READ_RECEIPT')
            return
        if op in _COMP_OPS:
            s.need_comp = False
        if op in _COMP_OPS or op in _DBID_OPS:
            s.dbid, s.dbid_ok = int(f.dbid), True
        if op in _DBID_OPS:
            s.need_dbid = False
            s.wdat_rem = s.pkts
        self._settle(cyc, s)

    def _on_cpl_dat(self, cyc, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        op = int(f.opcode)
        if op not in [int(o) for o in _RDATA_OPS]:
            return
        s = self._find_txn(int(f.txnid))
        if s is None:
            self.count('orphan_dat')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_ORPHAN_DAT, int(f.txnid),
                       exact=dict(opc=op, txnid=int(f.txnid)), rng=dict(occ=(0, self.n)), tag='ORPHAN_DAT')
            return
        if int(f.resperr) & 2:
            self.count('resp_err')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_RESP_ERR, int(f.txnid),
                       exact=dict(opc=op, rerr=int(f.resperr), txnid=int(f.txnid)), tag='RESP_ERR')
        if s.dat_rem:
            if op == int(DatOpcode.CompData) and s.dat_rem <= 1:
                s.need_comp = False
            s.dat_rem -= 1
        elif op == int(DatOpcode.CompData):
            s.need_comp = False
        s.dbid, s.dbid_ok = int(f.dbid), True
        self._settle(cyc, s)

    def _orph_ack(self, cyc, opc, txnid):
        self.count('orphan_ack')
        self._emit(cyc, PT_ERR, _E.CHI_ERR_ORPHAN_ACK, txnid, exact=dict(opc=opc, txnid=txnid),
                   rng=dict(occ=(0, self.n)), tag='ORPHAN_ACK')

    def _orph_snp(self, cyc, opc, txnid):
        self.count('orphan_snp_rsp')
        self._emit(cyc, PT_ERR, _E.CHI_ERR_ORPHAN_SNP_RSP, txnid, exact=dict(opc=opc, txnid=txnid),
                   rng=dict(occ=(0, self.n)), tag='ORPHAN_SNP_RSP')

    def _snoop_done(self, cyc, sn):
        sn.done = cyc
        self.snps += 1
        self.count('snoop_done')
        lat0 = cyc - sn.alloc
        self._emit(cyc, PT_COMPL, _C.CHI_COMPL_SNP, sn.txnid, exact=dict(txnid=sn.txnid),
                   rng=dict(lat=(lat0, lat0 + 8)), tag='SNP')

    def _on_rq_rsp(self, cyc, word):
        f = CHIRspFlit.from_word(self.cfg, word)
        op = RspOpcode(int(f.opcode))
        if op == RspOpcode.CompAck:
            hits = self._find_dbid(int(f.txnid))
            if not hits:
                self._orph_ack(cyc, int(op), int(f.txnid))
                return
            for s in hits:
                s.need_ack = False
                self._settle(cyc, s)
        elif op in (RspOpcode.SnpResp, RspOpcode.SnpRespFwded):
            sn = self._find_snoop(int(f.txnid))
            if sn is None:
                self._orph_snp(cyc, int(op), int(f.txnid))
                return
            self._snoop_done(cyc, sn)

    def _on_rq_dat(self, cyc, word):
        f = CHIDatFlit.from_word(self.cfg, word)
        op = int(f.opcode)
        if op in [int(o) for o in _WDATA_OPS]:
            hits = self._find_dbid(int(f.txnid))
            if not hits:
                self._orph_ack(cyc, op, int(f.txnid))
                return
            for s in hits:
                if op == int(DatOpcode.WriteDataCancel):
                    s.wdat_rem = 0
                elif s.wdat_rem:
                    s.wdat_rem -= 1
                if op == int(DatOpcode.NonCopyBackWriteDataCompAck):
                    s.need_ack = False
                self._settle(cyc, s)
        elif op in [int(o) for o in _SNPDATA_OPS]:
            sn = self._find_snoop(int(f.txnid))
            if sn is None:
                self._orph_snp(cyc, op, int(f.txnid))
                return
            if sn.rem <= 1:
                self._snoop_done(cyc, sn)
            else:
                sn.rem -= 1

    def _on_snp(self, cyc, word):
        f = CHISnpFlit.from_word(self.cfg, word)
        live = [s for s in self.snoops if s.done is None]
        if len(live) >= self.m:
            self.count('snp_table_full')
            self._emit(cyc, PT_ERR, _E.CHI_ERR_SNP_TABLE_FULL, int(f.txnid), exact=dict(txnid=int(f.txnid)),
                       rng=dict(occ=(0, self.n)), tag='SNP_TABLE_FULL')
            return
        loose = [s for s in self.snoops if s.done is None or cyc - s.done <= RETIRE_SLACK]
        if len(loose) >= self.m:
            self.ambiguous += 1
            self.errors.append(f"cycle {cyc}: snoop TxnID {int(f.txnid):#x} arrived near a snoop slot freeing "
                               f"with the table otherwise full (stimulus boundary)")
        self.snoops.append(_Snoop(int(f.txnid), cyc, self.line_pkts))
        self.count('snoop_alloc')

    # ---- link state ----------------------------------------------------------
    def feed_state(self, cyc: int, tx: int, rx: int):
        """Stream events: a direction entering ACTIVATE, RUN, DEACTIVATE or STOP."""
        base = {2: 0, 3: 1, 1: 2, 0: 3}
        if tx != self._tx:
            self.count('stream_tx')
            self._emit(cyc, PT_STREAM, base[tx], 0, exact=dict(prev_tx=self._tx, tx_link=tx), tag=f'TX_{tx}')
            self._tx = tx
        if rx != self._rx:
            self.count('stream_rx')
            self._emit(cyc, PT_STREAM, 4 + base[rx], 0, exact=dict(prev_rx=self._rx, rx_link=rx), tag=f'RX_{rx}')
            self._rx = rx

    # ---- bookkeeping the tests read -------------------------------------------------
    def open_txns(self):
        return [s for s in self.slots if s.done is None]

    def open_snoops(self):
        return [s for s in self.snoops if s.done is None]


def episodes(series, active=lambda v: bool(v)):
    """[(start_index, length)] of the consecutive runs of ``active`` values."""
    out, start = [], None
    for i, v in enumerate(series):
        if active(v):
            if start is None:
                start = i
        elif start is not None:
            out.append((start, i - start))
            start = None
    if start is not None:
        out.append((start, len(series) - start))
    return out


def match(expected: list[Ev], got: list[tuple[object, dict[str, int]]]):
    """Pair delivered packets with expected events by (type, code, channel)
    then payload. Returns (unexpected packets, missing events, matched pairs).
    ``got`` is [(MonitorPacket, unpacked fields)]."""
    pool: dict[tuple, list[Ev]] = {}
    for e in expected:
        pool.setdefault(e.key, []).append(e)
    unexpected, pairs = [], []
    for p, fields in got:
        key = (int(p.packet_type), int(p.event_code), int(p.channel_id))
        cands = pool.get(key, [])
        acc = [e for e in cands if e.accepts(fields)]
        hit = next((e for e in acc if not e.optional), acc[0] if acc else None)   # required events first
        if hit is None:
            unexpected.append((p, fields))
        else:
            cands.remove(hit)
            pairs.append((hit, p, fields))
    missing = [e for lst in pool.values() for e in lst]
    return unexpected, missing, pairs
