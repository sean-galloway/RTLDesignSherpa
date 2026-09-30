# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: byte_sequences
# Purpose: Directed byte-RAPIDS sequences the perf sweep cannot express, run by
#          run_characterization.py --byte-seq on the board and, unmodified, in
#          the UART sim of rapids_byte_top (rapids TASK-019):
#            zero_length    a zero-length descriptor alone and inside chains
#            boundary_4k    payloads that end on / straddle a 4 KB boundary
#            tlast_mismatch sink packet length != descriptor length
#            recovery       mismatch -> CHANNEL_RESET -> good descriptor, with a
#                           second channel concurrently active
#          Every case ends in golden checks and every sequence dumps the
#          running config, so a pass proves what it ran on. Register access is
#          by name only (campaign.read_field / write_fields, io.csr_*).
#
# Documentation: projects/fpga-systems/Genesys2/rapids/flows-rapids/host/
# Subsystem: rapids_byte_harness

import os
import sys

_HOST_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HOST_DIR)

import run_characterization as rc  # noqa: E402
from descriptor_builder import build_data_descriptor, descriptor_to_words  # noqa: E402
from rapids_byte_golden import (LFSR_SEED_DEFAULT, beat_bytes, crc32_over_bytes,  # noqa: E402
                                golden_crc, golden_sink_bytes, lfsr_seq)

LEVELS = ('gate', 'func', 'full')
BOUNDARY = 4096                     # the AXI burst must never cross this
IDLE_READS = 3                      # consecutive idle reads = settled
CHAIN_STRIDE = 32                   # descriptor size in descriptor RAM


# KNOWN RTL BUG (rapids TASK-019, snk_data_path_axis.sv): the ingress shifter
# keeps the data bytes it shifts past a packet's last strobed byte in r_hold_data
# (strobe 0) and ORs them into the NEXT packet of the same channel. It bites
# when a descriptor at offset off > 0 has a partial last stream beat of `tail`
# bytes with off + tail <= bpb (no spill, so no flush clears the hold) and the
# next descriptor starts at a lower offset: the junk lands in strobed lanes.
# Set RAPIDS_SNK_HOLD_JUNK_FIXED=1 once the RTL is fixed: the affected chains
# then use the plain golden.
SNK_HOLD_JUNK_FIXED = os.environ.get('RAPIDS_SNK_HOLD_JUNK_FIXED') == '1'


def snk_hold_junk_hits(chain, pkt_bytes, bpb):
    """True if a same-channel descriptor chain triggers the hold-junk bug."""
    live = [ad % bpb for ln, ad in chain if ln]
    tail = pkt_bytes % bpb
    return bool(tail) and any(
        live[i] > 0 and live[i] + tail <= bpb and live[i + 1] < live[i]
        for i in range(len(live) - 1))


def _rank(level):
    return LEVELS.index(level)


def mem_beats(length, addr, bpb):
    return 0 if length == 0 else -(-((addr % bpb) + length) // bpb)


def stream_beats(length, bpb):
    return -(-length // bpb)


class Seq:
    """One sequence's working state: the campaign, the checks, the launches."""

    def __init__(self, campaign, timeout_s, level, chunk=None):
        self.chunk = chunk              # (k, n), 1-based like --chunk: run every n-th case
        self._case_idx = 0
        self.c = campaign
        self.io = campaign.io
        self.timeout_s = timeout_s
        self.level = level
        self.checks = []
        self.bpb = campaign.ensure_build()['beat_bytes']

    # ---- bookkeeping -------------------------------------------------------

    def check(self, name, ok, **detail):
        self.checks.append({'name': name, 'ok': bool(ok), **detail})
        print(f"    {'ok  ' if ok else 'FAIL'} {name}" +
              (f" {detail}" if detail and not ok else ''), flush=True)
        return bool(ok)

    def mine(self, name=''):
        """True if the next case belongs to this chunk (one sim run is capped at
        100 ms, so a level can be split across runs; the merge joins them)."""
        only = os.environ.get('TEST_SEQ_ONLY')      # debug: run just the named case
        if only and only not in name:
            return False
        i, self._case_idx = self._case_idx, self._case_idx + 1
        return self.chunk is None or i % self.chunk[1] == self.chunk[0] - 1

    def at_least(self, level):
        return _rank(self.level) >= _rank(level)

    # ---- register reads (by name) ------------------------------------------

    def sched_err(self, half):
        return self.c.read_field(half, 'SCHED_ERROR', 'SCHED_ERR')

    def ch_idle(self, half):
        return self.c.read_field(half, 'SCHEDULER_IDLE', 'SCHED_IDLE')

    def settle(self, half, mask):
        """True once every channel in `mask` reads idle IDLE_READS times in a
        row. A UART read is ~10 us of sim time, so three reads outlast the
        descriptor fetch that follows GO."""
        run = 0

        def stable():
            nonlocal run
            run = run + 1 if (self.ch_idle(half) & mask) == mask else 0
            return run >= IDLE_READS
        return self.c._poll(stable, self.timeout_s, period_s=0.0)

    def reset_channel(self, half, ch):
        self.c.write_fields(half, 'CHANNEL_RESET', CH_RST=1 << ch)
        self.c.write_fields(half, 'CHANNEL_RESET', CH_RST=0)

    # ---- descriptor chains -------------------------------------------------

    def load_chains(self, half, specs, data_base):
        """specs: {ch: [(length_bytes, addr_in_channel_region), ...]}. One chain
        per channel, `last` on the final descriptor, zero-length allowed."""
        for ch, chain in specs.items():
            base = rc.DESC_BASE + ch * rc.KICK_STRIDE
            for n, (length, addr) in enumerate(chain):
                last = n + 1 == len(chain)
                buf = data_base + ch * rc.CHANNEL_OFFSET + addr
                beats = stream_beats(length, self.bpb)
                kw = dict(channel_id=ch, last=last,
                          next_ptr=0 if last else base + (n + 1) * CHAIN_STRIDE,
                          length_bytes=length)
                desc = (build_data_descriptor(0, buf, beats, **kw) if half == 'snk'
                        else build_data_descriptor(buf, 0, beats, **kw))
                self.io.load_descriptor(half, base + n * CHAIN_STRIDE, descriptor_to_words(desc))

    # ---- launches ----------------------------------------------------------

    def launch_sink(self, specs, pkt_bytes, pkts, *, interleave=False, gen_mask=None):
        """Generator: `pkts` packets of `pkt_bytes` per channel (uniform across
        the gen mask, a generator limit); descriptors per `specs`."""
        c, bpb = self.c, self.bpb
        kick = sum(1 << ch for ch in specs)
        gmask = kick if gen_mask is None else gen_mask
        bpp = stream_beats(pkt_bytes, bpb) if pkt_bytes else 0
        c.reset_channels()
        self.load_chains('snk', specs, rc.DST_DATA_BASE)
        self.io.csr_write_reg("MEM_CTRL", WR_CRC_RESET=1)
        self.io.csr_write_reg("GEN_SEED", VALUE=0)
        self.io.csr_write_reg("GEN_NBEATS", VALUE=bpp * pkts)
        self.io.csr_write_reg("GEN_BPP", VALUE=bpp)
        self.io.csr_write_reg("GEN_LASTB", VALUE=pkt_bytes - (bpp - 1) * bpb if bpp else 0)
        self.io.csr_write_reg("GEN_CHMASK", VALUE=gmask)
        self.io.csr_write_reg("GEN_TDEST", VALUE=0)
        self.io.csr_write_reg("GEN_MODE", INTERLEAVE=int(interleave))
        c._stage_kicks('snk', kick, start_gen=True)
        self.io.csr_write_reg("OBS_TARGET", VALUE=0)
        c.go()
        return kick

    def launch_source(self, specs):
        c = self.c
        kick = sum(1 << ch for ch in specs)
        c.reset_channels()
        self.io.csr_write_reg("MEM_CTRL", RD_CRC_LFSR_RESET=1)
        self.io.csr_write_reg("CHK_SEED", VALUE=0)
        self.io.csr_write_reg("CHK_CTRL", CHK_START=1, CHK_READY_EN=1)
        self.io.csr_write_reg("CHK_CTRL", CHK_START=0, CHK_READY_EN=1)
        self.load_chains('src', specs, rc.SRC_DATA_BASE)
        c._stage_kicks('src', kick, start_gen=False)
        self.io.csr_write_reg("OBS_TARGET", VALUE=0)
        c.go()
        return kick

    def wait_counter(self, reg, expected):
        return self.c._poll(lambda: self.io.csr_read_reg(reg) == expected, self.timeout_s,
                            period_s=0.0)

    # ---- goldens -----------------------------------------------------------

    def source_golden(self, ch, chain):
        """(rd_crc, egress_crc, stream_beats, mem_beats) for one channel's chain:
        the read LFSR advances once per memory beat across every descriptor
        (zero-length ones read nothing) and the egress re-packs from each
        descriptor's byte offset."""
        bpb = self.bpb
        total = sum(mem_beats(ln, ad, bpb) for ln, ad in chain)
        seq = lfsr_seq((LFSR_SEED_DEFAULT ^ ch) & (1 << 32) - 1, total)
        stream, k = bytearray(), 0
        for ln, ad in chain:
            n = mem_beats(ln, ad, bpb)
            mem = b''.join(beat_bytes(w, bpb) for w in seq[k:k + n])
            k += n
            off = ad % bpb
            stream += mem[off:off + ln]
        return (golden_crc(ch, total, LFSR_SEED_DEFAULT) if total else None,
                crc32_over_bytes(bytes(stream)) if total else None,
                sum(stream_beats(ln, bpb) for ln, _ in chain), total)

    # ---- case runners (launch + wait + score) ------------------------------

    def run_source_case(self, name, specs):
        """Source half: every channel's chain, golden on both CRCs, beat counts,
        no scheduler error, channels settle idle."""
        bpb = self.bpb
        exp = {ch: self.source_golden(ch, chain) for ch, chain in specs.items()}
        stream_total = sum(e[2] for e in exp.values())
        kick = self.launch_source(specs)
        got_count = self.wait_counter("CHK_BEATS_T", stream_total)
        settled = self.settle('src', kick)
        self.check(f"{name}: source completes", got_count and settled,
                   chk_beats=self.io.csr_read_reg("CHK_BEATS_T"), expected=stream_total)
        self.check(f"{name}: no SRC_SCHERR / data_error",
                   self.io.csr_read_reg("SRC_SCHERR") == 0 and
                   not self.io.csr_field("STATUS", "DATA_ERROR"),
                   src_scherr=self.io.csr_read_reg("SRC_SCHERR"))
        for ch, (rd_g, chk_g, sbeats, mbeats) in exp.items():
            if not mbeats:
                continue
            self.io.select_channel(ch)
            rd, chk = self.io.csr_read_reg("RD_CRC"), self.io.csr_read_reg("CHK_ACT_CRC")
            self.check(f"{name}: ch{ch} golden (rd+egress, {sbeats} stream beats)",
                       rd == rd_g and chk == chk_g, rd=rd, rd_golden=rd_g, chk=chk, chk_golden=chk_g)
        return exp

    def run_sink_case(self, name, specs, pkt_bytes, *, interleave=False):
        """Sink half with a uniform generator packet. Channels whose descriptors
        all match the packet length must equal the byte golden."""
        bpb = self.bpb
        npk = {ch: sum(1 for ln, _ in chain if ln) for ch, chain in specs.items()}
        pkts = max(npk.values()) if npk else 0
        assert all(n == pkts for n in npk.values()), "sink generator is uniform per channel"
        wr_total = sum(mem_beats(ln, ad, bpb) for chain in specs.values() for ln, ad in chain)
        kick = self.launch_sink(specs, pkt_bytes, pkts, interleave=interleave)
        got_count = self.wait_counter("WR_BEATS_T", wr_total)
        settled = self.settle('snk', kick)
        self.check(f"{name}: sink completes", got_count and settled,
                   wr_beats=self.io.csr_read_reg("WR_BEATS_T"), expected=wr_total)
        self.check(f"{name}: no SNK_SCHERR / sched_error",
                   self.io.csr_read_reg("SNK_SCHERR") == 0 and self.sched_err('snk') == 0,
                   snk_scherr=self.io.csr_read_reg("SNK_SCHERR"))
        self.check_sink_golden(name, specs, pkt_bytes, pkts)

    def check_sink_golden(self, name, specs, pkt_bytes, pkts, only=None):
        for ch in (only if only is not None else specs):
            if not pkts:
                continue
            self.io.select_channel(ch)
            crc = self.io.csr_read_reg("WR_CRC")
            gold = golden_sink_bytes(ch, pkt_bytes, pkts, self.bpb, LFSR_SEED_DEFAULT)
            if not SNK_HOLD_JUNK_FIXED and snk_hold_junk_hits(specs[ch], pkt_bytes, self.bpb):
                # the RTL must still corrupt this chain; if it matches the bug is fixed
                self.check(f"{name}: ch{ch} KNOWN-BUG snk hold-junk corrupts the write CRC "
                           f"({pkts} x {pkt_bytes} B)", crc != gold, wr_crc=crc, golden=gold,
                           hint="matches golden: RTL fixed, set RAPIDS_SNK_HOLD_JUNK_FIXED=1")
                continue
            self.check(f"{name}: ch{ch} write golden ({pkts} x {pkt_bytes} B)", crc == gold,
                       wr_crc=crc, golden=gold)


# ---- the sequences -----------------------------------------------------------

def seq_zero_length(s):
    """A zero-length descriptor does no read/write and makes no packet record.
    Alone it must complete idle with every counter at 0; in a chain it must not
    disturb its neighbours (the good descriptors still pass golden)."""
    P = s.bpb + 5
    cases = [('alone', lambda: [(0, 0)]),
             ('first', lambda: [(0, 0), (P, 0)]),
             ('last', lambda: [(P, 0), (0, 0)])]
    if s.at_least('func'):
        cases += [('between', lambda: [(P, 0), (0, 0), (P, 2 * s.bpb)]),
                  ('two_zero', lambda: [(0, 0), (0, 0), (P, 0)])]
    for nm, mk in cases:
        chain = mk()
        for ch_n in ((1, 2) if s.at_least('func') else (1,)):
            if not s.mine():
                continue
            specs = {ch: list(chain) for ch in range(ch_n)}
            tag = f"zero_{nm}_ch{ch_n}"
            s.run_source_case(f"{tag}/source", specs)
            s.run_sink_case(f"{tag}/sink", specs, P)
            only_zero = all(ln == 0 for ln, _ in chain)
            if only_zero:
                s.check(f"{tag}: zero-only chain moved nothing",
                        s.io.csr_read_reg("WR_BEATS_T") == 0 and
                        s.io.csr_read_reg("CHK_BEATS_T") == 0,
                        wr=s.io.csr_read_reg("WR_BEATS_T"), chk=s.io.csr_read_reg("CHK_BEATS_T"))


def boundary_cases(bpb, level):
    """(name, pkt_bytes, [addr...]): every descriptor is pkt_bytes long, one per
    listed address (address within the channel region; 4096 = a 4 KB boundary).
    k bytes before the boundary -> ends exactly at it (k == pkt), or straddles."""
    P = 100
    cases = [('end_exact', P, [BOUNDARY - P]),
             ('straddle_1', P, [BOUNDARY - 1]),
             ('straddle_33', P, [BOUNDARY - 33])]
    if _rank(level) >= _rank('func'):
        cases += [('straddle_31', P, [BOUNDARY - 31]),
                  ('straddle_bpb', P, [BOUNDARY - bpb]),
                  ('straddle_64', P, [BOUNDARY - 2 * bpb]),
                  ('max_payload_2k', 4096, [BOUNDARY // 2]),
                  ('chain_across', 77, [BOUNDARY - 120, BOUNDARY - 120 + 77, BOUNDARY - 120 + 154]),
                  ('start_on_boundary', P, [BOUNDARY]),
                  ('end_then_start', P, [BOUNDARY - P, BOUNDARY]),
                  ('unaligned_a', 203, [BOUNDARY - 203 - 1]),
                  ('unaligned_c', 203, [2 * BOUNDARY - 5]),
                  ('unaligned_ab', 203, [BOUNDARY - 203 - 1, BOUNDARY]),
                  ('unaligned_bc', 203, [BOUNDARY, 2 * BOUNDARY - 5]),
                  ('unaligned_chain', 203, [BOUNDARY - 203 - 1, BOUNDARY, 2 * BOUNDARY - 5])]
    return cases


def seq_boundary_4k(s):
    """Descriptors that end on or straddle a 4 KB boundary. The harness has no
    AXI 4 KB checker; the sim campaign adds one (aw/ar monitor, counted), and
    here the data the sink writes and the source returns is golden-checked."""
    for nm, P, addrs in boundary_cases(s.bpb, s.level):
        for ch_n in ((1, 2) if s.at_least('func') else (2,)):
            if not s.mine(nm):
                continue
            specs = {ch: [(P, a) for a in addrs] for ch in range(ch_n)}
            s.run_source_case(f"4k_{nm}_ch{ch_n}/source", specs)
            s.run_sink_case(f"4k_{nm}_ch{ch_n}/sink", specs, P)


def seq_tlast_mismatch(s):
    """Sink only. ch0's descriptor length differs from the generator's packet
    length; ch1 is correct and runs interleaved with it. Expect the sticky
    SNK_SCHERR bit and SCHED_ERROR for ch0 ONLY, and ch1 still golden. The next
    case's launch resets the channels, so the sticky bit also proves the reset
    clears it (the recovery sequence asserts that directly)."""
    bpb = s.bpb
    P = 2 * bpb
    cases = [('desc_short', bpb + 1), ('desc_long', 3 * bpb + 7)]
    if s.at_least('func'):
        cases += [('desc_short_by_1', P - 1), ('desc_long_by_1', P + 1),
                  ('desc_1_byte', 1), ('desc_beat_short', bpb)]
    for nm, l0 in cases:
        for il in ((False, True) if s.at_least('func') else (True,)):
            if not s.mine():
                continue
            tag = f"mismatch_{nm}{'_il' if il else ''}"
            specs = {0: [(l0, 0)], 1: [(P, 0)]}
            kick = s.launch_sink(specs, P, 1, interleave=il)
            s.wait_counter("PKT_CNT", 2)
            s.settle('snk', 2)          # ch1 must finish; ch0 may stay busy on the error
            scherr = s.io.csr_read_reg("SNK_SCHERR")
            s.check(f"{tag}: SNK_SCHERR flags ch0 only", scherr == 1, snk_scherr=scherr)
            s.check(f"{tag}: SCHED_ERROR flags ch0 only", s.sched_err('snk') == 1,
                    sched_err=s.sched_err('snk'))
            s.check_sink_golden(tag, specs, P, 1, only=[1])


def seq_recovery(s):
    """error -> CHANNEL_RESET -> good descriptor, ch1 active throughout.
    1. interleaved run: ch0 mismatches while ch1 streams; ch1 golden.
    2. reset ch0 (by name): SNK_SCHERR and SCHED_ERROR clear; ch1 untouched bit.
    3. both channels get good descriptors, interleaved: both golden, no error.
    (A channel reset cannot be timed mid-stream over UART, so 'concurrent' means
    ch1 shares the generator stream with ch0 in both phases.)"""
    bpb = s.bpb
    P = 2 * bpb + 3
    n_rounds = 2 if s.at_least('func') else 1
    for rnd in range(n_rounds):
        if not s.mine():
            continue
        t = f"recovery{rnd}"
        bad = {0: [(bpb + 1, 0)], 1: [(P, 0)]}
        s.launch_sink(bad, P, 1, interleave=True)
        s.wait_counter("PKT_CNT", 2)
        s.settle('snk', 2)
        s.check(f"{t}: error raised on ch0 only", s.io.csr_read_reg("SNK_SCHERR") == 1 and
                s.sched_err('snk') == 1,
                snk_scherr=s.io.csr_read_reg("SNK_SCHERR"), sched_err=s.sched_err('snk'))
        s.check_sink_golden(f"{t}: ch1 during error", bad, P, 1, only=[1])
        s.reset_channel('snk', 0)
        s.check(f"{t}: CHANNEL_RESET clears SNK_SCHERR", s.io.csr_read_reg("SNK_SCHERR") == 0,
                snk_scherr=s.io.csr_read_reg("SNK_SCHERR"))
        s.check(f"{t}: CHANNEL_RESET clears SCHED_ERROR", s.sched_err('snk') == 0,
                sched_err=s.sched_err('snk'))
        s.check(f"{t}: ch0 idle after reset", s.settle('snk', 1))
        # the launch below re-resets every channel; the clear asserted above is
        # the explicit one, this is the recovery proof
        good = {0: [(P, 0)], 1: [(P, 0)]}
        s.run_sink_case(f"{t}: good descriptors ch0+ch1", good, P, interleave=True)
        s.run_source_case(f"{t}: source untouched", {0: [(P, 0)], 1: [(P, 0)]})


SEQUENCES = {'zero_length': seq_zero_length, 'boundary_4k': seq_boundary_4k,
             'tlast_mismatch': seq_tlast_mismatch, 'recovery': seq_recovery}


def resolve(names):
    if names in (None, 'all'):
        return list(SEQUENCES)
    out = [n.strip() for n in names.split(',') if n.strip()]
    bad = [n for n in out if n not in SEQUENCES]
    if bad:
        raise SystemExit(f"unknown --byte-seq name(s) {bad}; known: {sorted(SEQUENCES)}")
    return out


def run(campaign, name, timeout_s, level='full', chunk=None):
    """Run one sequence; returns {name, pass, checks, config, uart_ops, level}."""
    s = Seq(campaign, timeout_s, level, chunk)
    ops0 = campaign.io.uart_ops
    print(f"\n=== SEQUENCE {name} (level {level}) ===", flush=True)
    try:
        SEQUENCES[name](s)
    except Exception as exc:  # noqa: BLE001 - a dead sequence is a recorded failure
        s.check(f"{name}: exception", False, error=f"{type(exc).__name__}: {exc}")
    return {'name': name, 'level': level, 'chunk': list(chunk) if chunk else None,
            'pass': all(c['ok'] for c in s.checks),
            'checks': s.checks, 'config': campaign.config_dump(),
            'uart_ops': campaign.io.uart_ops - ops0}
