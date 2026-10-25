# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Ocelus on a bridge stress build: the host side of the DUT's monitors.

A DUT built as the bridge's monitored variant (TOML `variants = ["mon"]`,
gen_bs_harness) has an Ocelus monitor on every port. The control block says
so (STATUS.HAS_MON); the monitors' cfg regblock is the configuration
bridge's window ext2 and the write-only group's error-window RAM is ext3.

Per run, before the fill sweep, the host:
  - notes the error-record count (a record left by an earlier run is reported
    and skipped, so a run reports only what it raised);
  - sets every port's monitor: timeouts on at TIMEOUT_US, errors on unless
    the profile injects them (Profile.errors -- those responses are the
    test, not a finding), completions / thresholds / performance / debug
    off;
  - routes every AXI packet type to the error window (group axi_err_select),
    so nothing goes to the trace window.
After the run (and its read sweep) it reads the records the count says
landed from the error window -- a RAM inside the harness filled by the
write-only group (monbus_axil4_group_1wr), addressed exactly like the old
drain -- and names, for each record, the port, the direction, the packet
type and event, the AXI ID and the address -- on a hang, which transaction
never completed and where.

LIMITS (each reported when it bites):
  - TIMEOUT_US: a transaction outstanding longer is reported as a timeout.
    The board's worst legal latency measured is ~124 us (cpu.wr, narrow,
    2026-10-20), so 2 ms is 16x that; a slower legal path would be reported.
    The monitors' "microsecond" is 100 cycles of the clock each runs on
    (the wrappers' ACLK_MHZ default; their tick LUT has that one entry, so
    freq_sel selects nothing -- bridge BUG-021): exact on aclk, 1.33 us on
    cclk, where a cdc slave several masters share is monitored (bridge W9).
  - MAX_RECORDS per run are read; more are counted, not decoded. The window
    holds ERR_CAPACITY records and wraps; a delta past that is reported.
  - The count is free-running (16 bits); the host tracks it by delta.
Decoding is the shared TBClasses.monbus.parse.
"""
from __future__ import annotations

from pathlib import Path
from typing import Callable, List

from TBClasses.harness.device import Device
from TBClasses.monbus import parse

MON_CFG_BASE = 0x0012_0000           # gen_bs_harness MON_WINDOWS: ext2
MON_DRAIN_BASE = 0x0013_0000         # ext3 -- the error-window RAM now
DRAIN_WORDS = 6                      # 32-bit reads: 3 slices x {low, high}
ERR_CAPACITY = 170                   # 4 KB window / 24-byte whole records
TIMEOUT_US = 2000
MAX_RECORDS = 64
UNIT_MASTER, UNIT_SLAVE = 2, 1       # bridge adapters' monitor UNIT_ID


class Ocelus:
    def __init__(self, h, regmap: Path, log: Callable[[str], None] = print):
        self.h, self.log = h, log
        if not regmap.exists():
            raise FileNotFoundError(f'{regmap}: the mon variant is not generated (bin/regen.sh)')
        self.cfg = Device(h.bridge, 'ocelus', regs_base=MON_CFG_BASE, regmap_file=str(regmap))
        b = h.build
        self.masters = list(b.masters)
        self.slaves = list(b.slaves)
        # bridge W9: a cdc slave that two or more masters reach is monitored on
        # its own clock (bridge_mon_cdc); every other monitor runs on aclk
        self.cclk_ports = {s.name for s in self.slaves
                           if s.cdc and sum(s in b.slaves_of(m) for m in self.masters) >= 2}
        if self.cclk_ports:
            log(f'  ocelus: {sorted(self.cclk_ports)} monitored on cclk (timeout ticks 1.33 us)')
        # report error responses even on a profile that injects them: the
        # sim's self-check that records come back, decoded and attributed
        self.force_errors = False
        # free-running MON_ERR_REC_COUNT watermark for delta-per-run drains
        self._last_count = None

    @staticmethod
    def regmap_for(area: Path, dut: str) -> Path:
        return area / 'rtl/bridges/generated' / f'{dut}_mon' / f'{dut}_mon_cfg_regmap.py'

    # ---- per run ---------------------------------------------------------------
    def configure(self, prof) -> None:
        stale = self.drain()
        if stale:
            self.log(f'  ocelus: {len(stale)} record(s) left from before this run, dropped: '
                     + '; '.join(self.describe(p) for p in stale[:4]))
        errors = int(self.force_errors or not getattr(prof, 'errors', False))
        for reg in self.cfg.registers:
            if not (reg.endswith('_WR_CTRL') or reg.endswith('_RD_CTRL')):
                continue
            self.cfg.write(reg, monitor_enable=1, error_enable=errors, timeout_enable=1,
                           perf_enable=0, compl_enable=0, threshold_enable=0, debug_enable=0,
                           freq_sel=0, timeout_cycles=TIMEOUT_US)
        self.cfg.write('MON_GROUP_PACK_0', axi_pkt_mask=0, flush_watermark=0)
        self.cfg.write('MON_GROUP_PACK_1', axi_err_select=0xFFFF, axi_error_mask=0)
        # Write-only group: the error window is the harness RAM's low 4 KB
        # (170 whole records), the trace window the upper 4 KB (idle while
        # every AXI class is err-selected, but legal so the writer never
        # stalls). Watermark 3 = flush every record.
        self.cfg.write_word('MON_GROUP_BASE_ADDR', 0x1000)
        self.cfg.write_word('MON_GROUP_LIMIT_ADDR', 0x1FFF)
        self.cfg.write_word('MON_GROUP_ERR_BASE_ADDR', 0x0000)
        self.cfg.write_word('MON_GROUP_ERR_LIMIT_ADDR', ERR_CAPACITY * 24 - 1)
        self.cfg.write_word('MON_GROUP_ERR_FLUSH_WATERMARK', 3)

    def drain(self) -> List:
        """The records that landed since the last drain, up to MAX_RECORDS,
        decoded. The cue is MON_ERR_REC_COUNT's delta (the 1wr group pulses
        mon_irq per record; a free-running count survives polling)."""
        count = self.cfg.field('MON_ERR_REC_COUNT', 'COUNT')
        if self._last_count is None:
            self._last_count = count
            return []
        delta = (count - self._last_count) & 0xFFFF
        self._last_count = count
        if delta > ERR_CAPACITY:
            self.log(f'  ocelus: {delta} records landed, the window holds '
                     f'{ERR_CAPACITY} -- the oldest were overwritten')
        out = []
        # The window is a ring the writer wraps at record granularity: record
        # number i (0-based, ever) sits at slot (i % ERR_CAPACITY) * 24.
        first = count - delta
        for k in range(min(delta, MAX_RECORDS, ERR_CAPACITY)):
            slot = ((first + k) % ERR_CAPACITY) * 24
            w = [self.h.bridge.read(MON_DRAIN_BASE + slot + 4 * i) for i in range(DRAIN_WORDS)]
            if any(x is None for x in w):
                raise IOError('ocelus: error-window read failed')
            # monbus_group_core_1wr's record: {tag, source_ts}, packet[127:64],
            # packet[63:0]; each 64-bit slice is two 32-bit reads, low first
            ts, hi, lo = (w[i] | w[i + 1] << 32 for i in (0, 2, 4))
            if lo or hi:
                p = parse(hi << 64 | lo)
                p.source_ts = ts & ((1 << 60) - 1)
                out.append(p)
        return out

    def describe(self, p) -> str:
        idx, wr = p.agent_id >> 4, p.agent_id & 1
        ports = self.masters if p.unit_id == UNIT_MASTER else self.slaves
        side = 'master' if p.unit_id == UNIT_MASTER else 'slave'
        name = ports[idx].name if p.unit_id in (UNIT_MASTER, UNIT_SLAVE) and idx < len(ports) \
            else f'unit {p.unit_id} agent {p.agent_id:#x}'
        # lite monitor event data: addr[31:0], latency / age in [63:48]
        addr, hi = p.event_data & 0xFFFF_FFFF, p.event_data >> 48
        return (f'{name}.{"wr" if wr else "rd"} ({side} port): {p.get_packet_type_name()} '
                f'{p.get_event_code_name()} id={p.channel_id:#x} addr={addr:#010x}'
                f'{f" hi={hi:#x}" if hi else ""} t={getattr(p, "source_ts", 0)}')
