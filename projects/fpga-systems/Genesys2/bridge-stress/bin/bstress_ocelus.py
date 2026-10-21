# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Ocelus on a bridge stress build: the host side of the DUT's monitors.

A DUT built as the bridge's monitored variant (TOML `variants = ["mon"]`,
gen_bs_harness) has an Ocelus monitor on every port. The control block says
so (STATUS.HAS_MON); the monitors' cfg regblock is the configuration
bridge's window ext2 and the group's error-FIFO drain window ext3.

Per run, before the fill sweep, the host:
  - empties the error FIFO (a record left by an earlier run is reported
    and dropped, so a run reports only what it raised);
  - sets every port's monitor: timeouts on at TIMEOUT_US, errors on unless
    the profile injects them (Profile.errors -- those responses are the
    test, not a finding), completions / thresholds / performance / debug
    off;
  - routes every AXI packet type to the error FIFO (group axi_err_select),
    so nothing goes to the trace-write master.
After the run (and its read sweep) it drains the FIFO and names, for each
record, the port, the direction, the packet type and event, the AXI ID and
the address -- on a hang, which transaction never completed and where.

LIMITS (each reported when it bites):
  - TIMEOUT_US: a transaction outstanding longer is reported as a timeout.
    The board's worst legal latency measured is ~124 us (cpu.wr, narrow,
    2026-10-20), so 2 ms is 16x that; a slower legal path would be reported.
    The monitors' "microsecond" is 100 cycles of the clock each runs on
    (the wrappers' ACLK_MHZ default; their tick LUT has that one entry, so
    freq_sel selects nothing -- bridge BUG-021): exact on aclk, 1.33 us on
    cclk, where a cdc slave several masters share is monitored (bridge W9).
  - MAX_RECORDS per run are drained; more are counted, not decoded.
  - A drain read of an empty FIFO stalls the bus (the group holds RVALID),
    so a record is read only while STATUS.MON_IRQ says one is waiting.
Decoding is the shared TBClasses.monbus.parse.
"""
from __future__ import annotations

from pathlib import Path
from typing import Callable, List

from TBClasses.harness.device import Device
from TBClasses.monbus import parse

MON_CFG_BASE = 0x0012_0000           # gen_bs_harness MON_WINDOWS: ext2
MON_DRAIN_BASE = 0x0013_0000         # ext3
DRAIN_WORDS = 6                      # 32-bit drain: 3 slices x {low, high}
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

    def drain(self) -> List:
        """Every record waiting, up to MAX_RECORDS, decoded."""
        out = []
        while self.h.ctl.field('STATUS', 'MON_IRQ'):
            if len(out) == MAX_RECORDS:
                self.log(f'  ocelus: MAX_RECORDS ({MAX_RECORDS}) drained; more are waiting')
                break
            w = [self.h.bridge.read(MON_DRAIN_BASE + 4 * i) for i in range(DRAIN_WORDS)]
            if any(x is None for x in w):
                raise IOError('ocelus: drain read failed')
            # monbus_group_core's slices: {tag, source_ts}, packet[127:64],
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
