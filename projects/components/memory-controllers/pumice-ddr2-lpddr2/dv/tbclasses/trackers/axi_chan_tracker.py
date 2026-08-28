# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AxiChanTracker
# Purpose: Passive per-cycle valid/ready accounting for ONE AXI channel --
#          utilization buckets + handshake RUN LENGTHS, so streaming
#          efficiency can be graded in sim without adding perf logic to
#          the pumice RTL.

"""
Passive AXI-channel utilization + run-length tracker.

Answers two questions the golden-data tests cannot:

1. **How long does the handshake hold?** The longest run of consecutive
   cycles with `valid && ready` both high. On a healthy streaming read
   the R channel should hold the handshake for a whole burst and ideally
   bridge burst boundaries; a max run of 1-2 on a 4-beat burst means
   something re-arbitrates every beat.
2. **Where do the cycles go?** The same four buckets `axi_bus_meter.sv`
   counts in hardware, so sim numbers and board numbers mean the same
   thing:

   | valid | ready | bucket        | meaning                          |
   |-------|-------|---------------|----------------------------------|
   |   1   |   1   | productive    | data delivered                   |
   |   1   |   0   | backpressure  | master wants to send, slave stalls |
   |   0   |   1   | starvation    | slave ready, master not producing |
   |   0   |   0   | idle          | both sides quiet                 |

NOTE ON SCOPE: this lives in DV, not RTL. Per the 2026-08-26 direction
("no monitor or perf logic inside pumice -- an external block does that"),
silicon-side measurement belongs to `axi4_intf_master_observer`
(PUMICE-008). This tracker is the SIM equivalent and adds no gates.

## Signals → events table

| Condition                          | Event emitted | Notes                              |
|------------------------------------|---------------|------------------------------------|
| end of a `valid&&ready` run        | `RUN_<n>`     | n = run length in cycles           |
| end of a `valid&&!ready` run       | `BP_<n>`      | n = consecutive stall cycles       |
| `last` beat with handshake         | `BURST_END`   | data=`beats=N` of that burst       |

Runs are emitted when they END, so one row per run instead of one per
cycle -- the log stays greppable at 100k cycles.

## Grep examples

```
grep '| axir ' run.md                    # read-data channel only
grep -E '\\| axi[a-z]+ +\\| RUN_' run.md   # every handshake run, all channels
grep '| axiw    | BP_' run.md            # write-data stalls only
```

## Stats (`.stats()`)

* `utilization` — **beats / cycles `valid` was high** (the headline number).
  NOT beats per wall-clock cycle: the denominator is `prod + bp` only, so
  cycles the master had nothing to offer are excluded. 100% means the DUT
  accepted every beat the cycle it was offered.
* `valid_cycles` — that denominator, exposed so a number can be re-derived
* `max_run` / `run_histogram` — how long the handshake sustains
* `max_bp_run` / `max_starv_run` — worst stall / worst starve
* `bucket_pct` — prod/bp/starv/idle as percentages, matching axi_bus_meter
"""

from __future__ import annotations

from collections import Counter, deque
from typing import Deque, Dict, Optional

from cocotb.triggers import RisingEdge

from ._base import (TrackerEvent, is_high, _sim_time_ns, auto_dump_register,
                    tracker_clock)


_NBA_SETTLE_PS = 1


class AxiChanTracker:
    """Per-cycle valid/ready accounting for one AXI channel.

        AxiChanTracker(dut, 'ar', valid='s_axi_arvalid', ready='s_axi_arready')
        AxiChanTracker(dut, 'r',  valid='s_axi_rvalid',  ready='s_axi_rready',
                       last='s_axi_rlast')

    `last` is optional; give it on the burst channels (W/R) to get
    per-burst beat counts.
    """

    def __init__(self, dut, chan: str, *, valid: str, ready: str,
                 last: Optional[str] = None, log=None,
                 output_dir: Optional[str] = None,
                 filename:   Optional[str] = None,
                 clk_signal: Optional[str] = None):
        self.dut = dut
        self._clk_h = (getattr(dut, clk_signal) if clk_signal
                       else tracker_clock(dut, log))
        self.log = log
        self.chan = chan
        self._name = f"axi{chan}"
        self.SHORT_NAME = self._name
        self._sig_v, self._sig_r, self._sig_last = valid, ready, last
        self._cycle = 0
        # buckets (axi_bus_meter semantics)
        self.prod = self.bp = self.starv = self.idle = 0
        # run state
        self._run = 0          # current valid&&ready run
        self._bp_run = 0       # current valid&&!ready run
        self._starv_run = 0    # current !valid&&ready run
        self.max_run = 0
        self.max_bp_run = 0
        self.max_starv_run = 0
        self.run_hist: Counter = Counter()
        self._burst_beats = 0
        self.events: Deque[TrackerEvent] = deque()
        self.output_path = auto_dump_register(
            self, self._name, output_dir=output_dir, filename=filename,
        )

    async def run(self) -> None:
        while True:
            await RisingEdge(self._clk_h)
            # SAMPLE IMMEDIATELY -- no Timer, no ReadOnly. This monitors
            # TESTBENCH-driven signals (a BFM's *valid) as well as RTL ones,
            # and the two need opposite treatment:
            #   * an RTL output settles in NBA at the edge, so edge+1ps is fine;
            #   * a cocotb DRIVER writes right after the edge it just consumed,
            #     and that write lands before either Timer(1ps) or ReadOnly --
            #     so any delayed sample reads the driver's NEXT intent (usually
            #     valid already deasserted) instead of what was on the bus AT
            #     the edge.
            # Measured 2026-08-27: with a delayed sample, AW/W/AR read 0%
            # utilization / 100% starvation on a run where the rd CAM tracker
            # counted 1024 inserts -- i.e. the handshakes were invisible.
            # Reading with no intervening await yields the pre-edge value,
            # which is exactly what the DUT's flops sampled.
            self._cycle += 1

            v = is_high(self.dut, self._sig_v)
            r = is_high(self.dut, self._sig_r)

            if v and r:
                self.prod += 1
                self._run += 1
                self._burst_beats += 1
                if self._sig_last and is_high(self.dut, self._sig_last):
                    self._push("BURST_END", data=f"beats={self._burst_beats}")
                    self._burst_beats = 0
            else:
                self._close_run()

            if v and not r:
                self.bp += 1
                self._bp_run += 1
            else:
                if self._bp_run:
                    self.max_bp_run = max(self.max_bp_run, self._bp_run)
                    self._push(f"BP_{self._bp_run}", data="stalled")
                    self._bp_run = 0

            if r and not v:
                self.starv += 1
                self._starv_run += 1
            else:
                self.max_starv_run = max(self.max_starv_run, self._starv_run)
                self._starv_run = 0

            if not v and not r:
                self.idle += 1

    def _close_run(self) -> None:
        if self._run:
            self.max_run = max(self.max_run, self._run)
            self.run_hist[self._run] += 1
            self._push(f"RUN_{self._run}", data="handshake held")
            self._run = 0

    def _push(self, event: str, **kw) -> None:
        ev = TrackerEvent(
            sim_time_ns=_sim_time_ns(), cycle=self._cycle,
            tracker=self._name, event=event,
            rank=kw.get('rank', -1), bank=kw.get('bank', -1),
            slot=kw.get('slot', -1), data=kw.get('data', ""),
        )
        self.events.append(ev)
        if self.log:
            self.log.debug(ev.to_md_row())

    # ---------------- stats ----------------

    def stats(self) -> Dict[str, object]:
        total = self.prod + self.bp + self.starv + self.idle
        pct = (lambda n: round(100.0 * n / total, 2)) if total else (lambda n: None)
        # a run still open at end of sim still counts
        max_run = max(self.max_run, self._run)
        # UTILIZATION IS BEATS PER VALID-CYCLE, not per wall-clock cycle.
        # The denominator is only the cycles the master actually held `valid`
        # high (prod + bp) -- which naturally ends when the last `ready`
        # drops it. Cycles where the master had nothing to offer
        # (starvation, idle) are the TESTBENCH's gaps and say nothing about
        # the DUT, so including them just dilutes the number with stimulus
        # quality. Defined this way, 100% means "every cycle data was
        # offered, the DUT took it" -- the thing the design is answerable
        # for. The four buckets below still divide by wall-clock cycles so
        # they keep matching axi_bus_meter.sv.
        valid_cycles = self.prod + self.bp
        return {
            'channel':        self.chan,
            'cycles':         total,
            'valid_cycles':   valid_cycles,
            'utilization':    (self.prod / valid_cycles) if valid_cycles else None,
            'bucket_pct':     {'prod': pct(self.prod), 'bp': pct(self.bp),
                               'starv': pct(self.starv), 'idle': pct(self.idle)},
            'max_run':        max_run,
            'avg_run':        (sum(k * v for k, v in self.run_hist.items())
                               / sum(self.run_hist.values())
                               ) if self.run_hist else None,
            'run_histogram':  dict(sorted(self.run_hist.items())),
            'max_bp_run':     self.max_bp_run,
            'max_starv_run':  self.max_starv_run,
        }

    def summary(self) -> str:
        """One-line human summary -- what to print at end of test."""
        s = self.stats()
        u = s['utilization']
        return (f"{self._name}: util={u:.1%} (beats/valid-cyc) " if u is not None
                else f"{self._name}: util=n/a ") + (
                f"max_run={s['max_run']} avg_run="
                f"{s['avg_run']:.1f} " if s['avg_run'] else "max_run=0 ") + (
                f"bp={s['bucket_pct']['bp']}% starv={s['bucket_pct']['starv']}% "
                f"idle={s['bucket_pct']['idle']}% max_stall={s['max_bp_run']}")


def wire_axi_channels(dut, *, prefix: str = "s_axi_", log=None,
                      output_dir: Optional[str] = None,
                      clk_signal: Optional[str] = None,
                      autostart: bool = True) -> Dict[str, AxiChanTracker]:
    """Instantiate a tracker per AXI channel on `prefix` and start them.

    Returns {'aw': .., 'w': .., 'b': .., 'ar': .., 'r': ..}.
    """
    spec = {
        'aw': (f"{prefix}awvalid", f"{prefix}awready", None),
        'w':  (f"{prefix}wvalid",  f"{prefix}wready",  f"{prefix}wlast"),
        'b':  (f"{prefix}bvalid",  f"{prefix}bready",  None),
        'ar': (f"{prefix}arvalid", f"{prefix}arready", None),
        'r':  (f"{prefix}rvalid",  f"{prefix}rready",  f"{prefix}rlast"),
    }
    out: Dict[str, AxiChanTracker] = {}
    for ch, (v, r, last) in spec.items():
        if getattr(dut, v, None) is None:
            continue
        out[ch] = AxiChanTracker(dut, ch, valid=v, ready=r, last=last, log=log,
                                 output_dir=output_dir, clk_signal=clk_signal)
    # One summary file for all channels: cocotb swallows stdout, so a
    # printed summary is invisible -- write it where the per-channel logs
    # already land.
    import atexit, os as _os
    _dir = output_dir or _os.getcwd()
    def _dump_summary() -> None:
        try:
            with open(_os.path.join(_dir, "axi_util.out"), "w") as f:
                f.write("# AXI channel utilization + handshake run lengths\n")
                f.write("# util% = beats / cycles VALID was high (prod+bp),\n")
                f.write("#   i.e. how often the DUT took data it was offered.\n")
                f.write("#   Cycles the master offered nothing are excluded.\n")
                f.write("# bucket %s are over wall-clock cycles and match\n")
                f.write("#   rtl/amba/shared/axi_bus_meter.sv\n\n")
                f.write(f"| {'chan':<5} | {'cycles':>8} | {'vldcyc':>7} "
                        f"| {'util%':>7} "
                        f"| {'prod%':>6} | {'bp%':>6} | {'starv%':>7} "
                        f"| {'idle%':>6} | {'max_run':>7} | {'avg_run':>7} "
                        f"| {'max_stall':>9} |\n")
                f.write(f"|{'-'*7}|{'-'*10}|{'-'*9}|{'-'*9}|{'-'*8}|{'-'*8}|{'-'*9}"
                        f"|{'-'*8}|{'-'*9}|{'-'*9}|{'-'*11}|\n")
                for ch, t in out.items():
                    st = t.stats()
                    b  = st['bucket_pct']
                    u  = st['utilization']
                    f.write(f"| {('axi'+ch):<5} | {st['cycles']:>8} "
                            f"| {st['valid_cycles']:>7} "
                            f"| {(100*u if u is not None else 0):>7.2f} "
                            f"| {b['prod']:>6} | {b['bp']:>6} | {b['starv']:>7} "
                            f"| {b['idle']:>6} | {st['max_run']:>7} "
                            f"| {(st['avg_run'] or 0):>7.2f} "
                            f"| {st['max_bp_run']:>9} |\n")
                f.write("\n# run-length histograms (cycles held : occurrences)\n")
                for ch, t in out.items():
                    st = t.stats()
                    f.write(f"axi{ch}: {st['run_histogram']}\n")
        except Exception as e:                      # noqa: BLE001
            print(f"[axi_util] summary dump failed: {e}")
    atexit.register(_dump_summary)

    if autostart:
        try:
            import cocotb
            from ._base import guard_run
            for ch, t in out.items():
                cocotb.start_soon(guard_run(t.run, f"axi{ch}", log)())
        except Exception as e:                      # noqa: BLE001
            if log:
                log.warning("wire_axi_channels autostart failed: %s", e)
    return out
