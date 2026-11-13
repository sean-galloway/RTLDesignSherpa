"""Export a cocotb sim's AXI request stream as a Ramulator TimedLoadStoreTrace
(memory-controllers MC-013 item 5).

MC-012 fed the model request streams REBUILT from the host program's stride
tables; this writes the stream the controller actually saw, one line per AXI
beat off the controller's own AXI slave port:

    <tick> <LD|ST> <byte address>

An AW handshake of AxLEN+1 beats at 1 << AxSIZE bytes becomes that many ST
lines at consecutive beat addresses; an AR handshake the same as LD. The tick
is the beat's index in acceptance order, the board's one-beat-per-MC-cycle
offer shape (what the rebuilt traces use), so the model schedules the SAME
requests in the SAME order and the two model numbers are comparable; the
cycle each burst was accepted on is kept in the sidecar `<path>.meta.json`
(first / last accept cycle, beats, bursts per direction) for anyone who wants
the controller-shaped timing instead.

Use from a test: build one on the controller's port signals, `start_soon`
its `run()`, then bracket each measured pass with `begin(path)` / `end()`.
Both are safe to call from the host thread (cocotb `bridge`): the coroutine
appends to a list the bracket swaps, so no file handle crosses threads.
The handshake is sampled the way this proxy's other probes sample it
(the value at the rising edge); nothing here drives a signal.

The frontend's contract: ticks non-decreasing, LD / ST only, one request per
line; `char_model.py run-trace` replays the file(s) under a model config.
"""
from __future__ import annotations

import json
from typing import Dict, List, Optional

from cocotb.triggers import RisingEdge


class AxiTraceExporter:
    def __init__(self, clk, *, awvalid, awready, awaddr, awlen, awsize,
                 arvalid, arready, araddr, arlen, arsize) -> None:
        self._clk = clk
        self._aw = (awvalid, awready, awaddr, awlen, awsize)
        self._ar = (arvalid, arready, araddr, arlen, arsize)
        self._lines: Optional[List[str]] = None
        self._meta: Optional[Dict[str, int]] = None
        self._cycle = 0
        self._path: Optional[str] = None
        self.written: List[Dict[str, object]] = []

    # ---- host-thread bracket ------------------------------------------------
    def begin(self, path: str) -> None:
        """Start capturing into `path` (the file is written at `end()`)."""
        self._path = path
        self._meta = dict(first_cycle=-1, last_cycle=-1, st_beats=0, ld_beats=0, st_bursts=0, ld_bursts=0)
        self._lines = []          # published last: the coroutine captures once this is a list

    def end(self) -> Dict[str, object]:
        """Stop capturing, write the trace and its sidecar, return the sidecar dict."""
        lines, self._lines = self._lines, None
        meta, self._meta = self._meta, None
        path, self._path = self._path, None
        if path is None or lines is None or meta is None:
            return {}
        with open(path, "w") as fh:
            fh.write("".join(lines))
        info = dict(meta, path=path, lines=len(lines))
        with open(path + ".meta.json", "w") as fh:
            json.dump(info, fh, indent=1)
        self.written.append(info)
        return info

    # ---- sim-thread sampler -------------------------------------------------
    def _burst(self, op: str, addr: int, length: int, size: int) -> None:
        lines, meta = self._lines, self._meta
        if lines is None or meta is None:
            return
        beat_bytes = 1 << size
        tick = len(lines)
        for i in range(length + 1):
            lines.append(f"{tick + i} {op} {addr + i * beat_bytes}\n")
        if meta["first_cycle"] < 0:
            meta["first_cycle"] = self._cycle
        meta["last_cycle"] = self._cycle
        meta[f"{'st' if op == 'ST' else 'ld'}_beats"] += length + 1
        meta[f"{'st' if op == 'ST' else 'ld'}_bursts"] += 1

    async def run(self) -> None:
        awv, awr, awa, awl, aws = self._aw
        arv, arr, ara, arl, ars = self._ar
        while True:
            await RisingEdge(self._clk)
            self._cycle += 1
            if self._lines is None:
                continue
            if int(awv.value) and int(awr.value):
                self._burst("ST", int(awa.value), int(awl.value), int(aws.value))
            if int(arv.value) and int(arr.value):
                self._burst("LD", int(ara.value), int(arl.value), int(ars.value))
