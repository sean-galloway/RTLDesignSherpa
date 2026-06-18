# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# MonbusGroupHarness -- unified, DUT-agnostic test collateral for the
# monbus_<p1>_<p2>_group family (p1 = err-drain READ side, p2 = trace
# master-WRITE side; each AXIL or AXI4). One implementation shared across
# the bridge monitor tests and the val/amba monbus-group TBs.
#
# All DUT specifics (clock, signal prefixes, the hierarchy node carrying
# err_fifo_count/write_fifo_count/*_full, and the IRQ handle) are injected
# via the constructor -- nothing here is bridge- or val-specific.
#
# Responsibilities:
#   * drain (err-FIFO read) side  -- drive AR/R, pop 64-bit beats, reassemble
#     3-beat records, parse via TBClasses.monbus.parse. Read rate is
#     throttle-able (starve the drain to fill the err FIFO).
#   * trace (master-write) side   -- consume awvalid/wvalid by driving
#     awready/wready/bvalid, capture (addr,data) beats in order, reassemble
#     via parse_stream. wready is throttle-able (stall the bulk drain to
#     fill the write FIFO).
#   * probes/watch                -- err/write fifo count+full, IRQ rising edge.
#
# Decode is delegated entirely to the existing TBClasses.monbus library
# (parse / parse_stream); this class adds only the wire-level orchestration.

import random

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.monbus import parse

from .monbus_group_scoreboard import BeatLayout, BeatOrder, MonbusGroupStats


class MonbusGroupHarness:
    def __init__(
        self,
        dut,
        clock,
        *,
        drain_proto: str,
        trace_proto: str,
        drain_prefix: str,
        trace_prefix: str,
        group_node=None,
        irq_sig=None,
        block_node=None,
        data_width: int = 64,
        addr_width: int = 32,
        id_width: int = 8,
        layout_drain: BeatLayout = None,
        layout_trace: BeatLayout = None,
        log=None,
    ) -> None:
        assert drain_proto in ("axil", "axi4"), drain_proto
        assert trace_proto in ("axil", "axi4"), trace_proto
        self.dut = dut
        self.clock = clock
        self.drain_proto = drain_proto
        self.trace_proto = trace_proto
        self.drain_prefix = drain_prefix
        self.trace_prefix = trace_prefix
        self.group_node = group_node if group_node is not None else dut
        self.irq_sig = irq_sig if irq_sig is not None else getattr(dut, "irq_out", None)
        self.block_node = block_node
        self.data_width = data_width
        self.addr_width = addr_width
        self.id_width = id_width
        self.layout_drain = layout_drain or BeatLayout(order=BeatOrder.LO_HI_TS)
        self.layout_trace = layout_trace or BeatLayout(order=BeatOrder.TS_HI_LO)
        self.log = log

        self._mask = (1 << data_width) - 1
        self.received_packets = []
        self._trace_beats = []           # captured (addr, data) in write order
        self._trace_bursts = []          # per-burst {addr,awlen,awsize,awburst,beats}
        self.stats = MonbusGroupStats()

        # throttle controls
        self._trace_ready_prob = 1.0     # P(wready==1) per cycle
        self._drain_gap_rand = None      # FlexRandomizer producing inter-read gap

        # background task handles
        self._trace_task = None
        self._fifo_task = None
        self._irq_task = None
        self._stop = {"trace": False, "fifo": False, "irq": False}
        self._rng = random.Random(0xB00B)

    # ------------------------------------------------------------------ #
    # signal access
    # ------------------------------------------------------------------ #
    def _sig(self, prefix, name):
        return getattr(self.dut, prefix + name, None)

    @staticmethod
    def _set(handle, value):
        if handle is not None:
            handle.value = value

    @staticmethod
    def _get(handle):
        try:
            return int(handle.value)
        except (ValueError, AttributeError, TypeError):
            return None

    # ------------------------------------------------------------------ #
    # drain (err-FIFO read) side
    # ------------------------------------------------------------------ #
    async def drain_read_beat(self, addr: int = 0x0, *, timeout_cycles: int = 200) -> int:
        """One drain read = one 64-bit beat popped from the err FIFO."""
        p = self.drain_prefix
        clk = self.clock
        self._set(self._sig(p, "arvalid"), 1)
        self._set(self._sig(p, "araddr"), addr)
        self._set(self._sig(p, "arprot"), 0)
        if self.drain_proto == "axi4":
            self._set(self._sig(p, "arlen"), 0)
            self._set(self._sig(p, "arsize"), (self.data_width // 8).bit_length() - 1)
            self._set(self._sig(p, "arburst"), 1)
            self._set(self._sig(p, "arid"), 0)
        self._set(self._sig(p, "rready"), 1)

        arready = self._sig(p, "arready")
        for _ in range(timeout_cycles):
            await RisingEdge(clk)
            if self._get(arready) == 1:
                break
        else:
            raise TimeoutError(f"{p}ar handshake timeout (addr=0x{addr:08x})")
        self._set(self._sig(p, "arvalid"), 0)

        rvalid = self._sig(p, "rvalid")
        rdata_h = self._sig(p, "rdata")
        for _ in range(timeout_cycles):
            if self._get(rvalid) == 1:
                rdata = self._get(rdata_h) & self._mask
                break
            await RisingEdge(clk)
        else:
            raise TimeoutError(f"{p}r handshake timeout (addr=0x{addr:08x})")
        await RisingEdge(clk)
        self._set(self._sig(p, "rready"), 0)
        self.stats.drain_reads += 1
        self.stats.drain_beats += 1
        return rdata

    async def drain_read_burst(self, burst_len: int, *, addr: int = 0x0,
                               arid: int = 0, timeout_cycles: int = 400):
        """Issue ONE AXI4 read burst of `burst_len` beats on the (axi4) drain
        port and return a list of (rdata, rlast, rid) per beat -- so callers
        can assert burst shape (rid constant, rlast only on the final beat).
        Only meaningful for drain_proto='axi4'."""
        assert self.drain_proto == "axi4", "drain_read_burst requires axi4 drain"
        p = self.drain_prefix
        clk = self.clock
        self._set(self._sig(p, "arid"), arid)
        self._set(self._sig(p, "araddr"), addr)
        self._set(self._sig(p, "arlen"), burst_len - 1)
        self._set(self._sig(p, "arsize"), (self.data_width // 8).bit_length() - 1)
        self._set(self._sig(p, "arburst"), 1)             # INCR
        self._set(self._sig(p, "arvalid"), 1)
        arready = self._sig(p, "arready")
        for _ in range(timeout_cycles):
            await RisingEdge(clk)
            if self._get(arready) == 1:
                break
        else:
            raise TimeoutError(f"{p}ar burst handshake timeout")
        self._set(self._sig(p, "arvalid"), 0)

        rvalid = self._sig(p, "rvalid")
        rdata_h = self._sig(p, "rdata")
        rlast_h = self._sig(p, "rlast")
        rid_h = self._sig(p, "rid")
        self._set(self._sig(p, "rready"), 1)
        out = []
        guard = 0
        while len(out) < burst_len and guard < timeout_cycles:
            await ReadOnly()
            if self._get(rvalid) == 1:
                out.append((self._get(rdata_h) & self._mask,
                            self._get(rlast_h), self._get(rid_h)))
            await RisingEdge(clk)
            guard += 1
        self._set(self._sig(p, "rready"), 0)
        await RisingEdge(clk)
        self.stats.drain_reads += 1
        self.stats.drain_beats += len(out)
        return out

    def set_drain_read_randomizer(self, randomizer) -> None:
        """FlexRandomizer whose .next() yields an inter-record gap (first value)."""
        self._drain_gap_rand = randomizer

    async def _drain_gap(self, gap_cycles):
        n = gap_cycles
        if n is None and self._drain_gap_rand is not None:
            vals = self._drain_gap_rand.next()
            n = next(iter(vals.values())) if vals else 0
        for _ in range(int(n or 0)):
            await RisingEdge(self.clock)

    async def drain_records(self, n_records: int, *, base_addr: int = 0x0,
                            addr_step: int = 0x8, gap_cycles=None):
        """Pop n_records*beats_per_record beats, reassemble per layout_drain,
        parse, and append to received_packets. Returns the new packets."""
        out = []
        bpr = self.layout_drain.beats_per_record
        for _ in range(n_records):
            beats = []
            for b in range(bpr):
                beats.append(await self.drain_read_beat(base_addr + b * addr_step))
            pkt = self._reassemble(beats, self.layout_drain)
            if pkt is not None:
                out.append(pkt)
                self.received_packets.append(pkt)
                self.stats.records_parsed += 1
            else:
                self.stats.skipped_zero_records += 1
            await self._drain_gap(gap_cycles)
        return out

    def start_drain_pump(self, *, record_gap_cycles: int = 64, base_addr: int = 0x0,
                         addr_step: int = 0x8) -> None:
        """Spawn a background drainer that pops one err-FIFO record every
        record_gap_cycles. Used by err-FIFO backpressure stress: a drain
        rate slower than the packet-production rate lets err_fifo_count
        climb toward full and regulate via block_ready, without the total
        deadlock that fully starving the drain would cause."""
        self._stop["pump"] = False
        self._pump_task = cocotb.start_soon(self._drain_pump(record_gap_cycles,
                                                             base_addr, addr_step))

    def stop_drain_pump(self) -> None:
        self._stop["pump"] = True

    async def _drain_pump(self, gap, base_addr, addr_step):
        while not self._stop.get("pump", False):
            try:
                await self.drain_records(1, base_addr=base_addr, addr_step=addr_step)
            except TimeoutError:
                pass
            for _ in range(gap):
                if self._stop.get("pump", False):
                    return
                await RisingEdge(self.clock)

    async def drain_until_empty(self, *, base_addr: int = 0x0, addr_step: int = 0x8,
                                max_records: int = 4096):
        """Drain err-FIFO records until err_fifo_count reaches 0 (or the
        max_records guard trips). Returns the packets drained."""
        out = []
        n = 0
        while self.err_fifo_count() > 0 and n < max_records:
            out.extend(await self.drain_records(1, base_addr=base_addr, addr_step=addr_step))
            n += 1
        return out

    def _reassemble(self, beats, layout):
        """Reassemble 3 beats into a MonitorPacket per the beat order. Returns
        None for an all-zero (padding) record."""
        if layout.order == BeatOrder.LO_HI_TS:
            lo, hi = beats[0], beats[1]
        else:  # TS_HI_LO
            hi, lo = beats[1], beats[2]
        if (hi & self._mask) == 0 and (lo & self._mask) == 0:
            return None
        raw = ((hi & self._mask) << 64) | (lo & self._mask)
        return parse(raw)

    # ------------------------------------------------------------------ #
    # trace (master-write) consume side
    # ------------------------------------------------------------------ #
    def set_trace_ready_prob(self, prob: float) -> None:
        """P(wready==1) per cycle. 1.0 = never stall; small = heavy backpressure."""
        self._trace_ready_prob = max(0.0, min(1.0, float(prob)))

    def set_trace_ready_randomizer(self, randomizer) -> None:
        """Alternative throttle: a FlexRandomizer whose .next() yields a per-cycle
        ready (non-zero => assert). Mutually exclusive with set_trace_ready_prob."""
        self._trace_ready_rand = randomizer
        self._trace_ready_prob = None

    def _trace_ready(self) -> int:
        if self._trace_ready_prob is None and getattr(self, "_trace_ready_rand", None):
            vals = self._trace_ready_rand.next()
            return 1 if (vals and next(iter(vals.values()))) else 0
        return 1 if self._rng.random() < self._trace_ready_prob else 0

    def start_trace_consumer(self, *, ready_prob: float = None) -> None:
        if ready_prob is not None:
            self.set_trace_ready_prob(ready_prob)
        self._stop["trace"] = False
        self._trace_task = cocotb.start_soon(self._trace_consumer())

    def stop_trace_consumer(self) -> None:
        self._stop["trace"] = True

    async def _trace_consumer(self):
        try:
            await self._trace_consumer_body()
        except Exception as e:  # noqa: BLE001 - surface silent start_soon crashes
            if self.log:
                self.log.error(f"trace consumer crashed: {e!r}")
            raise

    async def _trace_consumer_body(self):
        # Single-outstanding AXIL/AXI4 slave-write consumer: accept one AW,
        # capture its W beat(s) (wready throttled for backpressure), then
        # complete B, before accepting the next AW. Driving awready only when
        # idle enforces one-in-flight and keeps the master FSM unwedged.
        p = self.trace_prefix
        clk = self.clock
        awvalid = self._sig(p, "awvalid")
        awaddr = self._sig(p, "awaddr")
        awlen = self._sig(p, "awlen")            # axi4 only (None for axil)
        awsize = self._sig(p, "awsize")          # axi4 only
        awburst = self._sig(p, "awburst")        # axi4 only
        wvalid = self._sig(p, "wvalid")
        wdata = self._sig(p, "wdata")
        wlast = self._sig(p, "wlast")            # axi4 only (None for axil)
        bready = self._sig(p, "bready")
        cur_addr = 0
        cur_awlen = 0
        cur_awsize = None
        cur_awburst = None
        cur_beats = []                           # data beats of the current burst
        cur_wlast = []                           # wlast flag per captured beat
        aw_seen = False
        w_done = False                           # W (or W burst) captured
        self._set(self._sig(p, "bresp"), 0)
        self._set(self._sig(p, "bvalid"), 0)
        self._set(self._sig(p, "awready"), 1)
        while not self._stop["trace"]:
            rdy = self._trace_ready()
            self._set(self._sig(p, "wready"), rdy)
            self._set(self._sig(p, "awready"), 0 if aw_seen else 1)
            in_b = aw_seen and w_done
            self._set(self._sig(p, "bvalid"), 1 if in_b else 0)
            if rdy == 0:
                self.stats.trace_backpressure_cycles += 1
            await RisingEdge(clk)
            # B handshake first (completes the prior transaction -> burst)
            if in_b and self._get(bready) == 1:
                self._trace_bursts.append({
                    'addr': cur_addr, 'awlen': cur_awlen,
                    'awsize': cur_awsize, 'awburst': cur_awburst,
                    'beats': list(cur_beats), 'wlast_flags': list(cur_wlast),
                })
                aw_seen = False
                w_done = False
                cur_beats = []
                cur_wlast = []
                self._set(self._sig(p, "bvalid"), 0)
            # AW handshake (only when idle -> awready was 1)
            if not aw_seen and self._get(awvalid) == 1:
                cur_addr = self._get(awaddr) or 0
                cur_awlen = self._get(awlen) or 0
                cur_awsize = self._get(awsize)
                cur_awburst = self._get(awburst)
                self.stats.trace_aw += 1
                aw_seen = True
            # W handshake (throttled by wready=rdy)
            if aw_seen and not w_done and self._get(wvalid) == 1 and rdy == 1:
                d = self._get(wdata) & self._mask
                wl = 1 if wlast is None else (self._get(wlast) or 0)
                self._trace_beats.append((cur_addr, d))
                self.stats.trace_beats += 1
                cur_beats.append(d)
                cur_wlast.append(wl)
                if wl == 1:
                    w_done = True
        self._set(self._sig(p, "wready"), 0)
        self._set(self._sig(p, "bvalid"), 0)
        self._set(self._sig(p, "awready"), 0)

    @property
    def trace_beats(self):
        return list(self._trace_beats)

    @property
    def trace_bursts(self):
        """Per-burst captures on the master-write port, in completion order.
        Each is a dict {addr, awlen, awsize, awburst, beats:[data...],
        wlast_flags:[0..1]}. For an AXIL trace port every 'burst' is a single
        beat (awlen=0); for AXI4 it groups awlen+1 W beats with wlast timing."""
        return [dict(b) for b in self._trace_bursts]

    def parse_trace_records(self):
        """Reassemble captured trace wdata into records and append the decoded
        packets to received_packets. Reassembly honours layout_trace.order
        (the bridge master-write path is LO_HI_TS, same as its drain path);
        all-zero (padding) records are skipped. Returns the new packets."""
        words = [d for (_a, d) in self._trace_beats]
        bpr = self.layout_trace.beats_per_record
        out = []
        for i in range(0, len(words) - bpr + 1, bpr):
            pkt = self._reassemble(words[i:i + bpr], self.layout_trace)
            if pkt is None:
                self.stats.skipped_zero_records += 1
                continue
            out.append(pkt)
            self.received_packets.append(pkt)
            self.stats.records_parsed += 1
        return out

    # ------------------------------------------------------------------ #
    # FIFO / IRQ probes
    # ------------------------------------------------------------------ #
    def err_fifo_count(self) -> int:
        return self._get(getattr(self.group_node, "err_fifo_count", None)) or 0

    def write_fifo_count(self) -> int:
        return self._get(getattr(self.group_node, "write_fifo_count", None)) or 0

    def err_fifo_full(self) -> bool:
        return bool(self._get(getattr(self.group_node, "err_fifo_full", None)) or 0)

    def write_fifo_full(self) -> bool:
        return bool(self._get(getattr(self.group_node, "write_fifo_full", None)) or 0)

    def start_fifo_monitor(self) -> None:
        self._stop["fifo"] = False
        self._fifo_task = cocotb.start_soon(self._fifo_monitor())

    def stop_fifo_monitor(self) -> None:
        self._stop["fifo"] = True

    async def _fifo_monitor(self):
        block_sig = getattr(self.block_node, "w_block_ready", None) if self.block_node else None
        while not self._stop["fifo"]:
            await RisingEdge(self.clock)
            ec, wc = self.err_fifo_count(), self.write_fifo_count()
            if ec > self.stats.max_err_fifo_count:
                self.stats.max_err_fifo_count = ec
            if wc > self.stats.max_write_fifo_count:
                self.stats.max_write_fifo_count = wc
            if self.err_fifo_full():
                self.stats.err_fifo_full_seen = True
            if self.write_fifo_full():
                self.stats.write_fifo_full_seen = True
            if block_sig is not None and self._get(block_sig) == 0:
                self.stats.block_ready_gated = True

    def start_irq_watch(self) -> None:
        self._stop["irq"] = False
        self._irq_task = cocotb.start_soon(self._irq_watch())

    def stop_irq_watch(self) -> None:
        self._stop["irq"] = True

    async def _irq_watch(self):
        prev, cyc = 0, 0
        while not self._stop["irq"]:
            await RisingEdge(self.clock)
            cyc += 1
            cur = self._get(self.irq_sig)
            if cur is None:
                continue
            if cur == 1 and prev == 0:
                self.stats.irq_rising_edges += 1
                if self.stats.irq_first_cycle is None:
                    self.stats.irq_first_cycle = cyc
            prev = cur

    @property
    def irq_asserted(self) -> bool:
        return self.stats.irq_first_cycle is not None

    @property
    def irq_first_cycle(self):
        return self.stats.irq_first_cycle

    # ------------------------------------------------------------------ #
    # aggregation
    # ------------------------------------------------------------------ #
    def find_packets(self, **criteria):
        return [p for p in self.received_packets if p.matches(**criteria)]

    def count_packets(self, **criteria) -> int:
        return sum(1 for p in self.received_packets if p.matches(**criteria))

    def clear(self) -> None:
        self.received_packets = []
        self._trace_beats = []
        self._trace_bursts = []
        self.stats = MonbusGroupStats()

    def get_stats(self) -> MonbusGroupStats:
        return self.stats
