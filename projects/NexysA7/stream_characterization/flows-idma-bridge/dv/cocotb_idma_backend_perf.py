"""
Cosim perf harness for the PULP iDMA rw_axi backend.

Drives the backend's 1D request interface directly (src, dst, length) and serves
its AXI4 manager from a lightweight cocotb memory model with a configurable
per-response delay -- the same knob the STREAM characterization sweeps. Bus
utilization is measured the same way the STREAM axi4_dma_observer does:
  datapath_util = productive_beats / (last_beat_cycle - first_beat_cycle + 1)
where a productive beat is a cycle with valid && ready on the data channel.

This isolates iDMA's datapath (the headline util/throughput axis) for an
apples-to-apples comparison with STREAM, without the desc64/reg frontend.

Env knobs (set by the pytest wrapper):
  IDMA_XFER_BEATS   transfer length in 128-bit beats (default 256)
  IDMA_RESP_DELAY   per-response hold cycles on R and B (default 0)
  IDMA_MAX_LLEN     req_*_max_llen_i [0..7], caps AXI burst length (default 7)
"""
import os
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.queue import Queue

DW_BITS   = 128
BYTES_PB  = DW_BITS // 8          # 16 bytes / beat
SRC_BASE  = 0x8000_0000
DST_BASE  = 0x9000_0000
INCR      = 0b01


def _pattern(addr: int) -> int:
    """Deterministic read data for a given byte address (per-beat fill)."""
    beat = (addr // BYTES_PB) & 0xFF
    return int.from_bytes(bytes([beat]) * BYTES_PB, "little")


class AxiMemSlave:
    """Minimal AXI4 slave + memory for the iDMA manager port. In-order per the
    single-ID traffic iDMA generates; honors a fixed per-response delay."""

    def __init__(self, dut, resp_delay=0):
        self.dut = dut
        self.resp_delay = resp_delay
        self.store = {}                 # byte-addr -> 128b word written
        self.ar_q = Queue()
        self.aw_q = Queue()
        self.w_q = Queue()
        # perf counters
        self.r_beats = 0
        self.w_beats = 0
        self.r_first = self.r_last = -1
        self.w_first = self.w_last = -1
        self.cyc = 0

    # ---- channel drivers ----------------------------------------------
    async def _cycle_counter(self):
        while True:
            await RisingEdge(self.dut.clk_i)
            self.cyc += 1

    async def ar_accept(self):
        d = self.dut
        d.axi_ar_ready_i.value = 1
        while True:
            await RisingEdge(d.clk_i)
            if d.axi_ar_valid_o.value and d.axi_ar_ready_i.value:
                # Stamp the arrival cycle so the memory imposes latency as an
                # OVERLAPPING per-response pipe (data ready at arrival+L), not a
                # serial per-burst wait. This is the Little's-Law latency model
                # STREAM's axi_response_delay uses: with multiple ARs in flight,
                # their dwell times overlap, so sustained BW = min(1, in_flight/L)
                # and the DMA's outstanding limit is what throttles.
                await self.ar_q.put((int(d.axi_ar_addr_o.value),
                                     int(d.axi_ar_len_o.value),
                                     int(d.axi_ar_id_o.value),
                                     self.cyc))

    async def r_serve(self):
        d = self.dut
        d.axi_r_valid_i.value = 0
        while True:
            addr, length, rid, t_arr = await self.ar_q.get()
            ready = t_arr + self.resp_delay
            while self.cyc < ready:
                await RisingEdge(d.clk_i)
            for beat in range(length + 1):
                d.axi_r_valid_i.value = 1
                d.axi_r_data_i.value = _pattern(addr + beat * BYTES_PB)
                d.axi_r_id_i.value = rid
                d.axi_r_resp_i.value = 0
                d.axi_r_last_i.value = 1 if beat == length else 0
                await RisingEdge(d.clk_i)
                while not d.axi_r_ready_o.value:
                    await RisingEdge(d.clk_i)
                self.r_beats += 1
                if self.r_first < 0:
                    self.r_first = self.cyc
                self.r_last = self.cyc
            d.axi_r_valid_i.value = 0

    async def aw_accept(self):
        d = self.dut
        d.axi_aw_ready_i.value = 1
        while True:
            await RisingEdge(d.clk_i)
            if d.axi_aw_valid_o.value and d.axi_aw_ready_i.value:
                await self.aw_q.put((int(d.axi_aw_addr_o.value),
                                     int(d.axi_aw_len_o.value),
                                     int(d.axi_aw_id_o.value),
                                     self.cyc))

    async def w_accept(self):
        d = self.dut
        d.axi_w_ready_i.value = 1
        while True:
            await RisingEdge(d.clk_i)
            if d.axi_w_valid_o.value and d.axi_w_ready_i.value:
                self.w_beats += 1
                if self.w_first < 0:
                    self.w_first = self.cyc
                self.w_last = self.cyc
                await self.w_q.put((int(d.axi_w_data_o.value),
                                    int(d.axi_w_last_o.value)))

    async def b_serve(self):
        d = self.dut
        d.axi_b_valid_i.value = 0
        while True:
            addr, length, wid, t_arr = await self.aw_q.get()
            for beat in range(length + 1):
                data, wlast = await self.w_q.get()
                self.store[addr + beat * BYTES_PB] = data
            ready = t_arr + self.resp_delay   # overlapping AW->B latency
            while self.cyc < ready:
                await RisingEdge(d.clk_i)
            d.axi_b_valid_i.value = 1
            d.axi_b_id_i.value = wid
            d.axi_b_resp_i.value = 0
            await RisingEdge(d.clk_i)
            while not d.axi_b_ready_o.value:
                await RisingEdge(d.clk_i)
            d.axi_b_valid_i.value = 0

    def start(self):
        for c in (self._cycle_counter, self.ar_accept, self.r_serve,
                  self.aw_accept, self.w_accept, self.b_serve):
            cocotb.start_soon(c())

    # ---- metrics ------------------------------------------------------
    def util(self):
        r_win = (self.r_last - self.r_first + 1) if self.r_last >= 0 else 0
        w_win = (self.w_last - self.w_first + 1) if self.w_last >= 0 else 0
        return {
            "r_beats": self.r_beats, "w_beats": self.w_beats,
            "r_util": (self.r_beats / r_win) if r_win else 0.0,
            "w_util": (self.w_beats / w_win) if w_win else 0.0,
            "r_window": r_win, "w_window": w_win,
        }


def _init_req(d):
    for sig, val in [
        ("req_valid_i", 0), ("req_last_i", 1),
        ("req_src_protocol_i", 0), ("req_dst_protocol_i", 0),   # AXI
        ("req_axi_id_i", 0),
        ("req_src_burst_i", INCR), ("req_dst_burst_i", INCR),
        ("req_src_cache_i", 0), ("req_dst_cache_i", 0),
        ("req_src_lock_i", 0), ("req_dst_lock_i", 0),
        ("req_src_prot_i", 0), ("req_dst_prot_i", 0),
        ("req_src_qos_i", 0), ("req_dst_qos_i", 0),
        ("req_src_region_i", 0), ("req_dst_region_i", 0),
        ("req_decouple_aw_i", 1), ("req_decouple_rw_i", 1),
        # reduce_len=1 makes req_*_max_llen cap the AXI burst length to
        # 2^max_llen beats (legalizer page = 2^(OffsetWidth+max_llen) bytes).
        # max_llen=4 -> 16-beat bursts, matching STREAM's burst_len=16.
        ("req_src_reduce_len_i", 1), ("req_dst_reduce_len_i", 1),
        ("rsp_ready_i", 1), ("eh_req_valid_i", 0), ("test_i", 0),
    ]:
        getattr(d, sig).value = val


@cocotb.test()
async def cocotb_test_idma_backend_perf(dut):
    beats = int(os.environ.get("IDMA_XFER_BEATS", "256"))
    resp_delay = int(os.environ.get("IDMA_RESP_DELAY", "0"))
    max_llen = int(os.environ.get("IDMA_MAX_LLEN", "4"))   # 2^4 = 16-beat bursts
    length_bytes = beats * BYTES_PB

    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    _init_req(dut)
    dut.rst_ni.value = 0
    await ClockCycles(dut.clk_i, 10)
    dut.rst_ni.value = 1
    await ClockCycles(dut.clk_i, 5)

    mem = AxiMemSlave(dut, resp_delay=resp_delay)
    mem.start()

    # Issue one 1D transfer: src -> dst, length bytes.
    dut.req_length_i.value = length_bytes
    dut.req_src_addr_i.value = SRC_BASE
    dut.req_dst_addr_i.value = DST_BASE
    dut.req_src_max_llen_i.value = max_llen
    dut.req_dst_max_llen_i.value = max_llen
    dut.req_valid_i.value = 1
    await RisingEdge(dut.clk_i)
    while not dut.req_ready_o.value:
        await RisingEdge(dut.clk_i)
    dut.req_valid_i.value = 0

    # Wait for completion (rsp_valid) or timeout.
    for _ in range(beats * 20 + 2000):
        await RisingEdge(dut.clk_i)
        if dut.rsp_valid_o.value:
            break
    else:
        raise cocotb.result.TestFailure("iDMA backend did not complete")

    await ClockCycles(dut.clk_i, 20)
    u = mem.util()
    rec = {
        "beats": beats, "resp_delay": resp_delay, "max_llen": max_llen,
        "bytes": length_bytes, **u,
    }
    line = (f"iDMA backend perf: beats={beats} resp_delay={resp_delay} "
            f"max_llen={max_llen} | R util={u['r_util']*100:.1f}% "
            f"({u['r_beats']}/{u['r_window']}) W util={u['w_util']*100:.1f}% "
            f"({u['w_beats']}/{u['w_window']})")
    dut._log.info(line)

    # Persist a perf record (JSONL) so the pytest layer / sweeps can collect it,
    # independent of cocotb log capture. Also drop a human-readable .txt.
    out = os.environ.get("IDMA_PERF_OUT")
    if out:
        import json
        with open(out, "a") as f:
            f.write(json.dumps(rec) + "\n")
        with open(out + ".txt", "a") as f:
            f.write(line + "\n")

    assert u["r_beats"] == beats, f"R beat count {u['r_beats']} != {beats}"
    assert u["w_beats"] == beats, f"W beat count {u['w_beats']} != {beats}"
