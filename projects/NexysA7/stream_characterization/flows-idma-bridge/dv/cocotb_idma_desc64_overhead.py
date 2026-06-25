"""
Descriptor-fetch overhead of the iDMA desc64 frontend.

Programs a descriptor-chain head address into the desc64 register, serves the
descriptor reads from a cocotb memory, and times kick -> first emitted 1D
request (and the per-descriptor cadence down a chain). This is the iDMA analog
of STREAM's descriptor-engine startup cost -- the part the backend-only perf
cosim omits.

Descriptor: 256 bits, packed { flags[255:224], length[223:192], next[191:128],
src[127:64], dest[63:0] }. AXI data width is 64 (desc64 synth pkg), so a
descriptor is 4 beats:
  beat0 = dest, beat1 = src, beat2 = next, beat3 = (flags<<32)|length
next == 0xFFFF_FFFF_FFFF_FFFF marks the last descriptor.
"""
import os
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

LAST = 0xFFFF_FFFF_FFFF_FFFF
DESC_BASE = 0x1_0000
SRC_BASE = 0x8000_0000
DST_BASE = 0x9000_0000
DESC_ADDR_REG = 0x0


def descriptor_beats(length, src, dst, nxt):
    """4x 64-bit beats for one descriptor, MSB-word first (the reader reads the
    packed struct's first member -- flags/length -- from the lowest address):
      beat0 = {flags<<32 | length}, beat1 = next, beat2 = src, beat3 = dest."""
    M = 0xFFFFFFFFFFFFFFFF
    return [((0 << 32) | (length & 0xFFFFFFFF)) & M,  # flags=0
            nxt & M,
            src & M,
            dst & M]


def build_chain(n, length_bytes):
    """Return {byte_addr: 64b word} memory image for an n-descriptor chain."""
    mem = {}
    for i in range(n):
        a = DESC_BASE + i * 32
        nxt = LAST if i == n - 1 else (DESC_BASE + (i + 1) * 32)
        beats = descriptor_beats(length_bytes, SRC_BASE + i * length_bytes,
                                 DST_BASE + i * length_bytes, nxt)
        for b, word in enumerate(beats):
            mem[a + b * 8] = word
    return mem


class DescMem:
    def __init__(self, dut, image):
        self.dut = dut
        self.mem = image
        self.ar_seen = []

    async def serve(self):
        d = self.dut
        d.ar_ready_i.value = 1
        d.r_valid_i.value = 0
        while True:
            await RisingEdge(d.clk_i)
            if d.ar_valid_o.value and d.ar_ready_i.value:
                addr = int(d.ar_addr_o.value)
                length = int(d.ar_len_o.value)
                self.ar_seen.append((addr, length))
                for beat in range(length + 1):
                    word = self.mem.get(addr + beat * 8, 0)
                    d.r_valid_i.value = 1
                    d.r_data_i.value = word
                    d.r_id_i.value = int(d.ar_id_o.value)
                    d.r_resp_i.value = 0
                    d.r_last_i.value = 1 if beat == length else 0
                    await RisingEdge(d.clk_i)
                    while not d.r_ready_o.value:
                        await RisingEdge(d.clk_i)
                d.r_valid_i.value = 0


async def reg_write(dut, addr, data):
    dut.reg_addr_i.value = addr
    dut.reg_wdata_i.value = data
    dut.reg_write_i.value = 1
    dut.reg_valid_i.value = 1
    await RisingEdge(dut.clk_i)
    while not dut.reg_ready_o.value:
        await RisingEdge(dut.clk_i)
    dut.reg_valid_i.value = 0
    dut.reg_write_i.value = 0


@cocotb.test()
async def cocotb_test_idma_desc64_overhead(dut):
    # Frontend-only: the descriptor-fetch START overhead (kick -> first emitted
    # 1D request) is the headline. Multi-descriptor *cadence* needs the real
    # backend's completion feedback (desc64's speculative-prefetch protocol), so
    # the chain is best-effort here; default to a single descriptor.
    n = int(os.environ.get("IDMA_DESC_COUNT", "1"))
    length_bytes = int(os.environ.get("IDMA_DESC_LEN", "4096"))

    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    for s in ("reg_valid_i", "reg_write_i", "reg_addr_i", "reg_wdata_i"):
        getattr(dut, s).value = 0
    dut.rst_ni.value = 0
    await ClockCycles(dut.clk_i, 10)
    dut.rst_ni.value = 1
    await ClockCycles(dut.clk_i, 5)

    mem = DescMem(dut, build_chain(n, length_bytes))
    cocotb.start_soon(mem.serve())

    # Count cycles from kick to each emitted 1D request.
    reqs = []
    cyc = {"n": 0}

    async def counter():
        while True:
            await RisingEdge(dut.clk_i)
            cyc["n"] += 1
            if dut.idma_req_valid_o.value:
                reqs.append((cyc["n"], int(dut.idma_req_src_o.value),
                             int(dut.idma_req_dst_o.value),
                             int(dut.idma_req_length_o.value)))
    cocotb.start_soon(counter())

    t_kick = cyc["n"]
    await reg_write(dut, DESC_ADDR_REG, DESC_BASE)

    # Wait for the first request (and any further chain advance), then settle.
    for _ in range(4000):
        await RisingEdge(dut.clk_i)
        if len({r[0] for r in reqs}) >= n:
            break

    uniq = []
    seen_c = set()
    for c, s, d_, l in reqs:
        if c not in seen_c:
            seen_c.add(c)
            uniq.append((c, s, d_, l))
    dut._log.info(f"desc64 overhead: chain={n} len={length_bytes}B "
                  f"ARs={len(mem.ar_seen)} reqs={len(uniq)}")
    for i, (c, s, d_, l) in enumerate(uniq[:n]):
        dut._log.info(f"  req[{i}] @cyc {c-t_kick}: src=0x{s:08X} dst=0x{d_:08X} len={l}")

    assert len(uniq) >= 1, f"no 1D request emitted (ARs: {mem.ar_seen[:4]})"
    first = uniq[0][0] - t_kick
    cadence = (uniq[-1][0] - uniq[0][0]) / (len(uniq) - 1) if len(uniq) > 1 else 0
    out = os.environ.get("IDMA_PERF_OUT")
    if out:
        import json
        with open(out, "a") as f:
            f.write(json.dumps({"chain": n, "len_bytes": length_bytes,
                                "first_req_cyc": first, "per_desc_cyc": cadence,
                                "ars": len(mem.ar_seen)}) + "\n")
        with open(out + ".txt", "a") as f:
            f.write(f"desc64 chain={n} len={length_bytes}B: first req @ {first} cyc, "
                    f"~{cadence:.1f} cyc/descriptor\n")
    # Verify first descriptor decoded correctly.
    assert uniq[0][1] == SRC_BASE and uniq[0][3] == length_bytes, \
        f"first req mismatch: {uniq[0]}"
