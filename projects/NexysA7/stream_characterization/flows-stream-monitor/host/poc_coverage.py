#!/usr/bin/env python3
"""R6 -- on-silicon AGENT-RESOLVED coverage: DMA -> AddrMatch -> profile tally.

The end-to-end proof the monitors-on cosim was too slow to reach. Replicates the
cosim run_dma_test monitor-routing recipe by-name on the host (stream_addrs.A /
harness_addrs.H), then runs a small DMA and sweeps the STREAM tally's dense bins.
A match-all DEBUG address range on rd+wr means every accepted AR/AW emits an
AddrMatch (type 8) packet; the profile CAM resolves rd (agent 9) -> bin 0 and
wr (agent 10) -> bin 1. PASS = both bins > 0.

Critical config (all from the cosim, see flows-stream-monitor/dv/tests/test_stream_mon.py):
  * profile CAM loaded over the cfg slave (survives the SOFT_RESET)
  * SOFT_RESET first (it wipes the STREAM register block)
  * per-monitor: PKT_MASK=0xFEF0 (allow AddrMatch), MASK3=0 (clear ADDR_MASK),
    ENABLE=0x0F (COMPL+IRQ), ERR_CFG=0 (BULK_TRACE -> routes to the tally slot)
  * match-all range0 (DEBUG) on rd (MON+0x200/0x220) + wr (MON+0x230/0x250),
    ctrl=0x31 (RANGE_EN|CHECK_EN|MATCH_EN) -- programmed AFTER the reset
  * FREEZE_TRACE after the DMA flushes the tally cache into the count SRAM

Usage:  source env_python && python3 poc_coverage.py [--port /dev/ttyUSB2]
"""
import os
import sys
import time
import argparse

_REPO = os.environ.get("REPO_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(__file__), *[".."] * 5))
_BRIDGE_HOST = os.path.join(
    _REPO, "projects/NexysA7/stream_characterization/flows-stream-bridge/host")
sys.path.insert(0, os.path.join(_REPO, "projects/components/converters/bin"))
sys.path.insert(0, _BRIDGE_HOST)
from uart_axi_bridge import UARTAxiBridge          # noqa: E402
from stream_addrs import A                          # noqa: E402
from harness_addrs import H                         # noqa: E402
from stream_device import build_stream_bus          # noqa: E402

STREAM_TALLY_CFG = 0x0010_0000
PROFILE_CLEAR    = 0x0100
PROFILE_ENTRY    = 0x0200
MON              = 0x1000                # MON regfile base within STREAM APB space
N_PROFILE        = 64

# The STREAM legal set (matches test_stream_mon.STREAM_PROFILE): bin0=rd AddrMatch
# (agent 9), bin1=wr AddrMatch (agent 10), bin2/3 = perf on rd/wr datapath.
STREAM_PROFILE = [(9, 0, 8, 0x01), (10, 0, 8, 0x01), (48, 4, 1, 0x01), (16, 4, 1, 0x40)]


def profile_key(agent, proto, ptype, ec):
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (ec & 0xFF))


def run(port, channel=0, xfer_bytes=256):
    bridge = UARTAxiBridge(port=port)
    stream = build_stream_bus(bridge)["stream"]

    # 1. profile CAM load over the cfg slave (persists across the soft-reset)
    bridge.write(STREAM_TALLY_CFG + PROFILE_CLEAR, 0)
    for i, tup in enumerate(STREAM_PROFILE):
        bridge.write(STREAM_TALLY_CFG + PROFILE_ENTRY + i * 4, profile_key(*tup))
    print(f"  profile: loaded {len(STREAM_PROFILE)} legal tuples")

    # 2. SOFT_RESET the STREAM register block (CTRL bit 3), then re-program it
    bridge.write(H("CTRL"), 1 << 3)

    # 3. STREAM datapath config (post-reset), match-all descriptor windows
    bridge.write(A("SCHED_CONFIG"),        0x0F)
    bridge.write(A("SCHED_TIMEOUT_CYCLES"), 0xFFFF_FFFF)
    bridge.write(A("DESCENG_CONFIG"),      0x23)
    bridge.write(A("DESCENG_ADDR0_BASE"),  0x0000_0000)
    bridge.write(A("DESCENG_ADDR0_LIMIT"), 0xFFFF_FFFF)
    bridge.write(A("DESCENG_ADDR1_BASE"),  0x0000_0000)
    bridge.write(A("DESCENG_ADDR1_LIMIT"), 0xFFFF_FFFF)
    bridge.write(A("AXI_XFER_CONFIG"),     (15) | (15 << 8))

    # 4. per-monitor: allow AddrMatch, clear ADDR_MASK, COMPL+IRQ enable,
    #    ERR_CFG=0 (BULK_TRACE) so records route to the tally ingest slot
    for pk, en, err, m3 in (
        (A("DAXMON_PKT_MASK"), A("DAXMON_ENABLE"), A("DAXMON_ERR_CFG"), A("DAXMON_MASK3")),
        (A("RDMON_PKT_MASK"),  A("RDMON_ENABLE"),  A("RDMON_ERR_CFG"),  A("RDMON_MASK3")),
        (A("WRMON_PKT_MASK"),  A("WRMON_ENABLE"),  A("WRMON_ERR_CFG"),  A("WRMON_MASK3")),
    ):
        bridge.write(pk, 0x0000_FEF0)   # ALLOW_BASIC with AddrMatch(8) bit cleared
        bridge.write(m3, 0x0)           # clear ADDR_MASK -> AddrMatch passes event stage
        bridge.write(en, 0x0F)          # MON_ENABLE_COMPL_IRQ
        bridge.write(err, 0x0)          # BULK_TRACE routing

    # 5. match-all DEBUG range0 on rd + wr -> every AR/AW emits an AddrMatch
    ctrl_val = 0x01 | (1 << 4) | (1 << 5)   # RANGE_EN | CHECK_EN | MATCH_EN
    for rbase, cbase in ((MON + 0x200, MON + 0x220), (MON + 0x230, MON + 0x250)):
        bridge.write(rbase + 0x00, 0x0000_0000)
        bridge.write(rbase + 0x04, 0xFFFF_FFFF)
        bridge.write(cbase, ctrl_val)
    print(f"  monitors: BULK_TRACE + match-all AddrMatch range (ctrl=0x{ctrl_val:02X})")

    # 6. load one descriptor into desc_ram (survives reset), enable, arm timer
    kick_addr = stream.load_chain(channel, num_descriptors=1, transfer_bytes=xfer_bytes)
    bridge.write(A("GLOBAL_CTRL"),    0x1)          # GLOBAL_EN
    bridge.write(A("CHANNEL_ENABLE"), 1 << channel)
    beats = xfer_bytes // 16
    bridge.write(H("TIMER_CTRL"), 0x1)              # CLEAR
    bridge.write(H("TIMER_EXPECTED_BEATS"), beats)

    # 7. kick (shadow the descriptor addr, then pulse KICK_GO)
    bridge.write(H(f"CH{channel}_KICK_ADDR"), kick_addr & 0xFFFF_FFFF)
    bridge.write(H("KICK_GO"), 1 << channel)
    print(f"  DMA kicked (ch{channel}, {xfer_bytes} B, kick_addr=0x{kick_addr:08X})")

    # 8. wait for the harness timer.done (bit 0)
    t0 = time.time()
    done = False
    while time.time() - t0 < 10.0:
        ts = bridge.read(H("TIMER_STATUS")) or 0
        if ts & 0x1:
            done = True
            break
        time.sleep(0.02)
    print(f"  timer {'done' if done else 'TIMEOUT'} after {time.time()-t0:.2f}s "
          f"(status=0x{bridge.read(H('TIMER_STATUS')) or 0:02X})")

    # 9. FREEZE_TRACE (bit 2) flushes the tally cache into the count SRAM
    bridge.write(H("CTRL"), 1 << 2)
    time.sleep(0.05)

    # 10. sweep the dense bins + UNEXPECTED, on BOTH tallies.
    #     The slave tally is the cosim's "working reference" -- if it counts and
    #     the STREAM one doesn't, the bug is isolated to the STREAM in-core
    #     monbus group (records never reach m_axil_mon), not the tally mechanism.
    SLAVE_TALLY_CFG = 0x0014_0000

    def sweep(base):
        return {b: v for b in range(N_PROFILE + 1)
                if (v := (bridge.read(base + b * 4) or 0))}

    dense = sweep(STREAM_TALLY_CFG)
    slave = sweep(SLAVE_TALLY_CFG)
    rd_hits, wr_hits = dense.get(0, 0), dense.get(1, 0)
    print(f"  SLAVE  dense bins = {slave}  (reference group; no legal set loaded "
          f"-> any traffic lands in UNEXPECTED[{N_PROFILE}])")
    print(f"  STREAM dense bins = {dense}")
    print(f"    bin0 rd(agent9)  = {rd_hits}")
    print(f"    bin1 wr(agent10) = {wr_hits}")
    print(f"    UNEXPECTED(64)   = {dense.get(N_PROFILE, 0)}")

    ok = rd_hits > 0 and wr_hits > 0
    print(f"\n=== R6 {'PASS' if ok else 'FAIL'}: "
          f"{'per-agent AddrMatch resolved on silicon' if ok else 'agent binning not observed'} ===")
    try:
        bridge.ser.close()
    except Exception:
        pass
    return 0 if ok else 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default=os.environ.get("MON_UART", "/dev/ttyUSB2"))
    ap.add_argument("--bytes", type=int, default=256)
    ap.add_argument("--channel", type=int, default=0)
    a = ap.parse_args()
    print(f"[poc_coverage] UART {a.port} @ 115200")
    sys.exit(run(a.port, a.channel, a.bytes))
