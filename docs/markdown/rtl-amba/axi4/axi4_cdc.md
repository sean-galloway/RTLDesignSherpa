<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# axi4_cdc_wr / axi4_cdc_rd

**Files:** `rtl/amba/axi4/axi4_cdc_wr.sv`, `rtl/amba/axi4/axi4_cdc_rd.sv`
**Filelists:** `rtl/amba/filelists/axi4_cdc_wr.f`, `axi4_cdc_rd.f` (each `-f`'s `rtl/cdc/filelists/gaxi_fifo_async.f`)
**Test:** `val/amba/test_axi4_cdc.py` (`bin/TBClasses/amba/axi4_cdc_tb.py`)

## What it is

AXI4 channels carried across a clock-domain boundary: `s_axi_*` on
`s_aclk`/`s_aresetn`, `m_axi_*` on `m_aclk`/`m_aresetn`. One `gaxi_fifo_async`
per channel, each crossing in the channel's own direction -- AW, W and AR
from the requester's domain into the completer's, B and R back. There is no
protocol state, no ID logic and no reordering: each channel is an in-order
FIFO, so what a channel accepts on one side it presents on the other, later.
AW and W cross independently, as AXI permits.

Built for the bridge generator's CDC slave ports (BRIDGE-017): a slave port
declared `cdc = true` gets these between the crossbar-side wrapper and its
boundary, and its own `<slave>_aclk` / `<slave>_aresetn` pins on the bridge
top. The pair stands on its own as an AXI4 clock converter.

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `AXI_DATA_WIDTH`, `AXI_USER_WIDTH` | 8, 32, 32, 1 | port widths, both sides |
| `CDC_DEPTH` | 8 | entries per channel FIFO; also the beats a channel can have in flight across the boundary. Power of 2 under Gray pointers. 8 is the floor for full throughput: the pointer synchronizers make the FIFO's full/empty view about seven cycles stale round trip, and a 4-deep FIFO streams at 4/7 of a beat per cycle (measured 0.58) |
| `USE_JOHNSON` | 0 | 0 = Gray pointers (default), 1 = Johnson (any depth). Hoisted per the CDC handbook rule -- a conscious choice, never the FIFO's own default |
| `N_FLOP_CROSS` | 2 | synchronizer depth for the crossed pointers |

## Reset

Both domains reset each FIFO's own pointer and its crossed copy of the
remote pointer from that domain's reset. With both resets asserted together
the crossing starts consistent. A **one-sided reset is not safe**: within
`N_FLOP_CROSS` clocks of deassertion the crossed copy re-converges on a
remote pointer that kept moving, so a requester-side-only reset fabricates
entries and a completer-side-only reset replays them. Quiesce the bus before
resetting one side -- the same contract as `apb4_slave_cdc`, spelled out in
`vault/handbook/design/cdc.md`.

## Throughput and latency

One beat per clock of the slower domain per channel, once the FIFO has
something to offer, provided `CDC_DEPTH` covers the pointer round trip:
each side's view of the other's pointer is `N_FLOP_CROSS` plus a register
stale, so a FIFO shallower than that round trip (about seven cycles with the
defaults) stalls on a full or empty flag that is already out of date. At
depth 4 the crossing streams at 0.58 beat per cycle with equal clocks; at
the default 8 it streams at one. `test_axi4_cdc` asserts the streaming rate
at three clock ratios, so a depth that cannot keep up fails the unit test
before it reaches a bridge.
Latency per crossing is the synchronizer depth plus the FIFO's registered
flags, `N_FLOP_CROSS + 1` clocks of the destination domain, each way.

## Verification

`test_axi4_cdc.py` runs each module with the requester and completer at
equal, requester-fast (10/3 ns) and requester-slow (3/10 ns) periods, 32-
and 64-bit at FULL: sequential bursts of up to 16 beats (data straight out
of the completer's memory, W beats contiguous and in order at the completer,
WLAST on the last crossed beat, R beats in order at the requester), many
bursts in flight at once with rotating IDs, and an out-of-range access whose
SLVERR must come back through the response crossing with nothing written.
