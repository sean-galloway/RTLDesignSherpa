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

# CXS Pattern Injector and Checker

**Modules:** `cxs_master_injector.sv`, `cxs_slave_pattern_check.sv`
**Location:** `rtl/amba/shared/`
**Status:** New (2026-10-16)

---

## Overview

These are the CXS counterparts of [`axis4_master_injector`](axis4_master_injector.md) and [`axis4_slave_pattern_check`](axis4_slave_pattern_check.md): the same per-channel LFSR pattern and CRC-32, carried on a credited CXS link (Arm IHI 0079, Issue D) instead of an AXI-Stream. They are compositions; nothing is re-implemented:

```
cxs_master_injector     = axis4_master_injector -> axis_to_cxs -> cxs_master        -> m_cxs_*
cxs_slave_pattern_check = s_cxs_* -> cxs_slave   -> cxs_to_axis -> axis4_slave_pattern_check
```

Every `cfg_*` and status port is the wrapped AXIS block's, unchanged, so the expected and actual CRCs stay bit-identical to the AXIS pair, `axi4_slave_rd_injector` and `axi4_slave_wr_crc_check`. A harness that already drives the AXIS pair can swap them module for module.

## The Link

The link profile is the RAPIDS CXS plane's (see [AXIS to CXS Adapters](../../../../projects/components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/17_axis_to_cxs.md), Converters MAS 3.17): Issue D, `CXSMAXPKTPERFLIT` = 2, 16-byte start alignment, `TID` -> `CXSSRCID` (the channel), `TDEST` -> `CXSTGTID`, `CXSUSER` = `{TUSER, TSTRB}` (TUSER dropped above 1016-bit flits), link activation on, no parity.

`cfg_interleave` round-robins channels beat by beat, so packets of different channels are open at the same time on the one link. That is legal CXS because packets are framed per stream (IHI 0079D 2.5.2). Both blocks key on the channel bits of `CXSSRCID` (`STREAM_SRCID_BITS`, default `$clog2(NUM_CHANNELS)`), and both ends must use the same value.

On the checker, `ready_en` still gates the stream: when held low, the receive FIFO fills and the link stops granting credits, which is what backpressure is on CXS.

## Parameters

Beyond the wrapped AXIS block's parameters:

| Parameter | Block | Default | Description |
|---|---|---|---|
| CXS_MAX_CREDIT | both | 32 | Credits the link carries (one credit = one flit) |
| CXS_CREDIT_BEYOND_SPEC | both | 0 | Allow more than 63 credits; both ends must agree |
| STREAM_SRCID_BITS | both | `$clog2(NUM_CHANNELS)` | Per-stream framing key on `CXSSRCID` |
| CXS_IDLE_CYCLES | injector | 32 | Idle RUN cycles before the link deactivates |
| RX_FIFO_DEPTH | checker | CXS_MAX_CREDIT | Receive FIFO = the credit pool |

`AXIS_DATA_WIDTH` must be 256, 512 or 1024. Full CXS (with `CXSCNTL`) has no 128-bit flit (rule 6), and `TSTRB` fills `CXSUSER` at 1024 bits.

## Status Ports

| Port | Block | Meaning |
|---|---|---|
| `link_state` | both | `{CXSACTIVEREQ, CXSACTIVEACK}` |
| `protocol_error` | both | Sticky: a credit, link or framing rule was broken |
| `unsupported` | checker | Sticky: a flit AXIS framing cannot represent arrived |

## Verification

`val/amba/test_cxs_pattern_pair.py` wires the injector's link straight into the checker (`val/amba/tb_cxs_pattern_pair.sv`) and runs every scenario of the AXIS pair test (`bin/TBClasses/cxs/cxs_pattern_pair_tb.py` subclasses the AXIS pair TB): per-channel CRC agreement, beat counts and the exact sequential and interleaved schedules, under backpressure. On top of that, an RDS-DV `CXSMonitor` checks the link on every cycle, both endpoints' `protocol_error` and the checker's `unsupported` must stay low, and the link must reach RUN. The grid covers 4 channels at 512 bits, 2 at 256 and 8 at 1024.
