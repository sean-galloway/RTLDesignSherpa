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

# CXS (Credited eXtensible Stream) Modules

**Location:** `rtl/amba/cxs/`
**Specification:** Arm *AMBA CXS Protocol Specification*, ARM IHI 0079, Issues A, B, C and D
**Status:** New (2026-10-15); GATE/FUNC/FULL green

---

## Overview

CXS is Arm's point-to-point packet stream protocol for wide links. Its main use is between an on-chip interconnect and a PCIe controller carrying CCIX or CXL. Data moves in one direction, one *flit* (one cycle of `CXSDATA`) at a time. A flit can hold several packets, and a packet can span several flits.

CXS differs from AXI-Stream in one fundamental way: **there is no READY.** The receiver grants credits on `CXSCRDGNT`, one per cycle. The transmitter spends one credit per flit, and with link control it can hand a credit back on `CXSCRDRTN`. Every credit the receiver grants is a promise of buffer space for one flit, so the receiver is never back-pressured on the wire.

This directory holds one family covering **every published issue**. Each issue is a strict superset of the one before it. An issue is therefore a set of legal property values, not a different protocol, and the `CXS_ISSUE` parameter selects which set is checked at elaboration.

| Issue | Date | What it adds |
|---|---|---|
| A | Mar 2018 | First release: `CXSDATAFLITWIDTH` 256/512/1024, `CXSMAXPKTPERFLIT` 2..4, up to 15 credits, `CXSCHECKTYPE`, `CXSLINKCONTROL` |
| B | Dec 2020 | Multiple protocol streams: `CXSLAST` (`CXS_LAST`), `CXSPRCLTYPE` (`CXS_PROTOCOL_TYPE`), and their check signals |
| C | Dec 2023 | One packet per flit (`CXSMAXPKTPERFLIT` = 1, no `CXSCNTL`, any width 8..2048), `CXS_MAX_CREDIT` up to 63, clock and reset defined |
| D | Sep 2025 | 2048-bit flits with several packets, `CXS_START_ALIGNMENT` = 4, `CXSSRCID`/`CXSTGTID` (0..8 bits), `CXSUSER` (0..128 bits), CXS-Lite named |

## Module Categories

| Module | Role | Page |
|---|---|---|
| `cxs_master` | Transmitter: FUB valid/ready flits in, credited CXS link out | [cxs_master.md](cxs_master.md) |
| `cxs_slave` | Receiver: credited CXS link in, FUB valid/ready flits out; the receive FIFO is the credit pool | [cxs_slave.md](cxs_slave.md) |
| `cxs_master_cg` | `cxs_master` behind `amba_clock_gate_ctrl`; gates only in link STOP | [cxs_master_cg.md](cxs_master_cg.md) |
| `cxs_slave_cg` | `cxs_slave` behind `amba_clock_gate_ctrl`; a rising `CXSACTIVEREQ` wakes it | [cxs_slave_cg.md](cxs_slave_cg.md) |
| `cxs_pkg` (`rtl/amba/includes/`) | Widths, `CXSCNTL` field offsets, per-issue legality (`config_error`) | this page |
| `cxs_cntl_track` | Packet-open tracking and `CXSCNTL` format checks, shared by both endpoints | this page |
| `cxs_odd_byte_parity` | `Odd_Byte_Parity` generate/check for one signal of any width | this page |
| `cxs_stream_key` | The tracked part of a flit's stream identity: `{PRCLTYPE, SRCID, TGTID}` low bits | this page |
| `cxs_link_snoop` | Passive model of a link from its wires alone: credits in flight, link state, credit/link/per-stream framing checks (feeds `cxs_intf_observer`) | this page |
| `cxs_master_monlite` / `cxs_slave_monlite` | The endpoints with [`cxs_monitor_lite`](../monitor/cxs_monitor_lite.md) tapping their FUB handshake and status; packets tagged `PROTOCOL_CXS` | [cxs_monitor_lite.md](../monitor/cxs_monitor_lite.md) |
| `axis_to_cxs` / `cxs_to_axis` | AXI-Stream beats to CXS flits and back (one packet per TLAST run, `TSTRB` carried in `CXSUSER`). They live in `projects/components/utility-ip/converters/rtl/` | Converters MAS 3.17 ([17_axis_to_cxs.md](../../../../projects/components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/17_axis_to_cxs.md)) |

The monitor wrappers have no `_cg` variants (clock gating is an FPGA-only concern here). Both endpoints export `credit_starved` for the monitor: on the transmitter, a flit is waiting in RUN with no credit; on the receiver, no credit can be granted because the FIFO holds every slot.

## Properties and Parameters

Every endpoint takes the same property set. Parameter names follow the spec property they implement.

| Spec property | Parameter | Values | Issue |
|---|---|---|---|
| (issue) | `CXS_ISSUE` | 1..4 = A..D (`cxs_pkg::CXS_ISSUE_A..D`) | - |
| `CXSDATAFLITWIDTH` | `CXS_DATA_WIDTH` | 256/512/1024; 2048 with several packets (D); 8..2048 by 8 with one packet (C) | A |
| `CXSMAXPKTPERFLIT` | `CXS_MAX_PKT_PER_FLIT` | 2..4; 1 from C | A |
| `CXS_START_ALIGNMENT` | `CXS_START_ALIGN` | 16; 4 from D | D |
| `CXS_LAST` | `CXS_HAS_LAST` | 0/1 | B |
| `CXS_PROTOCOL_TYPE` | `CXS_HAS_PRCLTYPE` | 0/1 | B |
| `CXS_SRCID_WIDTH` / `CXS_TGTID_WIDTH` | same names | 0..8 | D |
| `CXS_USER_WIDTH` | same name | 0..128 | D |
| `CXS_MAX_CREDIT` | same name | 1..15; 1..63 from C | A |
| `CXSLINKCONTROL` | `CXS_LINK_CTRL` | 1 = `Explicit_Credit_Return`, 0 = `None` | A |
| `CXSCHECKTYPE` | `CXS_CHECK` | 1 = `Odd_Byte_Parity`, 0 = `None` | A |
| (beyond spec) | `CXS_CREDIT_BEYOND_SPEC` | 1 = `CXS_MAX_CREDIT` may exceed the cap (rule 12 skipped) | - |
| (stream tracking) | `CXS_STREAM_PRCL_BITS` / `CXS_STREAM_SRCID_BITS` / `CXS_STREAM_TGTID_BITS` | low bits of each field that tell interleaved streams apart; 0/0/0 = one stream | B |

`CXSCONTINUOUSDATA` and `CXSERRORFULLPKT` constrain what the *source of packets* does, so they are not parameters of these endpoints. Both endpoints carry flits unchanged. The transmitter never deactivates the link while a packet is open, which `CXSCONTINUOUSDATA` requires.

### Configuration checks

`cxs_pkg::config_error()` returns 0 for a legal property set, or the number of the first rule broken. Each endpoint calls it from an elaboration-time `param_check` and stops with `$fatal` naming the rule. The framework's `CXSConfig.config_error()` implements the same rules in the same order, so a rule number means the same thing on both sides.

| Rule | Requirement |
|---|---|
| 1 | Issue is A..D |
| 2 | `CXSMAXPKTPERFLIT` is 1..4 |
| 3 | One packet per flit needs Issue C or later |
| 4 | With one packet per flit, the width is 8..2048 and a multiple of 8 |
| 5 | With one packet per flit, `CXS_LAST` and `CXS_PROTOCOL_TYPE` are false |
| 6 | With several packets per flit, the width is 256/512/1024, plus 2048 from Issue D |
| 7 | A 256-bit flit carries at most 2 packets, unless start alignment is 4 (Issue D) |
| 8 | Start alignment is 4 or 16 |
| 9 | Start alignment 4 needs Issue D |
| 10 | `CXSLAST` / `CXSPRCLTYPE` need Issue B or later |
| 11 | `CXS_MAX_CREDIT` is at least 1 |
| 12 | `CXS_MAX_CREDIT` is at most 15 before Issue C, 63 from Issue C (skipped with `CXS_CREDIT_BEYOND_SPEC`) |
| 13 | Source/target ID widths are 0..8, user width 0..128 |
| 14 | `CXSSRCID` / `CXSTGTID` / `CXSUSER` need Issue D |

## Streams and Interleaving

A CXS stream is the flits that share `CXSPRCLTYPE`, `CXSSRCID` and `CXSTGTID` (IHI 0079D 2.5.2). Flits of different streams may interleave (with `CXSCONTINUOUSDATA`, only where `CXSLAST` allows), so packet framing is legal or not per stream: a flit may carry a START for stream B while stream A still has a packet open.

`cxs_cntl_track` keeps one packet-open bit per stream, selected by a key that `cxs_stream_key` builds from the low `CXS_STREAM_*_BITS` of the three fields. Tracking every possible stream would cost 2^19 bits, so the key bounds the state at 2^(P+S+T) bits. Streams that differ only above the key share one bit, so the key must cover every stream that can have a packet open at once. RAPIDS keys on the channel bits of `CXSSRCID`. The defaults (0/0/0) track the whole link as one stream, which is exactly the behaviour before 2026-10-16. Both ends of a link, and any monitor or snoop on it, must use the same key. With the key off, interleaved streams set `protocol_error`; `val/amba/test_cxs_stream_interleave.py` asserts both halves.

The framework's `CXSDepacketizer` and `CXSMonitor` track open packets per stream on the full spec key, so they need no parameter.

## Credits Beyond the Spec

`CXS_MAX_CREDIT` is capped at 63 (15 before Issue C). `CXS_CREDIT_BEYOND_SPEC = 1` lifts the cap and nothing else: rule 12 is skipped, the credit counters widen to hold the pool, and every other rule still applies. It exists for a receiver whose buffer is a whole SRAM (the RAPIDS CXS tops default the pool to one channel's SRAM). Both ends of the link must be built with it; the framework's `CXSConfig(credit_beyond_spec=True)` mirrors it.

## CXSCNTL Layout

`CXSCNTL` marks where packets start and end inside a flit. With N = `CXSMAXPKTPERFLIT`, the fields from bit 0 upward are:

```
START[N-1:0] | START0PTR .. START(N-1)PTR | END[N-1:0] | ENDERROR[N-1:0] | END0PTR .. END(N-1)PTR
```

- A start pointer is log2(W/128) bits with 16-byte alignment, or log2(W/32) with 4-byte alignment. The first byte of a packet is `STARTnPTR << 4` (or `<< 2`).
- An end pointer is always log2(W/32) bits and points at the packet's last aligned 4 bytes, so its last byte is `(ENDnPTR << 2) + 3`.
- `START` and `END` are thermometer codes, and `ENDERROR[n]` requires `END[n]`.

So `CXSCNTLWIDTH = N * (3 + start_ptr_w + end_ptr_w)`, and it is 0 when N = 1. `cxs_pkg::cntl_width()` computes it. The framework unit test `tests/unit/test_cxs_config.py` checks the formula against all 22 rows of IHI 0079D Tables 4-5 and 4-7, including each END field's bit position.

## Link Control (CXS_LINK_CTRL = 1)

Two signals, `CXSACTIVEREQ` (driven by the transmitter) and `CXSACTIVEACK` (driven by the receiver), form a four-phase handshake. The link state is simply the pair of signal values; there is no separate state machine.

| {REQ, ACK} | State | Flits | Credits |
|---|---|---|---|
| 00 | STOP | none | all held by the receiver |
| 10 | ACTIVATE | none | the transmitter must accept early grants |
| 11 | RUN | yes | granted, spent, optionally returned |
| 01 | DEACTIVATE | in-flight only | the transmitter returns every credit; ACK falls only when all are home |

`CXSDEACTHINT` lets the receiver ask the transmitter to take the link down. Only the transmitter starts a state change. `CXSACTIVEREQ` may be captured asynchronously, so `cxs_slave` synchronizes it (`ACTIVEREQ_SYNC_STAGES`).

## Implemented Signal Set

Every signal of IHI 0079D Table 3-1 and every check signal of Table 3-2 is implemented. An absent optional signal keeps a one-bit port, tied low on outputs and ignored on inputs, the same convention the AXIS endpoints use.

| Signal | Present when |
|---|---|
| `CXSVALID`, `CXSDATA`, `CXSCRDGNT` | always |
| `CXSCNTL` | `CXS_MAX_PKT_PER_FLIT` > 1 |
| `CXSLAST` / `CXSPRCLTYPE` | `CXS_HAS_LAST` / `CXS_HAS_PRCLTYPE` |
| `CXSSRCID` / `CXSTGTID` / `CXSUSER` | width > 0 |
| `CXSCRDRTN`, `CXSACTIVEREQ`, `CXSACTIVEACK`, `CXSDEACTHINT` | `CXS_LINK_CTRL` = 1 |
| `*CHK` (one per signal above, except `CXSDEACTHINT`) | `CXS_CHECK` = 1 and the signal is present |

## Verification

The BFMs are the `cxs` family of the RDS-DV framework (`CocoTBFramework.components.cxs`): `CXSTransmitter`, `CXSReceiver`, `CXSMonitor`, `CXSConfig`, `CXSPacketizer` and `CXSDepacketizer`. The FUB side of each endpoint is driven by the framework GAXI BFMs. TB classes live in `bin/TBClasses/cxs/`.

| Test | DUT | Grid |
|---|---|---|
| `val/amba/test_cxs_master.py` | `cxs_master` | issues A-D, CXS-Lite, with and without link control and parity |
| `val/amba/test_cxs_slave.py` | `cxs_slave` | the same grid, each config also run with a 3-deep receive FIFO |
| `val/amba/test_cxs_master_cg.py` | `cxs_master_cg` | the same grid; must gate in STOP, never without link control |
| `val/amba/test_cxs_slave_cg.py` | `cxs_slave_cg` | the same grid; ACTIVEREQ must wake it |
| `val/amba/monitor-lite/test_cxs_{master,slave}_monlite.py` | the `_monlite` wrappers | the same grid; every Ocelus packet class checked |

```bash
source env_python
cd val/amba
make clean-all && make 'run-cxs_*-func-parallel'
```

Each traffic phase makes one claim: streaming, credit starvation (the DUT must stall, and never send without a credit), a full idle credit pool (exactly the bound, never more), idle and hint-driven deactivation with every credit returned, no deactivation inside a packet, and parity-error injection. The suite kills six deliberate RTL mutations: sending without a credit, never returning credits, granting one past the pool, dropping ACK with credits outstanding, ignoring `CXSDATACHK`, and deactivating mid-packet.

## References

- Arm. *AMBA CXS Protocol Specification*, ARM IHI 0079, Issue A (Mar 2018), B (Dec 2020), C (Dec 2023), D (Sep 2025). [developer.arm.com/documentation/ihi0079](https://developer.arm.com/documentation/ihi0079/d/). Chapters 2-7 throughout: 2.1.2 credit rules, 2.2 properties (Table 2-2) and compatibility (Table 2-3), 3.2 check signals (Table 3-2), 4.1 packet placement, 4.3 control fields (Tables 4-4, 4-5, 4-7), chapter 5 link activation, 6.1 continuous delivery, chapter 7 CXS-Lite. Citation only; the PDFs are not redistributed here.

---

## Navigation

- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
