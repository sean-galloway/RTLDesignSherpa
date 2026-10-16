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

# CXS Interface Observer

**Module:** `cxs_intf_observer.sv`
**Location:** `projects/components/utility-ip/misc/rtl/`
**Filelist:** `projects/components/utility-ip/misc/rtl/filelists/cxs_intf_observer.f`
**Status:** New (2026-10-16)

---

## Overview

`cxs_intf_observer` is a passive tap for credited CXS links (Arm IHI 0079), the CXS sibling of [`axis4_intf_observer`](axis4_intf_observer.md). It has the same APB window, the same `obs_regs` map, the same monbus egress and the same telemetry readback, so one host decoder and one regmap serve all four observers. Every `obs_cxs_*` pin is an input, including the receiver's `CXSCRDGNT` and `CXSACTIVEACK`. It never drives the link (`vault/handbook/design/observers-do-not-drive.md`).

Per port it builds:

- a **`cxs_link_snoop`** (`rtl/amba/cxs`), the link modelled from its wires alone: credits in flight (grants minus flits minus returns), link state, and the protocol checks. Those are a flit with no credit, a return with no credit, VALID together with CRDRTN, a grant past `CXS_MAX_CREDIT`, and malformed or mis-framed `CXSCNTL` per stream;
- a **`cxs_monitor_lite`** event tap fed by the snoop, emitting `PROTOCOL_CXS` monbus packets. The monbus group filters `PROTOCOL_CXS` through its AXIS slot, so `AXIS_PKT_MASK` and `AXIS_MASK1..3` govern these packets;
- an **`axis_bus_meter`** with the cycle buckets mapped to CXS (below).

A passive tap cannot see whether the transmitter *wants* to send. The tap's credit-starved input is therefore the snoop's "RUN with no credit held", which is the receiver throttling, and not an endpoint's own starvation flag.

## Parameters

The egress, group, CFI, `ENABLE_MON_TAPS`, `TAP_ENABLE_*_LOGIC`, `ENABLE_BUS_METER`, `NUM_PORTS`, `NUM_CHANNELS` and `APB_ADDR_WIDTH` parameters are the AXIS observer's. The link parameters:

| Parameter | Default | Description |
|---|---|---|
| DATA_WIDTH | 512 | `CXSDATAFLITWIDTH` (the data itself is not observed) |
| CXS_MAX_PKT_PER_FLIT / CXS_START_ALIGN | 2 / 16 | the `CXSCNTL` layout |
| CXS_SRCID_WIDTH / CXS_TGTID_WIDTH | 8 / 4 | the ID ports; the channel bucket is the low `CXSSRCID` bits |
| CXS_MAX_CREDIT | 15 | the link's credit limit; beyond 63 is fine here |
| CXS_STREAM_PRCL_BITS / _SRCID_BITS / _TGTID_BITS | 0 | per-stream framing key, the same as the link's endpoints |
| UNIT_ID | 8'h12 | (8'h10 AXI, 8'h11 AXIS observers) |

## Ports

The APB, `cam_clear`, egress (`s_axil_*`, `m_axi_*`, `m_axil_*`), `irq_out` and `i_meter_clear` / `i_meter_freeze` ports are the AXIS observer's. The observed link, per port: `obs_cxs_valid`, `obs_cxs_cntl`, `obs_cxs_prcltype`, `obs_cxs_srcid`, `obs_cxs_tgtid`, `obs_cxs_crdgnt`, `obs_cxs_crdrtn`, `obs_cxs_activereq` and `obs_cxs_activeack`. There are also `obs_cxs_data` and `obs_cxs_deacthint`, which are observed but unused: the payload means nothing to a passive tap, and the hint shows up as the link state it causes. They exist so a link BFM binds unchanged.

## Meter Buckets

| Bucket | CXS meaning |
|---|---|
| productive | a flit crossed the link |
| backpressure | RUN, no credit held: the receiver is throttling |
| starvation | RUN, a credit held, no flit: the transmitter has nothing to send |
| idle | the link is not in RUN |

Bytes are counted per flit (`DATA_WIDTH/8` per flit), because a passive tap cannot tell how much of a CXS flit is payload. A packet is counted on every flit that ends one.

## Registers

The map is `obs_regs.rdl`, shared with the other observers. `MON_CTRL` gates the cones exactly as on the AXIS observer: ERROR_EN Error, TIMEOUT_EN Timeout, COMPL_EN Completion, THRESHOLD_EN Credit, PERF_EN Stream, DEBUG_EN Channel. `OBS_CAPS2` = `{ADDR_WIDTH, CXS_SRCID_WIDTH, DATA_WIDTH[15:0]}`. `OBS_STAT_SEL.METRIC` 0..16 have the AXIS observer's meanings, with the CXS buckets above and flit-granular bytes. It adds two:

| METRIC | Reads |
|---|---|
| 17 | the snoop's credits in flight |
| 18 | the snoop's sticky protocol error |

## Verification

`dv/tests/fub/test_cxs_intf_observer.py` runs over `dv/tbclasses/cxs_intf_observer_tb.py`. That TB extends the AXI observer TB, the same way the AXIS one does, and plays both ends of the link with the RDS-DV `CXSTransmitter` and `CXSReceiver`.

| Test | Proves |
|---|---|
| `test_cxs_intf_observer` | `OBS_CAPS0/1/2` report the build; the snoop reports no error out of reset |
| `..._traffic` | Two channels interleaved flit by flit, three-flit packets open in both. Flits, packets, bytes, productive cycles and per-channel buckets match the stimulus exactly, with no protocol error. Backpressure appears when the receiver's grants are throttled (1 cycle with free grants, 145 throttled at gate) and not otherwise |
| `..._packets` | One Completion/PACKET_END per packet and no Error on clean traffic. A flit forced on the pins with the link in STOP and no credit sets the sticky error (METRIC 18) and comes out as Error/PROTOCOL |

The forced flit is the one stimulus not sent through a BFM, because a compliant transmitter cannot produce it.

## Related

- [`axis4_intf_observer`](axis4_intf_observer.md): the AXIS sibling this is built from.
- `rtl/amba/cxs/cxs_link_snoop.sv` and `rtl/amba/ocelus/cxs_monitor_lite.sv`: the snoop and the tap.
- `docs/markdown/rtl-amba/cxs/README.md`: streams, interleaving and credits.
