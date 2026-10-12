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

# AXI4 to AXI5-Lite

**Modules:** `axi4_to_axil5.sv`, `axi4_to_axil5_wr.sv`, `axi4_to_axil5_rd.sv`
**Filelists:** `rtl/filelists/axi4_to_axil5{,_wr,_rd}.f` (each `-f`'s the AXI4-Lite converter's closure)

## Overview

AXI5-Lite changes less than the version bump suggests. The transfer protocol
is AXI4-Lite -- single-beat, no burst, same handshakes and response codes --
plus a transaction ID (AWID/BID, ARID/RID) and a few optional signals
(IHI 0022L section B2.1.5, Table B2.2). So these blocks are thin wrappers over
[`axi4_to_axil4_{wr,rd}`](02_axi4_to_axil4.md). Burst decomposition, address
incrementing, response folding and the one-outstanding guards are that module,
instantiated unchanged. What lives here is the ID, the optional signals, and
one timing decision they force.

`axi4_to_axil5` pairs the two halves exactly as `axi4_to_axil4` pairs its own,
and contains nothing but the two instantiations.

The AXI4 slave surface is the **full** AXI4 interface, not a subset. A master
upstream of this converter may be feeding a fabric whose other branches reach
AXI4 slaves, so nothing is dropped from the boundary on the grounds that this
particular downstream path cannot use it.

## Where each signal gets its value

Every AXI5-Lite signal is in one of four groups. This is the whole content of
the block, so it is worth reading as a table rather than as prose.

| Group | Signals | Handling |
| --- | --- | --- |
| **ID** | `awid`/`arid` out; `bid` -> `s_axi_bid`, `rid` -> `s_axi_rid` | AXI4 ID of the burst the beat belongs to; the response carries the ID the AXI5-Lite completer returned. `AXI_ID_WIDTH` bits |
| **FORWARDED** | `awuser`/`aruser`, `wuser` | carries the AXI4 value, gated by `ENABLE_USER` |
| **FORWARDED (response)** | `buser` -> `s_axi_buser`, `ruser` -> `s_axi_ruser` | returned onto the AXI4 response channel, gated by `ENABLE_USER` |
| **TIED** | `awtrace`, `wpoison`, `artrace` | driven `'0`; AXI4 has no source for them |
| **TERMINATED** | `btrace`, `rtrace`, `rpoison` | completer-driven, nothing on the AXI4 side to return them to |

: AXI4 to AXI5-Lite -- Signal Disposition

**What is not there.** AxLOCK, AxMPAM, AxMECID, AxNSAID and xLOOP are not
present on AXI5-Lite, and exclusive access is not supported (IHI 0022L
B2.1.5, Table B2.2). Until issue #102 these converters carried them (LOCK
forwarded, the rest tied to zero); they now have no such ports and no
`ENABLE_LOCK`, `LOOP_WIDTH`, `MPAM_WIDTH`, `MECID_WIDTH` or `NSAID_WIDTH`
parameters. The AXI4 `AxLOCK` input is dropped. An AXI4 exclusive access
through this converter therefore completes as a normal access with an OKAY
response, which is exactly what AXI4 specifies for a subordinate without
exclusive support: OKAY, not EXOKAY, tells the master the exclusive failed,
and an exclusive write still updates memory (IHI 0022H A7.2.3, A7.2.5).

**The tied group has no `ENABLE_` parameter, and that is deliberate.** A knob
that cannot change the design's behaviour is worse than no knob: a reader sets
it and believes something happened. `ENABLE_USER` exists because it gates a
real choice; `ENABLE_TRACE` and `ENABLE_POISON` do not exist at all. The
`USER_WIDTH` parameter remains, because it sets the port shape.

**The tied group's ports still exist.** An AXI5-Lite boundary whose shape
changes with a config knob cannot be wired to a fixed external completer, so
the ports are always present and always driven -- zero rather than floating.

## IDs and response ordering

The AXI4 ID crosses unchanged: `m_axil_awid`/`m_axil_arid` carry it on every
decomposed beat, held across the burst the same way the USER sideband is (see
the next section), and `s_axi_bid`/`s_axi_rid` are driven from
`m_axil_bid`/`m_axil_rid` -- the ID the AXI5-Lite completer returned, which a
compliant completer reflects from AxID (IHI 0022L A5.1.1).

This is correct for any mix of AXI4 IDs because the core holds **one** AXI4
burst in flight per direction: `s_axi_awready`/`s_axi_arready` stay low until
the burst's B, or its RLAST beat, has been handed back. Every AXI5-Lite
response therefore belongs to the single burst in flight. The completer is
allowed to reorder responses across IDs, but there is never a second ID
outstanding for it to reorder against, and responses with the same ID return
in order. An AXI4 master issuing several IDs gets each transaction's response
under its own ID, in issue order, which AXI4 permits (there is no ordering
requirement across IDs). Using the returned ID rather than a locally stored
copy means a completer that fails to reflect AxID is visible at the AXI4
boundary instead of being masked.

`rpoison` deserves its own note. AXI4 has no poison bit, so a poisoned read
beat arriving from an AXI5-Lite completer cannot be signalled to the AXI4
master through any protocol field. It is terminated rather than folded into
`RRESP`, because turning poison into `SLVERR` would invent an error the
completer never reported. A design that must observe poison needs an AXI5
master port, not an AXI4 one.

## The AW/AR sideband is held, not passed through

This is the one place the wrapper is not trivial, and it is worth understanding
before modifying it.

The core **decomposes**: one AXI4 AW handshake becomes N AXI5-Lite AW
handshakes, one per beat. And `axi4_to_axil4_wr` drops `s_axi_awready` as soon
as it accepts the AW (`s_axi_awready = !r_aw_active && !r_wr_outstanding && ...`).
So from the cycle after acceptance, an AXI4 master is free to present the
**next** transaction's AW signals -- new address, new ID, new USER -- while
beats 2..N of the current burst are still going out.

A combinational passthrough of the sideband therefore stamps those later beats
with the wrong values. The core has the identical problem with the address and
solves it with a capture-and-hold mux:

```systemverilog
assign m_axil_awaddr = r_aw_active ? r_aw_addr : s_axi_awaddr;
```

`r_aw_active` is registered, so it is still 0 during the accept cycle itself
and 1 for every beat after. The wrapper cannot see that signal, so it
reconstructs the same selector from outside:

```systemverilog
wire w_aw_accept = s_axi_awvalid && s_axi_awready;
// ... captured into r_held_aw{id,user} on w_aw_accept ...
wire [AXI_USER_WIDTH-1:0] w_awuser_sel = w_aw_accept ? s_axi_awuser
                                                     : r_held_awuser;
```

Accept cycle takes the live value; every beat after takes the captured one --
identical to the core's mux, so the ID and sideband travel with the address
they were issued against. `m_axil_awid` uses the same selector.

The first version of this RTL passed it through combinationally. The failure is
not subtle once you can see it: with two overlapping writes, burst A's beats
carry burst B's USER **from beat 0**, because B's AW is already on the bus. It
is invisible to sequential traffic, which is why the test that catches it
(`test_axi4_to_axil5.py`, `full` level) issues two writes concurrently rather
than one after another.

W beats need no hold. The core assigns `m_axil_wdata = s_axi_wdata` directly --
W is 1:1 with the AXI4 side -- so `wuser` is a plain passthrough.

## Reset style

These modules use the `ALWAYS_FF_RST` macro from `reset_defs.svh`, as do the
AXI4-Lite converters they wrap, so one compiled design has one reset style.
Mixing the macro with hand-written `always_ff @(posedge aclk or negedge
aresetn)` blocks would make it half synchronous-reset and half asynchronous
-- Verilator says so with `SYNCASYNCNET`. The area conversion is recorded as
projects/components/utility-ip/converters BUG-007 (was CONV-009).

## Verification

`projects/components/utility-ip/converters/dv/tests/test_axi4_to_axil5.py` covers only
what the wrapper adds; the transfer protocol is already covered by the
AXI4-Lite suites, and duplicating it would test code this module does not
contain. Eight configurations across three levels check that:

- the signals AXI5-Lite excludes (LOCK, LOOP, MPAM, MECID, NSAID) are absent
  from the DUT;
- every AXI5-Lite AW/AR beat carries its burst's AXI4 ID and USER, and every
  AXI4 B/R carries the ID the completer returned;
- several AXI4 IDs in flight at once (`func` and up) each complete under their
  own ID with their own data -- the AXI4 master BFM picks responses up by ID,
  and the AXI5-Lite slave BFM reflects AxID and shares one memory between its
  read and write sides;
- tied signals read 0 (never X) at every handshake, the response USER returns
  on the AXI4 channels, and an `ENABLE_USER=0` build produces zeros from
  non-zero AXI4 traffic.

The overlapping-burst case was confirmed RED against the unfixed USER hold
and GREEN after. For the ID, a mutant that passes `s_axi_awid` through
combinationally fails 6 of 8 configurations, a mutant that zeroes `s_axi_rid`
fails all 8, and the pre-#102 RTL (no ID ports) fails all 8.

## Related Modules

The bridge generator instantiates these converters for `protocol = "axil5"`
slaves through the same component path as the AXI4-Lite ones -- the
`Axi4ToAxilShim` component takes `protocol='axil5'`. Which sideband groups are
live comes from the port's `axi5_features`. Since issue #102 the only gate
the converter has is `ENABLE_USER`; the bridge generator's `axil5` handling
(`bridge_pkg/axil5_sideband.py`) has to follow the new port list -- no
LOCK/LOOP/MPAM/MECID/NSAID, plus `m_axil_{aw,ar}id` and `m_axil_{b,r}id`. Verified by
`projects/components/fabric-gen-ip/bridge/dv/tests/test_bridge_1x2_rw_axil5.py`.

## Navigation

**Next:** [PeakRDL Adapter](05_peakrdl_adapter.md)
