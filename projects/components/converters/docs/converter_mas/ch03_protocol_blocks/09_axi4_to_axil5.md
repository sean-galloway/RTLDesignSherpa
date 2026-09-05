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

AXI5-Lite changes less than the version bump suggests, and in exactly the way
APB5 does: the transfer protocol is pure AXI4-Lite -- single-beat, no burst, no
ID, same handshakes and response codes -- and everything new is sideband. So
these blocks are thin wrappers over
[`axi4_to_axil4_{wr,rd}`](02_axi4_to_axil4.md). Burst decomposition, address
incrementing, response folding and the one-outstanding guards are that module,
instantiated unchanged. What lives here is the sideband, and one timing
decision it forces.

`axi4_to_axil5` pairs the two halves exactly as `axi4_to_axil4` pairs its own,
and contains nothing but the two instantiations.

The AXI4 slave surface is the **full** AXI4 interface, not a subset. A master
upstream of this converter may be feeding a fabric whose other branches reach
AXI4 slaves, so nothing is dropped from the boundary on the grounds that this
particular downstream path cannot use it.

## Where each signal gets its value

Every AXI5-Lite signal is in one of three groups. This is the whole content of
the block, so it is worth reading as a table rather than as prose.

| Group | Signals | Handling |
| --- | --- | --- |
| **FORWARDED** | `awlock`/`arlock`, `awuser`/`aruser`, `wuser` | carries the AXI4 value, gated by `ENABLE_LOCK` / `ENABLE_USER` |
| **FORWARDED (response)** | `buser` -> `s_axi_buser`, `ruser` -> `s_axi_ruser` | returned onto the AXI4 response channel, gated by `ENABLE_USER` |
| **TIED** | `awloop`, `awmpam`, `awmecid`, `awnsaid`, `awtrace`, `wpoison` (and the AR equivalents) | driven `'0`; AXI4 has no source for them |
| **TERMINATED** | `bloop`, `btrace`, `rloop`, `rtrace`, `rpoison` | completer-driven, nothing on the AXI4 side to return them to |

: AXI4 to AXI5-Lite -- Sideband Disposition

Two consequences of that table are worth stating outright.

**The tied group has no `ENABLE_` parameter, and that is deliberate.** A knob
that cannot change the design's behaviour is worse than no knob: a reader sets
it and believes something happened. `ENABLE_LOCK` and `ENABLE_USER` exist
because they gate a real choice; `ENABLE_TRACE`, `ENABLE_MPAM` and the rest do
not exist at all. The width parameters (`USER_WIDTH`, `LOOP_WIDTH`,
`MPAM_WIDTH`, `MECID_WIDTH`, `NSAID_WIDTH`) do remain, because they set the
port shape.

**The tied group's ports still exist.** An AXI5-Lite boundary whose shape
changes with a config knob cannot be wired to a fixed external completer, so
the ports are always present and always driven -- zero rather than floating.

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
**next** transaction's AW signals -- new address, new USER, new LOCK -- while
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
// ... captured into r_held_aw{lock,user} on w_aw_accept ...
wire [AXI_USER_WIDTH-1:0] w_awuser_sel = w_aw_accept ? s_axi_awuser
                                                     : r_held_awuser;
```

Accept cycle takes the live value; every beat after takes the captured one --
identical to the core's mux, so the sideband travels with the address it was
issued against.

The first version of this RTL passed it through combinationally. The failure is
not subtle once you can see it: with two overlapping writes, burst A's beats
carry burst B's USER **from beat 0**, because B's AW is already on the bus. It
is invisible to sequential traffic, which is why the test that catches it
(`test_axi4_to_axil5.py`, `full` level) issues two writes concurrently rather
than one after another.

W beats need no hold. The core assigns `m_axil_wdata = s_axi_wdata` directly --
W is 1:1 with the AXI4 side -- so `wuser` is a plain passthrough.

## Reset style

These modules use `always_ff @(posedge aclk or negedge aresetn)` rather than
the components-area `ALWAYS_FF_RST` macro, matching the AXI4-Lite converters
they wrap. Using the macro here while the core stays manual would make one
compiled design half synchronous-reset and half asynchronous -- Verilator says
so with `SYNCASYNCNET`. Converting the whole area is tracked as CONV-009, with
what it actually costs recorded there.

## Verification

`projects/components/converters/dv/tests/test_axi4_to_axil5.py` covers only
what the wrapper adds; the transfer protocol is already covered by the
AXI4-Lite suites, and duplicating it would test code this module does not
contain. Eight configurations across three levels check that forwarded values
arrive and stay with their burst, that tied signals read 0 (never X) at every
handshake, that the response sideband returns on the AXI4 channels, and that an
`ENABLE_*=0` build produces zeros from non-zero AXI4 traffic. The
overlapping-burst case was confirmed RED against the unfixed RTL and GREEN
after.

## Related Modules

The bridge generator instantiates these converters for `protocol = "axil5"`
slaves through the same component path as the AXI4-Lite ones -- the
`Axi4ToAxilShim` component takes `protocol='axil5'`. Which sideband groups are
live comes from the port's `axi5_features`, which on an `axil5` port accepts
only `user` and `exclusive`: naming a tied group there would suggest it changes
something, so the validator rejects it rather than ignoring it. Verified by
`projects/components/bridge/dv/tests/test_bridge_1x2_rw_axil5.py`.

## Navigation

**Next:** [PeakRDL Adapter](05_peakrdl_adapter.md)
