# Fault-Injection Repro: G2 Board Read Hang (host_adapter AR tracker)

Standalone Icarus TB answering: *"if you know the scenario, why can't you
recreate it in sim?"*

Run:

```sh
REPO=<repo root>
iverilog -g2012 -I $REPO/rtl/amba/includes -o fi_host_adapter.vvp \
  $REPO/projects/fpga-systems/Genesys2/cache-ip/amber/rtl/bridges/generated/bridge_amber_axil/bridge_amber_axil_pkg.sv \
  $REPO/rtl/amba/gaxi/gaxi_skid_buffer.sv \
  $REPO/rtl/amba/axi4/axi4_slave_wr.sv \
  $REPO/rtl/amba/axi4/axi4_slave_rd.sv \
  $REPO/projects/components/utility-ip/converters/rtl/axil_to_axi4_wide_align_wr.sv \
  $REPO/projects/components/utility-ip/converters/rtl/axil_to_axi4_wide_align_rd.sv \
  $REPO/projects/fpga-systems/Genesys2/cache-ip/amber/rtl/bridges/generated/bridge_amber_axil/host_adapter.sv \
  tb_host_adapter_fi.sv
vvp fi_host_adapter.vvp
```

## What it proves

**Phase 1** deposits `host_adapter`'s AR tracker into its *full* encoding
(`ar_trk_wptr - ar_trk_rptr == AR_TRK_DEPTH`, no reads in flight). The
first read after reset then wedges with the board's exact ILA signature
(`build-bringup/fpga/reports/ila_trace.csv`, round 4):

| Signal (ILA tap)               | Board | This TB |
|--------------------------------|-------|---------|
| `ub_m_arv` (host ARVALID)      | 1 held | 1 held |
| `ub_m_arr` (host ARREADY)      | 0     | 0      |
| `host_32b_arvalid` (forward)   | 0     | 0      |
| R channel                      | never | never  |
| window                         | static 45us | static 64+32 cyc |

and the wedge is self-sustaining after the deposit is released: popping the
tracker needs an R; an R needs a forwarded AR; forwarding needs `!full`.
Deadlock by construction.

**Phase 2** releases, re-applies reset, and runs legal reads -- all pass.
The RTL has no legal transition from clean reset into the wedged state:
the push/pop handshake discipline keeps `wptr - rptr` inside
`[0, AR_TRK_DEPTH)` unconditionally.

## Why no 2-state sim ever reproduced it

RTL sim, gate-level sim, and `+verilator+rand+reset+2` all explore only
states reachable by legal transitions from the (applied) reset state. The
board's wedged state is outside that set, so no sim at any level (fub,
unit, harness) could enter it. `rand+reset` does not help: it randomizes
initial values and then applies the same clean reset, returning the design
to the same reachable set.

Silicon entered the state by means RTL cannot model: a single-event flip
(voltage droop/bounce during the cycle-injector storm -- deterministic
because placement and stimulus are identical across builds) or a Vivado
netlist transform. The round-5 ILA `mark_debug` taps on
`ar_trk_full` / `ar_trk_wptr/rptr` / wrapper busy name which one.

## Use as A/B vehicle

Any proposed hardening (FSM safe-default, watchdog flush of the tracker,
SEU-tolerant state) can be tested here: deposit the same state, verify
recovery, then re-run Phase 2 to confirm no functional regression.
