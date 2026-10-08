# ISSUE-005: no harness exercises a master's multi-outstanding path

**Priority:** P2
**Status:** closed no-action 2026-10-08 — Sean's call, recorded
**Owner:** TBD

> **RESOLUTION 2026-10-08 (Sean):** no harness should exercise this. The
> repo's instrument for traffic-shape pressure is test generator RTL — the
> generators in pumice/scoria, and stream/rapids driving multi-outstanding
> traffic against slave test blocks that instantiate the exact receive RTL a
> real slave would use — not Python-BFM extensions to val harnesses. The BFM
> option below is declined. Basis for the close, per ISSUE-004 precedent, is
> this call; the supporting facts checked before recording it:
>
> - Post-ISSUE-004 `sdpram_slave_axi4_axi4` (BURST_Q_DEPTH=2) accepts AW n+1
>   while burst n is in flight, so the engine's `r_outstanding` counter IS
>   exercised — over the full 0..3 range (increment on AW, decrement on B,
>   threshold compare). What is not exercised is only the exact clamp at
>   MAX_OUTSTANDING=4, and 4 is margin above the deepest shipped slave (3),
>   per the engine's own comment ("bounded so the slave is not flooded").
> - The shipped Genesys2 RS pipeline (`rs_axi4_pipeline.sv`) wires
>   `rs_axi4_write_engine` to `sdpram_slave_axi4_axi4`, so the board loop
>   exercises the same 0..3 range in hardware.
> - If a future pipelined slave ever needs the clamp proven at depth, the
>   instrument is the RTL pipelined-slave variant from the options table
>   below — filed as its own issue then, against that slave.

> **UPDATE 2026-10-02:** the premise below is partially gone. ISSUE-004 was
> fixed after all (Sean's call): sdpram_core now queues two commands per
> direction and accepts AW n+1 while burst n is in flight, so a master's
> AWs-minus-Bs counter CAN exceed 1 against this slave -- up to
> BURST_Q_DEPTH + 1 = 3. Phase 4c of val/amba/test_sdpram_slave.py streams
> four bursts with commands offered ahead and passes. What is still true:
> `rs_axi4_write_engine` is built with MAX_OUTSTANDING = 4, deeper than the
> slave's 3, and no harness drives B-lagging-behind-AW pressure hard enough
> to prove the engine's gate at its full depth. The BFM option below remains
> the way to close that residual.

Every AXI4 master in this repo that carries outstanding-transaction depth is
verified against `sdpram_slave_axi4_axi4`, and that slave serialises bursts
(amba ISSUE-004, closed no-action). So the depth is never reached and the
logic that manages it is never exercised.

The deduction is from the handshake, not a sample:

```systemverilog
// sdpram_core.sv
assign fub_awready = !r_wr_active && !r_b_pending && !w_clearing;
```

B for burst N must be consumed before AW for burst N+1 is accepted, so an
AWs-minus-Bs counter in the master can only ever hold 0 or 1 against it.

Concretely, `rs_axi4_write_engine.sv`:

```systemverilog
logic [OSW-1:0] r_outstanding;   // AWs issued minus Bs received
assign m_axi_awvalid = r_running && (r_aw_left != '0)
                    && (r_outstanding < OSW'(MAX_OUTSTANDING));
```

is instantiated with `MAX_OUTSTANDING(4)` -- the only such instantiation in
the projects -- and that gate can never be what stops it. The engine is RIGHT
to carry the depth: it will meet pipelined slaves in a real system. But it is
untested logic in shipped IP, and the usual failure mode for an unexercised
counter is an off-by-one or a missed decrement that only shows under pressure
the test bench cannot apply.

## What this is NOT

Not a request to change `sdpram_core`. That was considered and declined in
ISSUE-004: it is a test memory, four harnesses depend on it, and the
throughput cost amortises away with burst length.

## Options

| | |
|---|---|
| a pipelining slave variant for DV only | a `sdpram_slave_axi4_axi4_pipe` (or a parameter) that accepts AW while a burst is active, used by TBs that want to stress outstanding. Keeps the simple core simple |
| drive the engines from a BFM instead | the AXI4 slave BFM can accept multiple outstanding AWs; a component-level test of the engines against the BFM would reach the depth without touching the harness memories |
| constrain the IP instead | if nothing in the roadmap needs depth > 1, reduce MAX_OUTSTANDING to 1 and delete the logic rather than ship untested capability |

The BFM route is probably cheapest and belongs in
`projects/components/ecc-ip/reed-solomon/dv/` rather than here -- the engines
are RS's, even though the gap was found from the amba side. Needs an owner's
call on which.
