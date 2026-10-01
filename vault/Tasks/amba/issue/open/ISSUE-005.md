# ISSUE-005: no harness exercises a master's multi-outstanding path

**Priority:** P2
**Status:** open
**Owner:** TBD

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
