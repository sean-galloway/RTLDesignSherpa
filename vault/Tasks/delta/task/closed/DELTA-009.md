# DELTA-009: systolic package — torus wrap, route lookahead, source-route, speculative VA+SA

**Status:** CLOSED 2026-10-15 (commit in the delta mesh Task 9 round-2 fix).  
**Priority:** P2  
**Filed from:** plan Task 9 (`docs/superpowers/plans/2026-10-14-delta-mesh-implementation.md`).

## What changed

- `projects/components/fabric-gen-ip/delta/bin/delta_mesh/cell.py`
  - Torus wrap links enabled in `fabric.py` and dateline rule implemented.
  - Source-route override (`--source-route`) bypasses the RAM table and walks
    `sr_ptr[3:0]`; `4'hF` terminates cleanly when the current cell matches the
    destination, otherwise the packet drops as an exhausted path.
  - Speculative VA+SA (`--speculation`) added: a VC1 head whose downstream
    credit is high is captured one cycle early, then committed or revoked on the
    next cycle based on the actual credit level.
- `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_systolic.py`
  created: ring-latency, dateline, source-route (positive + exhaustion), and
  speculation-parity scenarios.
- Regenerated `projects/components/fabric-gen-ip/delta/rtl/delta_mesh_cell.sv`
  and `delta_mesh_fabric_4x4x1.sv`.

## Root cause of the speculation parity failure

`test_delta_mesh_systolic_speculation[func]` lost flits because a committed
speculative grant released the output after only the head beat.  The bubble
flop was set on `spec_commit`, which made `gnt_ack` fire one cycle after the
head handshake.  The arbiter then handed the output off to the next waiting
requester before the rest of the packet had been sent.  On the downstream
link the original packet's body beats became separated from its head; the
downstream cell read the intervening packet's beats as if they were the body
of the first packet, producing truncated or missing frames.

The revoke path was correct (the captured head never left, so releasing the
arbiter early is safe), but a *commit* must hold the output until the packet's
TLAST exactly like a non-speculative grant.

## Fix

In `cell.py` the release bubble is now set only on `out_xfer_last` or
`spec_revoke`:

```systemverilog
bubble[q] <= out_xfer_last[q] || spec_revoke[q];
```

`spec_commit` no longer creates a bubble, so the speculative grant stays
registered through the body beats and is acknowledged only at TLAST.  This
preserves packet atomicity on every link while still allowing the head to be
granted one cycle early when the credit is high.

## Verification

- `pytest projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_systolic.py -k "speculation and (gate or func)"`  
  → 2/2 passed.
- `pytest projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_systolic.py -k "gate or func"`  
  → all systolic scenarios passed.
- Quick delta mesh gate subset (cell_routing, fabric_2x2, modes, multicast,
  qos, tables) → 20/20 passed.
- Offline generator tests (`projects/components/fabric-gen-ip/delta/bin/tests/`)
  → 120/120 passed.
- Regenerated RTL artifacts are byte-reproducible from `cell.py`.
