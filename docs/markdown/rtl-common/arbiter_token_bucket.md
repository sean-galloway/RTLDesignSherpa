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

# Token-Bucket Request Shaper

**Module:** `rtl/common/arbiter_token_bucket.sv`

## Overview

Per-client token-bucket request shaper. It sits in front of any arbiter in
the family and gates each client's request by its token balance: tokens
accumulate at a configured per-client rate on an external refill tick (up to
a burst cap), and one token is spent per completed grant. A client out of
tokens simply stops requesting until the next refill.

This is **rate shaping, not fairness** — the arbiter behind it still decides
who wins among the requests that pass; the shaper decides how *often* each
client may compete. That separation is why it is a free-standing block
rather than a mode of any one arbiter: it composes with
[arbiter_round_robin](arbiter_round_robin.md) for rate-limited fair sharing,
or with [arbiter_round_robin_weighted](arbiter_round_robin_weighted.md) /
[arbiter_deficit_round_robin](arbiter_deficit_round_robin.md) for shaped
rate *and* weighted share together.

```systemverilog
module arbiter_token_bucket #(
    parameter int CLIENTS      = 4,
    parameter int MAX_TOKENS   = 64,
    parameter int RATE_WIDTH   = 4,
    parameter int WAIT_GNT_ACK = 0
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              refill_tick,
    input  logic [CXRW-1:0]   rate,
    input  logic [CXTW-1:0]   bucket_cap,
    input  logic [C-1:0]      request_in,
    input  logic [C-1:0]      grant,
    input  logic              grant_valid,
    input  logic [C-1:0]      grant_ack,
    output logic [C-1:0]      request_out,
    output logic [CXTW-1:0]   tokens
);
```

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| CLIENTS | int | 4 | Number of clients being shaped |
| MAX_TOKENS | int | 64 | Exclusive bound on buckets/caps; field width = $clog2(MAX_TOKENS) |
| RATE_WIDTH | int | 4 | Width of each per-client tokens-per-tick rate field |
| WAIT_GNT_ACK | int | 0 | Completion contract of the DOWNSTREAM arbiter (must match it) |

## Functional Description

- **`refill_tick` is external.** Pair it with
  [counter_freq_invariant](counter_freq_invariant.md)'s microsecond tick so
  rates carry real-time meaning across clock frequencies, or with any pulse
  of your choosing.
- **cap = 0 means UNSHAPED, not blocked** (fail-open). A zeroed config must
  degrade to "no shaping", never to "no service". To block a client, gate
  its request upstream or zero its weight/quantum in the downstream arbiter.
  Corollary: real caps live in 1..MAX_TOKENS-1 — a cap value equal to
  MAX_TOKENS wraps the field to 0 and turns shaping OFF.
- **The cap clamp is an invariant, applied every cycle** — not only at
  refill. A runtime cap decrease bites immediately; banked burst above the
  new cap is forfeited (with rate 0 a refill-time-only clamp would never
  fire at all).
- **Overspend-proof gate.** The downstream grant registers one cycle after
  arbitration saw `request_out`, so in the completion cycle the bucket
  register still shows the pre-spend value. The pass gate subtracts the
  in-flight spend, so a one-token client cannot win twice on one token —
  the same registered-decision window the DRR's cost pipeline handles.
- **Burst semantics:** a bucket at cap C allows C back-to-back grants, then
  the client throttles to its refill rate. Reset starts every bucket empty
  (the conservative choice for a rate limiter).
- **No config-update FSM** — unlike the WRR/DRR there is no cross-client
  invariant to protect; rate/cap changes take effect per the clamp rules.

## Timing

| Property | Value |
|---|---|
| Gate | Combinational: request_in to request_out through one compare |
| Buckets | Registered; refill-then-clamp-then-spend per cycle |
| Sustained rate | Exactly rate[i] tokens per tick interval under saturation |

## Related Modules

- [arbiter_round_robin](arbiter_round_robin.md),
  [arbiter_round_robin_weighted](arbiter_round_robin_weighted.md),
  [arbiter_deficit_round_robin](arbiter_deficit_round_robin.md) — the
  arbiters this shaper feeds (welded to none of them)
- [counter_freq_invariant](counter_freq_invariant.md) — the natural
  refill_tick source

## Testing

**Location:** `val/common/test_arbiter_token_bucket.py`

The TB plays the downstream arbiter (registered grants, both ACK modes) and
keeps a never-overspend ledger asserted at every completion: cumulative
grants can never exceed cumulative banked refill. Scenarios: sustained rate
under saturation, burst allowance exactly the cap, cap-0 bypass, and a
runtime rate cut that drains then fully blocks.

```bash
pytest val/common/test_arbiter_token_bucket.py -v
```

## Navigation

- **[Index](index.md)** · **[Overview](overview.md)**
