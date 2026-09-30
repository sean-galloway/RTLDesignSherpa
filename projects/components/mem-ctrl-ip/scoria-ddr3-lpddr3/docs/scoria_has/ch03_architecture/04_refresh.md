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

# Refresh: DDR3 All-Bank and LPDDR3 Per-Bank

## What is inherited

pumice's `refresh_ctrl` already implements the parts that carry over unchanged:
the retention interval, all-bank refresh, and JEDEC's plus-or-minus-eight
postpone and pull-in scheduling. Its retention headroom is proven in formal
across all sixteen postpone values, and that proof transfers.

## What changes: LPDDR3 keeps per-bank refresh

JESD209-3C carries per-bank refresh (`REFpb`). This is the one refresh feature
DDR3 does *not* have — DDR3 adds no controller-directed per-bank refresh — so
`refresh_ctrl` becomes genuinely memtype-dependent in a way pumice's was for
LPDDR2 already.

| Memtype | Refresh available |
|---|---|
| DDR3 | all-bank `REF` only, with the JEDEC postpone window |
| LPDDR3 | all-bank `REF`, plus `REFpb` per-bank round-robin |

: Table 3.5: Refresh by memtype

Per-bank refresh matters because an all-bank refresh blocks every bank at once,
while `REFpb` refreshes one bank and leaves the others available. On a workload
with bank parallelism, that is the difference between a refresh being a stall and
being nearly free.

**Round-robin, not scheduled.** scoria TASK-001 already records the boundary
here, and this specification adopts it: `REFpb` round-robin is the only per-bank
scheme that is commodity-legal at this tier. The cleverer schemes — out-of-order
per-bank refresh, write-refresh parallelisation, refresh pausing, SARP and DSARP
— are LPDDR4/DDR5 or research, and they are assigned to the DDR4 controller,
not here.

## Requirements

1. Per memtype, offer all-bank refresh with the JEDEC postpone/pull-in window
   (inherited), and for LPDDR3 additionally `REFpb` in round-robin order.
2. The choice between all-bank and per-bank on LPDDR3 is a **runtime CSR**, not
   a build parameter, so both can be measured on one bitstream.
3. Retention must be satisfied in either mode. The inherited formal property —
   retention headroom across every postpone value — must be re-established for
   the per-bank path, because refreshing one bank per interval changes the
   arithmetic that property checks.
4. `REFpb` must respect per-bank timing as an ordinary bank occupant: a per-bank
   refresh is an operation on that bank and the bank timer owns it.

**Important:** requirement 3 is the one that will be tempting to skip. The
retention proof is the reason refresh can be trusted, and per-bank refresh
changes its arithmetic — the interval per bank is now the all-bank interval
times the bank count. Carrying the old property forward unchanged would prove
the wrong thing while appearing green.
