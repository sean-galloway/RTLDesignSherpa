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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Credit Logic

## MAS Decision: Memory Sizing and Advertisement

**MAS decision:** `IN_DEPTH = 32` lines and `OUT_DEPTH = 32` lines.

Rationale: A 32-line depth is a power of two, matches the default
credit-strap scale, and gives simple 5-bit pointers. The result memory
is intentionally deeper than the default `TILE_LAND_FLITS` strap (16
flits) so that the landing-space strap, not the result memory, is the
emit bottleneck. The input memory's flit capacity is the cell's boot
advertisement value.

With `LINE_W = 32` and a 64-bit payload flit today, one input line
occupies one payload flit (low 32 bits). Therefore the boot
advertisement is:

```text
advertisement flits = IN_DEPTH = 32 flits
```

**Note:** Slice 3 may pack two 32-bit lines per 64-bit payload flit; if
that packing is adopted, the advertisement value must be re-derived from
the new flit count (`IN_DEPTH / 2` flits) while the line count stays 32.
Until then, the advertisement is 32 flits.

## MAS Decision: Credit Batch Size and Timeout

**MAS decision:** Per-source credit batching uses `N = CREDIT_BATCH_N`
consumed lines per source, with a default of `N = 1`. A partial batch
that has not reached `N` drains after a 64-cycle timeout.

Rationale: `N = 1` gives the simplest exact-per-line behavior, which is
what the slice-2 credit-loop test will verify. Making `N` configurable
lets later builds trade return latency for lower credit-packet traffic.
The 64-cycle timeout bounds the latency of a trailing partial batch
without adding any traffic at `N = 1`.

## Per-Source Owed Counters

`cell_credit` maintains a bank of owed counters indexed by the recorded
source coordinate. Each counter has:

- `owed[src]`: number of consumed lines not yet returned to this source
- `timer[src]`: cycles since the last return to this source (valid when
  `owed` is non-zero and below the batch threshold)

On every consumed-line strobe from `cell_exec_fsm`:

1. `owed[src] += 1`
2. If `owed[src] >= CREDIT_BATCH_N`, send one `credit`/`add` packet for
   `CREDIT_BATCH_N` flits, decrement `owed[src]` by `CREDIT_BATCH_N`,
   and clear the timer.
3. Otherwise, load the timer with the timeout value (or reset it if it
   was already running).

Every cycle, for each source with `0 < owed[src] < CREDIT_BATCH_N`:

- If `timer[src] == 0`, send one `credit`/`add` packet for `owed[src]`
  flits and clear `owed[src]`.
- Else, `timer[src] -= 1`.

The timeout value is 64 cycles. The timer is loaded only when a new
partial batch begins; additional consumed lines in the same partial
batch do not reset the timer (they will be included in the same return
when it fires).

## Credit Packet Format

A consumed-line credit return is a header-only `credit` packet with:

- `ptype = credit` (3)
- `op = 0` (`add`)
- `length =` number of flits returned (`CREDIT_BATCH_N` or the residual
  `owed` count)
- `destination =` the recorded source coordinate of the consumed line
- `source =` this cell's external ID
- `tag =` echoed or zero (the sink does not store credit packets)
- `target_address[1:0] = credit_class = 0` (sink space)

Credit packets ride the credit VC and need no grant (TILE_SPEC §11.9).
TILE_SPEC §11.5 encodes the credit class in the low two bits of the
target address: `0` = sink-space credit, `1` = descriptor-slot credit.
Consumed-line returns and the boot advertisement below are sink-space
credits (class 0).

## Boot Advertisement Packet

After reset, `cell_credit` sends one `credit`/`set` packet to
`level = 3` (the tile I/O / RAPIDS) carrying the input memory's full
size in flits:

- `op = 1` (`set`)
- `length = IN_DEPTH` flits (32 today)
- `destination = {ext=0, level=3, X/Y/Z = tile I/O}`
- `source =` this cell's external ID
- `target_address[1:0] = credit_class = 0` (sink space)

This advertisement is the cell's "alive" signal; RAPIDS's external
sink-space counter for this cell starts at 0 and is filled by this
packet (TILE_SPEC §11.10).

## Sender-Generic Returns

The return is sender-generic: a credit goes to the source coordinate
recorded on the input-memory line, not to a hard-coded RAPIDS ID. A
cell that streamed into this cell's input memory therefore receives the
credits, not RAPIDS, exactly as TILE_SPEC §11.9 requires.

## Implementation Note: Counter Bank Sizing

The number of legal source coordinates in a tile is bounded by the
credit-counter index table in TILE_SPEC §11.9. A cell therefore needs
at most enough per-source owed counters to cover every possible source
that may send to it. A practical implementation allocates one counter
per external ID (RAPIDS + peer cells + tetrad cores) that the tile can
address, lazily allocating on first strobe if area must be minimized.

---

**Last Updated:** 2026-10-19
