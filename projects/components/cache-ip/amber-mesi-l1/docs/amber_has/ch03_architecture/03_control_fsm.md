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

# Control FSM: Blocking Pipeline and Pending-Fill Bypass

## The blocking pipeline

`amber_control` implements the cache's only state machine. It moves through a fixed sequence per request:

1. **Lookup** — read tag and state for the request's set on port A.
2. **Hit service** — read or write the data array and return the response.
3. **Miss resolution** — on a miss, ask `amber_repl` for a victim way.
4. **Victim drain** — if the victim is dirty, stage it in `amber_victim` and hand it to `amber_drain`.
5. **Fill request** — launch `amber_fill` for a whole-line burst.
6. **Fill completion** — write data and install tag + MESI state.
7. **Replay** — re-present the original request from the front-end latch; it now hits.

Because the pipeline is blocking, no new CPU request is accepted while a miss is in flight. That single-outstanding property is what makes the pending-fill bypass tractable.

## Pending-fill bypass register

While a fill is outstanding, a snoop may arrive for the same line. `amber_control` keeps one pending-fill register holding `{line_address, state_being_installed, data_available_mask}`. A snoop matching the pending line is answered from the register:

- `CRRESP` reflects the post-fill state (e.g., Shared for a read-shared fill, Exclusive for a read-unique fill, Invalid for a line that will be invalidated by the requester's MakeUnique).
- Required CD beats are forwarded from the fill stream as the beats arrive, so the response is bounded both for hits and for misses.

The correctness target is *state-accuracy*: a probe against a pending fill must observe exactly the post-fill state, never pre-fill. This is one of the SymbiYosys proof targets (D9).

## FSM oracle derivation

The control FSM's stable and transient states are derived from the gem5 Ruby `MESI_Two_Level` SLICC tables, specifically `L1cache.sm` (D9). The Python reference model and the formal oracles replay the same state transitions, so the protocol is cross-checked against an executable spec rather than prose. MOESI headroom is reserved in the encoding but the FSM v1.0 implements only M/E/S/I.
